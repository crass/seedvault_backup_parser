#!/usr/bin/env python3

#   Copyright 2020 Thomas Lambertz
#   Copyright 2024 Glenn Washburn
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.


import re
import os
import sys
import io
import itertools
import argparse
import codecs
import json
import getpass
import glob
import shutil
import string
import struct
import hashlib
import gzip
import datetime
import logging

logging.basicConfig(format='%(message)s', stream=sys.stdout, level=logging.WARNING)
logger = logging.getLogger(__name__)

from base64 import urlsafe_b64decode, urlsafe_b64encode

try:
    import apsw
    import apsw.bestpractice
    apsw.bestpractice.apply(apsw.bestpractice.recommended)
    USE_APSW = True
except Exception as e:
    if sys.version_info.major < 3 or sys.version_info.minor < 11:
        logger.warning(f"Error unable to initialize apsw: {e}")

        logger.warning(f"  May not be able to print out KV data from sqlite db, though it will still be decrypted")
    USE_APSW = False

try:
    # If pybip39 is available use it to add additional verification
    import pybip39
except:
    logger.warning(f"pybip39 module not found: Disabling extra mnemonic validation")
    pybip39 = None

# debian does not ship pycryptodome under the pycrypto namespace. Try both.
# See Issue #8
try:
    from Crypto.Hash import SHA256
    from Crypto.Cipher import AES
    AES.MODE_GCM
except:
    try:
        from Cryptodome.Hash import SHA256
        from Cryptodome.Cipher import AES
        AES.MODE_GCM
    except:
        logger.error("ERROR: Please install pycryptodome.")
        exit(-1)


# This is what SeedVault V1 backups are using under it all
try:
    import tink
    from tink import streaming_aead
    streaming_aead.register()
except tink.TinkError as e:
    logger.error(f"Error initialising Tink: {e}")
    exit(1)


try:
    # TODO: Perhaps have BackupSnapshot protobuf defined in this file
    from proto.backup_snapshot_pb2 import BackupSnapshot
    DECRYPT_SNAPSHOTS = True
except Exception as e:
    logger.warning(f"Unable to decrypt snapshots: {e}")
    DECRYPT_SNAPSHOTS = False


class JSONBytesEncoder(json.JSONEncoder):
    """Only to be used for display, decoding will give undesirable results"""
    def default(self, o):
        if type(o) == bytes:
            try:
                return o.decode('utf8')
            except:
                return repr(o)
        return super().default(o)


# Stolen from pycryptodome.Protocol.KDF.HKDF()
# See: https://github.com/Legrandin/pycryptodome/blob/master/lib/Crypto/Protocol/KDF.py#L281
# Allow expansion only mode when onlyexpand evals to True.
# TODO: Send a PR to pycryptodome adding the onlyexpand modification
from Crypto.Hash import HMAC
def HKDF(master, key_len, salt, hashmod, num_keys=1, context=None, onlyexpand=False):
    output_len = key_len * num_keys
    if output_len > (255 * hashmod.digest_size):
        raise ValueError("Too much secret data to derive")
    if not salt:
        salt = b'\x00' * hashmod.digest_size
    if context is None:
        context = b""

    # Step 1: extract
    if not onlyexpand:
        hmac = HMAC.new(salt, master, digestmod=hashmod)
        prk = hmac.digest()
    else:
        prk = master

    # Step 2: expand
    t = [ b"" ]
    n = 1
    tlen = 0
    while tlen < output_len:
        hmac = HMAC.new(prk, t[-1] + context + struct.pack('B', n), digestmod=hashmod)
        t.append(hmac.digest())
        tlen += hashmod.digest_size
        n += 1
    derived_output = b"".join(t)
    if num_keys == 1:
        return derived_output[:key_len]
    kol = [derived_output[idx:idx + key_len]
           for idx in iter_range(0, output_len, key_len)]
    return list(kol[:num_keys])


def tink_key_protos_from_keyset_proto(keyset_proto: tink.proto.tink_pb2.Keyset):
    """
        Given a KeySet protocol buffer return the class for the Key protocol buffer
    """
    import importlib

    key_pb_classes = []
    for key_pb in keyset_proto.key:
        key_name = keyset_proto.key[0].key_data.type_url.split('.')[-1]
        key_name_snake = key_name.translate(dict([(ord(c), '_'+c.lower()) for c in string.ascii_uppercase]))
        module_name = key_name_snake[1:key_name_snake.rfind('_')] + '_pb2'
        key_pb_mod = importlib.import_module('tink.proto.' + module_name)
        key_pb_classes.append(getattr(key_pb_mod, key_name))
    return key_pb_classes


from tink import _keyset_handle
def tink_import_key(keyset_handle: _keyset_handle.KeysetHandle, *keys: bytes):
    """
        Return a KeysetHandle of the same type as keyset_handle filled
        key material.
    """
    from tink import _insecure_keyset_handle
    from tink import secret_key_access

    # Get the protobuf
    keyset_proto = _insecure_keyset_handle.to_proto_keyset(keyset_handle, secret_key_access.TOKEN)
    assert len(keyset_proto.key) == len(keys)

    for key, key_pb, key_proto_class in zip(keys, keyset_proto.key, tink_key_protos_from_keyset_proto(keyset_proto)):
        key_proto = key_proto_class()
        key_proto.ParseFromString(key_pb.key_data.value)
        key_proto.key_value = key
        if getattr(tink_import_key, '_key_proto_log', 0) == 0:
            logger.debug(f"key_proto = {key_proto}")
            tink_import_key._key_proto_log = 1
        key_pb.key_data.value = key_proto.SerializeToString()

    keyset_handle = _insecure_keyset_handle.from_proto_keyset(keyset_proto, secret_key_access.TOKEN)
    return keyset_handle


#
class SeedVaultBackupBase(object):
    METADATA_FILE = ".backup.metadata"

    def __init__(self):
        raise RuntimeError("Abstract Base Class")

    @classmethod
    def get_version(cls, backupfolder):
        meta_path = os.path.join(backupfolder, cls.METADATA_FILE)
        if not os.path.exists(meta_path):
            raise RuntimeError(f"Not a SeedVault backup: {backupfolder}")

        with open(meta_path, "rb") as f:
            try:
                return json.load(f)["@meta@"]["version"]
            except:
                f.seek(0)
                return ord(f.read(1))

    # parses file-path, where file is a base64 encoded key into the decoded filenam
    @classmethod
    def filepath_to_key(cls, filepath):
        filename = filepath.split("/")[-1]

        # seedvault removes padding =, add them back, else python complains
        return urlsafe_b64decode(filename + "=" * ((4 - len(filename) % 4) % 4))

    def get_password(self, mnemonic=None):
        if mnemonic is None:
            mnemonic = self.password

        if mnemonic is None:
            vis = input("Should mnemonic be visible while typing? [y/n]: ")
            if vis.lower().startswith("y"):
                mnemonic = input("Please enter mnemonic: ")
            else:
                mnemonic = getpass.getpass("Please enter mnemonic: ")

        if pybip39:
            pybip39.Mnemonic.validate(mnemonic)

        return mnemonic.encode()


class SeedVaultBackupBaseV0(SeedVaultBackupBase):
    # separator can't be in urlsafe b64 alphabet. -> no A-Za-Z0-9-_ -> choose .
    B64_SEPARATOR = "."

    # generate the key from a user-input mnemonic phrase
    # uses the same algorithms as seedvault, see
    # https://github.com/NovaCrypto/BIP39/blob/master/src/main/java/io/github/novacrypto/bip39/SeedCalculator.java
    # https://github.com/NovaCrypto/BIP39/blob/master/src/main/java/io/github/novacrypto/bip39/JavaxPBKDF2WithHmacSHA512.java
    def get_key(self, mnemonic=None):
        salt = b"mnemonic"
        rounds = 2048
        keysize = 256

        key = hashlib.pbkdf2_hmac("sha512", self.get_password(mnemonic), salt, rounds)
        return key[:keysize//8]


class SeedVaultBackupBaseV1(SeedVaultBackupBase):
    ALGORITHM_HMAC = "HmacSHA256"
    KEY_SIZE = 256
    KEY_SIZE_BYTES = KEY_SIZE / 8
    SIZE_SEGMENT = 1 << 20
    INFO_STREAM_KEY = b"stream key"
    APPDATA_STREAM_KEY = b"app data key"

    TYPE_METADATA = 0x00
    TYPE_BACKUP_KV = 0x01
    TYPE_BACKUP_FULL = 0x02
    TYPE_CHUNK = 0x00
    TYPE_SNAPSHOT = 0x01

    def get_key(self, mnemonic=None, context=APPDATA_STREAM_KEY):
        salt = b"mnemonic"
        # See: https://github.com/seedvault-app/seedvault/blob/android14/app/src/main/java/com/stevesoltys/seedvault/crypto/Crypto.kt#L125
        rounds = 2048
        keysize = 256

        # See: https://github.com/Electric-Coin-Company/kotlin-bip39/blob/main/bip39-lib/src/commonMain/kotlin/cash/z/ecc/android/bip39/Mnemonics.kt#L309
        seed = hashlib.pbkdf2_hmac("sha512", self.get_password(mnemonic), salt, rounds)

        # The seed is comprised first the backup key, then the main key
        # See: https://github.com/seedvault-app/seedvault/blob/android14/app/src/main/java/com/stevesoltys/seedvault/crypto/KeyManager.kt#L76
        mainkey = seed[keysize//8:]

        # Only do an HKDF expansion
        # See: https://github.com/seedvault-app/seedvault/blob/android14/storage/lib/src/main/java/org/calyxos/backup/storage/crypto/StreamCrypto.kt#L31
        # Where the expansion is defined here:
        # https://github.com/seedvault-app/seedvault/blob/android14/storage/lib/src/main/java/org/calyxos/backup/storage/crypto/Hkdf.kt
        key = HKDF(mainkey, keysize//8, None, SHA256, context=context, onlyexpand=True)

        logger.debug(f"seed = {codecs.encode(seed, 'hex')} ({len(codecs.encode(seed, 'hex'))})")
        logger.debug(f"key = {codecs.encode(key[:keysize//8], 'hex')} ({len(codecs.encode(key, 'hex'))})")
        return key[:keysize//8]

    def get_stream_key(self):
        return self.get_key(context=self.INFO_STREAM_KEY)

    def getAD(self, version, ctype, bytestr = b''):
        # getAD: get AD (associated data)
        # See: app/src/main/java/com/stevesoltys/seedvault/metadata/Metadata.kt#L11
        # NOTE: Java is big-endian
        adbuf = struct.pack(">BB", version, ctype) + bytestr
        return adbuf


    def getChunkAD(self, version, chunkid):
        # getAD: get AD (associated data) for chunks
        # See: storage/lib/src/main/java/org/calyxos/backup/storage/crypto/StreamCrypto.kt#L43
        # NOTE: Java is big-endian
        assert len(codecs.decode(chunkid, 'hex')) == self.KEY_SIZE_BYTES, len(codecs.decode(chunkid, 'hex'))
        return struct.pack(">BB", version, self.TYPE_CHUNK) + codecs.decode(chunkid, 'hex')


    def getSnapshotAD(self, version, timestamp):
        # getAD: get AD (associated data) for snapshots
        # See: storage/lib/src/main/java/org/calyxos/backup/storage/crypto/StreamCrypto.kt#L43
        # NOTE: Java is big-endian
        return struct.pack(">BBQ", version, self.TYPE_SNAPSHOT, timestamp)


    def get_cipher(self, input_file, key, adbuf):
        # 1. Get a handle to the key material
        keyset_handle = tink.new_keyset_handle(
            streaming_aead.streaming_aead_key_templates.AES256_GCM_HKDF_1MB)
        keyset_handle = tink_import_key(keyset_handle, key)

        # 2. Get the primitive.
        streaming_aead_primitive = keyset_handle.primitive(streaming_aead.StreamingAead)

        # 3. Return stream decryptor.
        return streaming_aead_primitive.new_decrypting_stream(input_file, adbuf)


#############################################################
##### Decryptors
#############################################################
class SeedVaultBackupDecryptorV0(SeedVaultBackupBaseV0):

    def __init__(self, backupdir, targetdir=None, password=None):
        self.backupdir = backupdir
        self.targetdir = targetdir
        self.password = password


    def decrypt(self):
        return self.parse_backup(self.backupdir, self.targetdir)


    # parses key-value pairs stored in the "kv" subfolder
    # see KVBackup.kt
    def parse_kv_backup(self, backupfolder, targetfolder, userkey):
        kvs = sorted(glob.glob(f"{backupfolder}/kv/*"))
        #print("Found kv folders: ")
        #for kv in kvs:
        #    print("  "+"/".join(kv.split("/")[2:]))

        print("Decrypting Key-Value files: ")
        kv_parsed = {}
        for kv in kvs:
            appname = kv.split("/")[-1]
            print("  for app "+appname)
            pairsb64 = glob.glob(kv+"/*")

            if targetfolder:
                os.makedirs(f"{targetfolder}/kv/{appname}", exist_ok=True)

            # verbose: dump all found paths
            if not targetfolder:
                for p in sorted([self.filepath_to_key(p) for p in pairsb64]):
                    print(f"    {p.decode()}")

            pairs = {}
            for p in pairsb64:
                with open(p, "rb") as f:
                    ct = f.read()

                key = self.filepath_to_key(p)
                b64 = urlsafe_b64encode(key)
                version = ct[0]
                ct = ct[1:]
                assert version == 0 # only version 0 supported

                versionheader_bytes, ct = self.decrypt_segment(ct, userkey)
                versionheader = self.parse_versionheader(versionheader_bytes)

                # if decrypted versionheader does not match folder/filename, something has gone wrong
                #print(versionheader, appname, self.filepath_to_key(p))
                assert versionheader['name'].decode() == appname
                assert versionheader['key'] == key
                assert versionheader['version'] == version

                # parse all remaining segments
                data = self.decrypt_segments(ct, userkey)

                if targetfolder:
                    # we need to save as b64, since some keys contain "/" etc
                    whitelist = string.ascii_letters + string.digits + '.'
                    cleanname = re.sub(f'[^{whitelist}]', '', key.decode())
                    with open(f"{targetfolder}/kv/{appname}/{cleanname}{self.B64_SEPARATOR}{b64.decode()}", "wb") as f:
                        f.write(data)

                pairs[key] = data
                #print(key, data, b64)

            kv_parsed[appname] = pairs

        return kv_parsed


    # just prints all apk names found
    def parse_apk_backup(self, backupfolder, targetfolder=None):
        apks = sorted(glob.glob(f"{backupfolder}/*.apk"))
        if targetfolder is None:
            print("Found apks:")
            for apk in apks:
                print("  "+"/".join(apk.split("/")[1:]))
        else:
            print("Copying apk files")
            for apk in apks:
                shutil.copy2(apk, targetfolder)


    # parses the full app backups, stored in the "full" subfolder
    # see FullBackup.kt::performFullBackup()
    def parse_full_app_backups(self, backupfolder, targetfolder, userkey):
        if targetfolder:
            os.makedirs(f"{targetfolder}/full", exist_ok=True)
        fulls = sorted(glob.glob(f"{backupfolder}/full/*"))
        print("Decrypting full backup for apps: ")
        for full in fulls:
            appname = full.split("/")[-1]
            print("  "+appname)

            with open(full, "rb") as f:
                ct = f.read()

            #key = self.filepath_to_key(p)
            #b64 = urlsafe_b64encode(key)
            version = ct[0]
            ct = ct[1:]
            assert version == 0 # only version 0 supported

            versionheader_bytes, ct = self.decrypt_segment(ct, userkey)
            versionheader = self.parse_versionheader(versionheader_bytes, False)

            # if decrypted versionheader does not match folder/filename, something has gone wrong
            #print(versionheader, appname, self.filepath_to_key(p))
            assert versionheader['name'].decode() == appname
            assert versionheader['version'] == version

            # parse all remaining segments
            data = self.decrypt_segments(ct, userkey)
            if targetfolder:
                with open(f"{targetfolder}/full/{appname}.tar", "wb") as f:
                    f.write(data)
            else:
                print("   Value: ", data)
                print("\n\n\n")


    def parse_metadata(self, backupfolder, targetfolder, key):
        with open(f"{backupfolder}/{self.METADATA_FILE}", "rb") as f:
            ct = f.read()

        version = ct[0]
        assert version == 0
        pt = self.decrypt_segments(ct[1:], key)

        if targetfolder:
            with open(f"{targetfolder}/{self.METADATA_FILE}", "wb") as f:
                f.write(pt)
        else:
            print("Metadata:")
            print(pt)


    # Version Header is:
    # 1 Byte  - Version
    # 2 Bytes - Packagename length x
    # x Bytes - Packagename
    # 2 Bytes - Keyname length y
    # y Bytes - Keyname
    #
    # see HeaderWriter.kt
    def parse_versionheader(self, vb, include_key=True):
        version = vb[0]
        namelen = struct.unpack(">H", vb[1:3])[0]
        name = vb[3:3+namelen]
        key = None
        if include_key:
          keylen = struct.unpack(">H", vb[3+namelen:3+namelen+2])[0]
          assert len(vb) == namelen + keylen + 2 + 2 + 1
          key = vb[3+2+namelen:]
        return {
            "version": version,
            "name": name,
            "key": key,
        }


    # parses everything
    def parse_backup(self, backupfolder, targetfolder, key=None):
        if key is None:
            key = self.get_key()

        if targetfolder:
            os.makedirs(targetfolder, exist_ok=True)

        self.parse_metadata(backupfolder, targetfolder, key)
        self.parse_apk_backup(backupfolder, targetfolder)

        kv_parsed = self.parse_kv_backup(backupfolder, targetfolder, key)
        if targetfolder == None:
            self.print_kv_pairs(kv_parsed)

        print("\n\n")

        # only decrypt apps into a folder, never print, since they might be huge
        if targetfolder:
            self.parse_full_app_backups(backupfolder, targetfolder, key)
        else:
            print("Skipping full app backup decryption, since they might be too large to show. Use the DECRYPT option")

        return kv_parsed


    # "pretty" prints all found key-value pairs
    def print_kv_pairs(self, kv):
        for app, pairs in kv.items():
            print("------------------------------------------------------\n")
            for key, value in pairs.items():
                print(f"APP: {app}\t\tKEY: {key.decode()}")
                print(value)
                print()


    # takes a single segment, decrypts it. Returns trailing data (other segments)
    # segment consists of
    # 2  Bytes - Segment length x
    # 12 Bytes - IV used for encryption
    # x  Bytes - Encrypted Data (of which last 16 bytes are aes-gcm-tag)
    def decrypt_segment(self, ct, key):
        # parse segment header to get iv and segment length
        length = struct.unpack(">h", ct[:2])[0]
        assert len(ct[2:]) >= length
        remainder = ct[2+12+length:]
        iv = ct[2:2+12]
        ct = ct[2+12:2+12+length]

        # use iv from segment header to decrypt
        pt = self.aes_decrypt(ct, key, iv)

        #print(length, iv, ct)
        return pt, remainder


    # decrypt multiple consecutive segments
    def decrypt_segments(self, ct, key):
        data = b""
        while ct:
            pt, ct = self.decrypt_segment(ct, key)
            data += pt
        return data


    # decrypt a ciphertext with aesgcm and verify its tag. Last 16 bytes of ct are tag
    def aes_decrypt(self, ct, key, iv):
        TAG_LEN = 128//8
        cipher = AES.new(key, AES.MODE_GCM, nonce=iv)
        tag = ct[-TAG_LEN:]
        try:
            pt = cipher.decrypt_and_verify(ct[:-TAG_LEN], tag)
        except ValueError as e:
            print(e)
            print("Could not decrypt data! Is your key correct?")
            sys.exit(-1)
        return pt


class SeedVaultBackupDecryptorV1(SeedVaultBackupBaseV1):

    def __init__(self, backupdir, targetdir=None, password=None):
        self.backupdir = backupdir
        self.targetdir = targetdir
        self.password = password


    def decrypt(self):
        return self.parse_backup(self.backupdir, self.targetdir)


    # See: app/src/main/java/com/stevesoltys/seedvault/crypto/Crypto.kt#L115
    def parse_metadata(self, backupfolder, targetfolder, key):
        f = open(f"{backupfolder}/{self.METADATA_FILE}", "rb")
        version = ord(f.read(1))
        assert version == 1, version

        output_file = io.BytesIO()
        adbuf = self.getAD(version, self.TYPE_METADATA) + \
            struct.pack(">Q", int(os.path.basename(backupfolder.rstrip(os.sep))))
        scipher = self.get_cipher(f, key, adbuf)

        with scipher as dec_stream:
            bytes_read = dec_stream.read()
            output_file.write(bytes_read)
        metadata = json.loads(output_file.getvalue())
        assert version == metadata["@meta@"]["version"]

        if targetfolder:
            logger.info(f"metadata json = {json.dumps(metadata, indent=2)}")
            with open(f"{targetfolder}/{self.METADATA_FILE}", "wb") as f:
                f.write(output_file.getvalue())
        else:
            logger.info(f"Metadata:\n{json.dumps(metadata, indent=2)}")

        return metadata


    def parse_settings_dict(self, bytestr, lensz=4):
        """Parse particular KV settings of the format:
            {len}{key string}{len}{value string}...{null}
            See: https://cs.android.com/android/platform/superproject/main/+/main:frameworks/base/packages/SettingsProvider/src/com/android/providers/settings/SettingsBackupAgent.java;drc=edc28c0a73d18e18583252daaada966bfae4cba5;l=1041
        """
        if lensz == 4:
            fmt = ">I"
        elif lensz == 2:
            fmt = ">H"
        else:
            raise RuntimeError(f"Unallowed length size: {lensz}")
        settings = {}
        while bytestr:
            l = struct.unpack(fmt, bytestr[:lensz])[0]
            if l == 0:
                break
            key = bytestr[lensz:lensz+l].decode('utf8')
            bytestr = bytestr[lensz+l:]
            l = struct.unpack(fmt, bytestr[:lensz])[0]
            value = bytestr[lensz:lensz+l]
            if key == 'nfc_payment_default_component':
                logger.debug(f"{value[0]!r} {value!r}")
            if value and value[0] == 0:
                value = self.parse_settings_dict(value, lensz)
            else:
                value = value.decode('utf8')
            settings[key] = value
            bytestr = bytestr[lensz+l:]

        return settings


    def get_kv_dict(self, sqlite_bytes, sqlite_path=None):
        if sys.version_info.major >= 3 and sys.version_info.minor >= 11:
            import sqlite3
            c = sqlite3.connect(":memory:")
            c.deserialize(sqlite_bytes)
        elif USE_APSW:
            c = apsw.Connection(":memory:")
            c.deserialize('main', sqlite_bytes)
        elif self.targetdir:
            import sqlite3
            c = sqlite3.connect(sqlite_path)
        else:
            return
        return dict([r for r in c.execute("select * from kv_entry")])


    def parse_apk_data_backup(self, pkg_name, pkg_metadata, key, salt):
        if 'backupType' not in pkg_metadata:
            logger.warning(f"    Skipping parsing apk data: No backupType in metadata: {pkg_metadata}")
            return

        h = hashlib.sha256((salt + pkg_name).encode()).digest()
        pkg_path = os.path.join(self.backupdir.encode(), urlsafe_b64encode(h).rstrip(b'='))

        if not os.path.exists(pkg_path):
            if not pkg_metadata.get('system', False):
                logger.warning(f"    Skipping, pkg path not exist: {pkg_path}: {pkg_metadata}")
            return

        logger.debug(f"    Decrypting app backup file: {os.path.basename(pkg_path).decode()}")

        # Decrypt package data
        with open(pkg_path, 'rb') as f:
            version = ord(f.read(1))
            assert version == 1, version

            btype = None
            if pkg_metadata["backupType"] == "KV":
                btype = self.TYPE_BACKUP_KV
                bext = '.sqlite'
            if pkg_metadata["backupType"] == "FULL":
                btype = self.TYPE_BACKUP_FULL
                bext = '.tar'

            logger.info(f"    Parsing {pkg_metadata['backupType']} backup as {bext[1:]} file")

            output_file = io.BytesIO()
            adbuf = self.getAD(version, btype, pkg_name.encode())
            scipher = self.get_cipher(f, key, adbuf)

            with scipher as dec_stream:
                try:
                    bytes_read = dec_stream.read()
                except Exception as e:
                    logger.error(f"    Error: Failure to decrypt {os.path.basename(pkg_path).decode()}: {e}")
                    return
                output_file.write(bytes_read)

            output_file.seek(0)
            if btype == self.TYPE_BACKUP_KV:
                output_file = gzip.GzipFile(fileobj=output_file)

            output_path = None
            if self.targetdir:
                output_path = os.path.join(self.targetdir, pkg_name + bext)
                with open(output_path, 'wb') as f:
                    f.write(output_file.read())

            if btype == self.TYPE_BACKUP_KV and logger.getEffectiveLevel() <= logging.DEBUG:
                output_file.seek(0)
                kv = self.get_kv_dict(output_file.read(), output_path)
                if kv:
                    if pkg_name == 'com.android.providers.settings':
                        # See: https://cs.android.com/android/platform/superproject/main/+/main:frameworks/base/packages/SettingsProvider/src/com/android/providers/settings/SettingsBackupAgent.java
                        # This should show how to decode all these settings
                        kv['lock_settings'] =  self.parse_settings_dict(kv['lock_settings'], 2)
                        dict_cfgs = ('secure', 'global', 'system')
                        for cfg in dict_cfgs:
                            kv[cfg] = self.parse_settings_dict(kv[cfg])
                    logger.debug(f"    kv: {json.dumps(kv, indent=6, cls=JSONBytesEncoder)}")
            if btype == self.TYPE_BACKUP_FULL:
                import tarfile
                output_file.seek(0)
                assert tarfile.is_tarfile(output_file)
                if logger.getEffectiveLevel() <= logging.DEBUG:
                    tf = tarfile.open(fileobj=output_file)
                    for info in tf:
                        import time
                        mtime = "%d-%02d-%02d %02d:%02d:%02d" \
                            % time.localtime(info.mtime)[:6]
                        logger.debug(f'      {info.size:10d} {mtime} {info.name + ("/" if info.isdir() else "")}')


    def copy_apk_files(self, pkg_name, pkg_metadata, salt):
        for splitname, sha256val in [('', pkg_metadata.get('sha256', None))] + [(s['name'], s['sha256']) for s in pkg_metadata.get('splits', [])]:
            h = hashlib.sha256((salt + "APK" + pkg_name + splitname).encode()).digest()
            apk_path = os.path.join(self.backupdir.encode(), urlsafe_b64encode(h).rstrip(b'='))

            if not os.path.exists(apk_path) or pkg_metadata.get('system', False):
                logger.warning(f"    Skipping, apk path not exist: {apk_path}")
                if not pkg_metadata.get('system', False):
                    logger.debug(f"      {pkg_metadata}")
                return

            # APKs are not encrypted
            with open(apk_path, 'rb') as f:
                # Verify that the hash checks out
                h = urlsafe_b64encode(hashlib.sha256(f.read()).digest())
                if sha256val is None or h.decode('ascii').rstrip('=') == sha256val:
#                    print(f"APK {pkg_name} passed hash check")
                    if splitname:
                        filename = pkg_name + '.' + splitname + ".apk"
                    else:
                        filename = pkg_name + ".apk"
                    if self.targetdir:
                        shutil.copy2(apk_path, os.path.join(self.targetdir, filename))
                    logger.info(f"    APK file {filename} validated and copied")
                else:
                    logger.warn(f"    APK failed hash check: {apk_path}")


    def parse_apk_backup(self, pkg_name, pkg_metadata, key, salt):
        # TODO: Verify signatures

        logger.info('='*60)
        print(f"  {pkg_name}")

        self.parse_apk_data_backup(pkg_name, pkg_metadata, key, salt)
        self.copy_apk_files(pkg_name, pkg_metadata, salt)


    def parse_chunk(self, snapdir, chunkid, key=None, zipindex=-1):
        chunk_path = os.path.join(snapdir, chunkid[:2], chunkid)
        assert os.path.exists(chunk_path), chunk_path

        if key is None:
            key = self.get_stream_key()

        output_file = io.BytesIO()
        with open(chunk_path, 'rb') as f:
            version = ord(f.read(1))
            #assert version == 1, version

            adbuf = self.getChunkAD(version, chunkid)
            scipher = self.get_cipher(f, key, adbuf)
            with scipher as dec_stream:
                bytes_read = dec_stream.read()
                output_file.write(bytes_read)

            if zipindex > 0:
                import zipfile
                output_file.seek(0)
                assert zipfile.is_zipfile(output_file), output_file.getvalue()[:100]
                output_file.seek(0)
                zf = zipfile.ZipFile(output_file)
                chunk = zf.read(str(zipindex))
            else:
                chunk = output_file.getvalue()

        return chunk


    def parse_snapshot(self, snapdir, timestamp):
        snap_path = os.path.join(self.backupdir, snapdir, str(timestamp) + '.SeedSnap')
        ts_str = datetime.datetime.fromtimestamp(timestamp//1000).isoformat()
        snap_name = f"{ts_str}.{str(timestamp)}"
        print(f"  Parsing snapshot {os.path.join(snapdir, str(timestamp))} {ts_str}")
        key = self.get_stream_key()

        with open(snap_path, 'rb') as f:
            version = ord(f.read(1))
#            assert version == 1, version

            adbuf = self.getSnapshotAD(version, timestamp)
            scipher = self.get_cipher(f, key, adbuf)

            output_file = io.BytesIO()
            with scipher as dec_stream:
                bytes_read = dec_stream.read()
                output_file.write(bytes_read)

        bsnap = BackupSnapshot()
        bsnap.ParseFromString(output_file.getvalue())
        logger.debug(f"  BackupSnapshot: num media files = {len(bsnap.media_files)}, num document files = {len(bsnap.document_files)}\n{bsnap}")

        from google.protobuf import json_format
        if self.targetdir:
            snapmeta_path = os.path.join(self.targetdir, f"{snap_name}.SeedSnap")
            with open(snapmeta_path, 'wb') as f:
                f.write(json_format.MessageToJson(bsnap).encode())
            logger.info(f"  Wrote snapshot metadata to {snapmeta_path}")

        print("  Extracting snapshot files")
        # See: splitSnapshot in storage/lib/src/main/java/org/calyxos/backup/storage/restore/FileSplitter.kt
        for mfile in itertools.chain(bsnap.media_files, bsnap.document_files):
            print(f"    {os.path.join(mfile.path, mfile.name)}")
            if self.targetdir:
                dir_path = os.path.join(self.targetdir, snap_name, mfile.path)
                os.makedirs(dir_path, exist_ok=True)
                file_path = os.path.join(dir_path, mfile.name)

                if not os.path.exists(file_path) or mfile.size != os.path.getsize(file_path):
                    with open(file_path, 'wb') as f:
                        for chunkid in mfile.chunk_ids:
                            f.write(self.parse_chunk(snapdir, chunkid, key=key, zipindex=mfile.zip_index))

                os.utime(file_path, times=(mfile.last_modified//1000, mfile.last_modified//1000))
                assert mfile.size == os.path.getsize(file_path), mfile.size


    def find_snapshots(self, backupfolder=None):
        dir_re = re.compile(r"^[a-f0-9]{16}\.sv$")
        snapshot_re = re.compile(r"([0-9]{13})\.SeedSnap")

        if backupfolder is None:
            backupfolder = self.backupdir
        root = os.path.dirname(backupfolder)
        print(f"Looking for snapshots in {root}")
        for dirname in os.listdir(root):
            dirpath = os.path.join(root, dirname)
            if not os.path.isdir(dirpath):
                continue
            logger.debug(f"  Checking {dirname} for snapshots")
            if dir_re.match(dirname):
                logger.info(f"  Looking for snapshots in {dirname}")
                for name in os.listdir(dirpath):
                    m = snapshot_re.match(name)
                    if m:
                        timestamp = int(m.group(1))
                        print(f"  Found snapshot with timestamp: {timestamp}")
                        yield (dirpath, timestamp)


    def parse_snapshots(self, backupfolder=None):
        if backupfolder is None:
            backupfolder = self.backupdir

        for snapdir, timestamp in self.find_snapshots(backupfolder):
            self.parse_snapshot(snapdir, timestamp)


    # parses everything
    def parse_backup(self, backupfolder, targetfolder, key=None):
        if key is None:
            key = self.get_key()

        if targetfolder:
            os.makedirs(targetfolder, exist_ok=True)

        print(f"Parsing APK and backup metadata")
        metadata = self.parse_metadata(backupfolder, targetfolder, key)

        print(f"Parsing APK and backup data")

        # Extract APKs and backup data
        salt = metadata['@meta@']['salt']
        for pkg_name, pkg_metadata in metadata.items():
            if pkg_name in ("@meta@", "@end@"): # @pm@ ???
                continue

            self.parse_apk_backup(pkg_name, pkg_metadata, key, salt)

        # Extract snapshots
        global DECRYPT_SNAPSHOTS
        if DECRYPT_SNAPSHOTS:
            logger.info('='*60)
            self.parse_snapshots()


def SeedVaultBackupDecryptor(*args, **kwargs):
    version = SeedVaultBackupBase.get_version(args[0])
    if version == 0:
        klass = SeedVaultBackupDecryptorV0
    elif version == 1:
        klass = SeedVaultBackupDecryptorV1
    else:
        raise RuntimeError(f"Unsupported version: {version}")
    return klass(*args, **kwargs)


#############################################################
##### Encryptors
#############################################################
class SeedVaultBackupEncryptorV0(SeedVaultBackupBaseV0):
    def __init__(self, plaindir, targetdir=None, password=None):
        self.plaindir = plaindir
        self.targetdir = targetdir
        self.password = password


    def encrypt(self):
        return self.encrypt_backup(self.plaindir, self.targetdir)


    # encrypt a ciphertext with aesgcm. Last 16 bytes of ct are tag
    def aes_encrypt(self, pt, key, iv):
        TAG_LEN = 128//8
        cipher = AES.new(key, AES.MODE_GCM, nonce=iv)
        ct, tag = cipher.encrypt_and_digest(pt)
        return ct + tag


    # encrypts a segment, creates random iv and correct header
    def encrypt_segment(self, pt, key):
        # create segment header
        # length of cipher text and following tag (16 bytes) must fit into 15 bits
        # because the android code reads it as a signed short.
        assert len(pt) + 16 < 2**15, f"Encryption block must be less than {(2**15)-16}, was {len(pt)}"
        header = struct.pack(">h", len(pt) + 16)
        iv = os.urandom(12) # random IV
        header += iv

        ct = self.aes_encrypt(pt, key, iv)

        return header + ct

    # encrypt multiple consecutive segments
    # blocksize defaults to maximum segment data size. Segment length is 2 bytes,
    # but read as a signed short, so 15bits, and subtract the 16 byte auth tag.
    def encrypt_segments(self, pt, key, blocksize=(2**15)-(16+1)):
        ct = b""
        for i in range(0, len(pt), blocksize):
            ct += self.encrypt_segment(pt[i:i+blocksize], key)
        return ct


    def create_versionheader(self, appname, key=None):
        data = b"\0" # version
        assert len(appname) < 255
        data += struct.pack(">H", len(appname))
        data += appname.encode()
        data += struct.pack(">H", len(key or ""))
        if key:
            data += key
        return data


    # reencrypts key-value pairs from a decrypted backup, so they can be flashed to the device
    def encrypt_backup(self, plainfolder, targetfolder, userkey=None):
        assert targetfolder

        if userkey is None:
            userkey = self.get_key()

        with open(f"{plainfolder}/{self.METADATA_FILE}") as f:
          metadata = json.load(f)
        token = metadata["@meta@"]["token"]
        targetfolder += '/' + str(token)

        os.makedirs(f"{targetfolder}/kv", exist_ok=True)
        kvs = sorted(glob.glob(f"{plainfolder}/kv/*"))

        print("Encrypting Key-Value files: ")
        for kv in kvs:
            appname = kv.split("/")[-1]
            print("  for app "+appname, kv)
            pairsb64 = glob.glob(kv+"/*")
            os.makedirs(f"{targetfolder}/kv/{appname}", exist_ok=True)

            for p in pairsb64:
                with open(p, "rb") as f:
                    pt = f.read()

                # file has to have an B64_SEPARATOR followed by the base64 of the key!
                keyb64 = p.split(self.B64_SEPARATOR)[-1]
                print(keyb64)
                key = urlsafe_b64decode(keyb64)
                print("    ", key)

                ct = b""
                # version is 0
                ct += b"\0"

                versionheader_bytes = self.create_versionheader(appname, key)
                ct += self.encrypt_segment(versionheader_bytes, userkey)
                # encrypt the plaintext
                ct += self.encrypt_segments(pt, userkey)

                with open(f"{targetfolder}/kv/{appname}/{keyb64.replace('=', '')}", "wb") as f:
                    f.write(ct)

        os.makedirs(f"{targetfolder}/full", exist_ok=True)
        fulls = sorted(glob.glob(f"{plainfolder}/full/*"))

        print("Encrypting Full backup files: ")
        for full in fulls:
            appid = full[:-4] if full.endswith('.tar') else full
            appid = appid.split("/")[-1]
            print("  for app "+appid, full)

            with open(f"{targetfolder}/full/{appid}", "wb") as wf:
                with open(full, "rb") as f:
                    pt = f.read()

                ct = b""
                # version is 0
                ct += b"\0"

                versionheader_bytes = self.create_versionheader(appid)
                ct += self.encrypt_segment(versionheader_bytes, userkey)
                # encrypt the plaintext
                ct += self.encrypt_segments(pt, userkey)

                wf.write(ct)

        print("Copying apk files")
        apks = sorted(glob.glob(f"{plainfolder}/*.apk"))
        for apk in apks:
            shutil.copy2(apk, targetfolder)

        print("Encrypting Metadata file")
        with open(f"{plainfolder}/{self.METADATA_FILE}", "rb") as f:
            meta = f.read()

        metac = b"\0" + self.encrypt_segment(meta, userkey)
        with open(f"{targetfolder}/{self.METADATA_FILE}", "wb") as f:
            f.write(metac)

        print("Done.")


class SeedVaultBackupEncryptorV1(SeedVaultBackupBaseV1):
    def __init__(self, plaindir, targetdir=None, password=None):
        self.plaindir = plaindir
        self.targetdir = targetdir
        self.password = password


    def encrypt(self):
        return self.encrypt_backup(self.plaindir, self.targetdir)


    def encrypt_backup(self, plainfolder, targetfolder, userkey=None):
        raise NotImplementedError


def SeedVaultBackupEncryptor(*args, **kwargs):
    version = SeedVaultBackupBase.get_version(args[0])
    if version == 0:
        klass = SeedVaultBackupEncryptorV0
    elif version == 1:
        klass = SeedVaultBackupEncryptorV1
    else:
        raise RuntimeError(f"Unsupported version: {version}")
    return klass(*args, **kwargs)


#############################################################

def main():
    parser = argparse.ArgumentParser(
        description='Work with SeedVault backups')
    subparsers = parser.add_subparsers(help='sub-command help')
    parser.add_argument('-p', '--password', default=None, help='backup password')
    parser.add_argument('-v', default=0, action='count', help='increase verbosity')

    show_sparser = subparsers.add_parser('show')
    show_sparser.add_argument('backupfolder', type=str, help='path to SeedVault backup')
    show_sparser.set_defaults(targetfolder=None)
    show_sparser.set_defaults(action="show")

    decrypt_sparser = subparsers.add_parser('decrypt')
    decrypt_sparser.add_argument('backupfolder', help='path to SeedVault backup')
    decrypt_sparser.add_argument('targetfolder', help='path to put decrypted SeedVault backup')
    decrypt_sparser.set_defaults(action="decrypt")

    encrypt_sparser = subparsers.add_parser('encrypt')
    encrypt_sparser.add_argument('plainfolder', help='path to decrypted SeedVault backup')
    encrypt_sparser.add_argument('targetfolder', help='path to put re-encrypted SeedVault backup')
    encrypt_sparser.set_defaults(action="encrypt")

    args = parser.parse_args()

    if args.v > 1:
        logger.setLevel(logging.DEBUG)
    elif args.v > 0:
        logger.setLevel(logging.INFO)

    if args.action == "show":
        logger.info(f"Parsing backup {args.backupfolder}")
        kv_parsed = SeedVaultBackupDecryptor(args.backupfolder, password=args.password).decrypt()

    elif args.action == "decrypt":
        logger.info(f"Decrypting backup from {args.backupfolder} into {args.targetfolder}")
        kv_parsed = SeedVaultBackupDecryptor(args.backupfolder, args.targetfolder, password=args.password).decrypt()

    elif args.action == "encrypt":
        logger.info(f"Encrypting backup from {args.plainfolder} into {args.targetfolder}")
        kv_parsed = SeedVaultBackupEncryptor(args.plainfolder, args.targetfolder, password=args.password).encrypt()


if __name__ == "__main__":
    main()
