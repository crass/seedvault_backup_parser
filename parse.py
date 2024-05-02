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
import argparse
import json
import getpass
import glob
import shutil
import string
import struct
import hashlib

try:
    # If pybip39 is available use it to add additional verification
    import pybip39
except:
    pybip39 = None

# debian does not ship pycryptodome under the pycrypto namespace. Try both.
# See Issue #8
try:
    from Crypto.Cipher import AES
    AES.MODE_GCM
except:
    try:
        from Cryptodome.Cipher import AES
        AES.MODE_GCM
    except:
        print("ERROR: Please install pycryptodome.")
        exit(-1)

from base64 import urlsafe_b64decode, urlsafe_b64encode


#
class SeedVaultBackupBase(object):
    # separator can't be in urlsafe b64 alphabet. -> no A-Za-Z0-9-_ -> choose .
    B64_SEPARATOR = "."

    METADATA_FILE = ".backup.metadata"

    def __init__(self):
        raise RuntimeError("Abstract Base Class")

    # parses file-path, where file is a base64 encoded key into the decoded filenam
    @classmethod
    def filepath_to_key(cls, filepath):
        filename = filepath.split("/")[-1]

        # seedvault removes padding =, add them back, else python complains
        return urlsafe_b64decode(filename + "=" * ((4 - len(filename) % 4) % 4))


class SeedVaultBackup(SeedVaultBackupBase):

    def __init__(self, password=None):
        self.password=password

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
                with open(f"{targetfolder}/full/{appname}", "wb") as f:
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
            appid = full.split("/")[-1]
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


    # generate the key from a user-input mnemonic phrase
    # uses the same algorithms as seedvault, see
    # https://github.com/NovaCrypto/BIP39/blob/master/src/main/java/io/github/novacrypto/bip39/SeedCalculator.java
    # https://github.com/NovaCrypto/BIP39/blob/master/src/main/java/io/github/novacrypto/bip39/JavaxPBKDF2WithHmacSHA512.java
    def get_key(self, mnemonic=None):
        salt = b"mnemonic"
        rounds = 2048
        keysize = 256

        if mnemonic is None:
            mnemonic = self.password

        if mnemonic is None:
            vis = input("Should mnemonic be visible while typing? [y/n]: ")
            if vis.lower().startswith("y"):
                 mnemonic = input("Please enter mnemonic: ").encode()
            else:
                mnemonic = getpass.getpass("Please enter mnemonic: ").encode()

        if pybip39:
            pybip39.Mnemonic.validate(mnemonic.decode('ascii'))

        key = hashlib.pbkdf2_hmac("sha512", mnemonic, salt, rounds)
        return key[:keysize//8]


def main():
    parser = argparse.ArgumentParser(
        description='Work with SeedVault backups')
    subparsers = parser.add_subparsers(help='sub-command help')
    parser.add_argument('-p', '--password', default=None, help='backup password')

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
    if args.password:
        args.password = bytes(args.password, 'ascii')

    svb = SeedVaultBackup(password=args.password)

    if args.action == "show":
        print(f"Parsing backup {args.backupfolder}")
        kv_parsed = svb.parse_backup(args.backupfolder, args.targetfolder)

    elif args.action == "decrypt":
        print(f"Decrypting backup from {args.backupfolder} into {args.targetfolder}")
        kv_parsed = svb.parse_backup(args.backupfolder, args.targetfolder)

    elif args.action == "encrypt":
        print(f"Encrypting backup from {args.plainfolder} into {args.targetfolder}")
        kv_parsed = svb.encrypt_backup(args.plainfolder, args.targetfolder)


if __name__ == "__main__":
    main()
