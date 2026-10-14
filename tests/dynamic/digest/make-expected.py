#!/usr/bin/env python3
"""Writes `expected` from hashlib: the digests main prints, for the same
messages (see src/bin/digest.bats), and asserts the published ones
(FIPS 180-2 appendix B, the empty message) first."""
import hashlib

def message(mode, p, total):
    if mode == 0:
        return bytes(97 + (i % p) for i in range(total))
    return bytes(97 + (i // 4) % 20 + (i % 4) for i in range(total))

def sha(m):
    return hashlib.sha256(m).hexdigest()

assert sha(b"") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
assert sha(b"abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
b2 = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
assert message(1, 0, 56) == b2
assert sha(b2) == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

cases = [
    ("empty", 0, 26, 0), ("abc", 0, 26, 3), ("b2", 1, 0, 56), ("a55", 0, 26, 55),
    ("a56", 0, 26, 56), ("a63", 0, 26, 63), ("a64", 0, 26, 64), ("a65", 0, 26, 65),
    ("a119", 0, 26, 119), ("a120", 0, 26, 120), ("a128", 0, 26, 128), ("aj1000", 0, 10, 1000),
    ("abc/1", 0, 26, 3), ("b2/1", 1, 0, 56), ("a56/7", 0, 26, 56), ("a64/64", 0, 26, 64),
    ("a65/64", 0, 26, 65), ("a120/13", 0, 26, 120), ("aj1000/7", 0, 10, 1000),
    ("aj1000/64", 0, 10, 1000), ("aj1000/1", 0, 10, 1000),
]
cases.append(("aj10000/4097", 0, 10, 10000))
for name, mode, p, total in cases:
    print(name, sha(message(mode, p, total)))

once = [("empty", 0, 26, 0), ("abc", 0, 26, 3), ("b2", 1, 0, 56), ("a55", 0, 26, 55),
        ("a56", 0, 26, 56), ("a63", 0, 26, 63), ("a64", 0, 26, 64), ("a65", 0, 26, 65),
        ("a119", 0, 26, 119), ("a120", 0, 26, 120), ("a128", 0, 26, 128), ("aj1000", 0, 10, 1000),
        ("aj10000", 0, 10, 10000)]
for name, mode, p, total in once:
    print(name, sha(message(mode, p, total)))

# FIPS 180-1 appendix A and B, the empty message
assert hashlib.sha1(b"abc").hexdigest() == "a9993e364706816aba3e25717850c26c9cd0d89d"
assert hashlib.sha1(b2).hexdigest() == "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
assert hashlib.sha1(b"").hexdigest() == "da39a3ee5e6b4b0d3255bfef95601890afd80709"
for name, mode, p, total in once:
    print("sha1", name, hashlib.sha1(message(mode, p, total)).hexdigest())
