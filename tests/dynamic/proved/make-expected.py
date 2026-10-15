# The expected output of proved.bats, from hashlib; the NIST vectors are
# checked against the digests FIPS 180-4's examples (and the NIST CAVP
# short-message vectors) give.
import hashlib

def sha256(b): return hashlib.sha256(b).hexdigest()
def sha1(b): return hashlib.sha1(b).hexdigest()

# the published digests the vectors must have (NIST SHA-256 and SHA-1 examples)
KNOWN256 = {
    b"abc": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq": "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
    b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu": "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
    b"a" * 1000000: "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0",
    b"": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
}
KNOWN1 = {
    b"abc": "a9993e364706816aba3e25717850c26c9cd0d89d",
    b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq": "84983e441c3bd26ebaae4aa1f95129e5e54670f1",
    b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu": "a49b2446a02c645bf419f995b67091253a04a259",
    b"a" * 1000000: "34aa973cd4c4daa4f61eeb2bdbad27316534016f",
    b"": "da39a3ee5e6b4b0d3255bfef95601890afd80709",
}
for m, h in KNOWN256.items(): assert sha256(m) == h
for m, h in KNOWN1.items(): assert sha1(m) == h

def pattern(n): return bytes(97 + i % 26 for i in range(n))

def pseudo(n, x):
    out = bytearray()
    for _ in range(n):
        out.append(x % 256)
        x = (75 * x + 74) % 65537
    return bytes(out)

d = pattern(201)
for k in range(201):
    print("sha256", k, sha256(d[:k]))
print("sha256 prefixes 0 to 200, fast and proved differ 0 times")

r = pseudo(5001, 12345)
y = 777
for _ in range(40):
    y = (75 * (y % 65537) + 74) % 65537
    length = 201 + y % 4800
    assert length <= 5001
    print("random", length, sha256(r[:length]))
print("sha256 random lengths, fast and proved differ 0 times")

print("sha1 empty", sha1(b""))
for k in range(1, 201):
    print("sha1", k, sha1(d[:k]))

def whole(name, m):
    print(name, len(m), "fast", sha256(m))
    print(name, len(m), "proved", sha256(m))
    print(name, len(m), sha1(m))

whole("abc", b"abc")
whole("nist-448", b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
whole("nist-896", b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")
whole("million-a", b"a" * 1000000)
whole("mebibyte-pattern", pattern(1048576))
whole("mebibyte-pseudo", pseudo(1048576, 4242))
print("whole messages, fast and proved differ 0 times")
