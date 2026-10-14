#!/usr/bin/env python3
"""Writes this test's `expected` and the constants its reference uses.

The expected output is made by an independent SHA-256 and SHA-1 written
here in Python integers from the standard's formulas (FIPS 180-4), which
hash the vectors to hashlib's digests (checked below) and whose first rounds
of "abc" are the published traces (FIPS 180-2 appendix B.1 and A.1); the
round constants are computed from their definitions with integer cube and
square roots, not copied.

usage: make-test.py <expected-file> <reference-constants-file>"""
import hashlib, math, sys

M = 0xffffffff
def rotr(x, n): return ((x >> n) | (x << (32 - n))) & M
def rotl(x, n): return ((x << n) | (x >> (32 - n))) & M

def primes(n):
    ps = []; c = 2
    while len(ps) < n:
        if all(c % p for p in ps): ps.append(c)
        c += 1
    return ps

def icbrt(n):
    lo, hi = 0, 1 << 40
    while lo < hi:
        m = (lo + hi + 1) // 2
        if m ** 3 <= n: lo = m
        else: hi = m - 1
    return lo

# the first 32 bits of the fractional part of the cube root of the first 64 primes
K256 = [icbrt(p << 96) & M for p in primes(64)]
# the first 30 bits of the square roots of 2, 3, 5, 10 (times 2 to the 30)
K1 = [math.isqrt(n << 60) for n in (2, 3, 5, 10)]
H256 = [math.isqrt(p << 64) & M for p in primes(8)]   # square roots, section 5.3.3
H1 = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
assert K256[0] == 0x428a2f98 and K256[63] == 0xc67178f2 and H256[0] == 0x6a09e667

def message(vector):
    if vector == 0: return b"abc"
    if vector == 1: return bytes(97 + i // 4 + i % 4 for i in range(56))
    return bytes((i * 7 + 3) % 256 for i in range(64))

def padded(m):
    n = len(m)
    m = m + b"\x80"
    while len(m) % 64 != 56: m += b"\x00"
    return m + (8 * n).to_bytes(8, "big")

def schedule256(block):
    w = [int.from_bytes(block[4*i:4*i+4], "big") for i in range(16)]
    for t in range(16, 64):
        s1 = rotr(w[t-2], 17) ^ rotr(w[t-2], 19) ^ (w[t-2] >> 10)
        s0 = rotr(w[t-15], 7) ^ rotr(w[t-15], 18) ^ (w[t-15] >> 3)
        w.append((s1 + w[t-7] + s0 + w[t-16]) & M)
    return w

def block256(h, block, trace):
    w = schedule256(block)
    a, b, c, d, e, f, g, hh = h
    for t in range(64):
        t1 = (hh + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & M & g)) + K256[t] + w[t]) & M
        t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) & M
        hh, g, f, e, d, c, b, a = g, f, e, (d + t1) & M, c, b, a, (t1 + t2) & M
        trace.append((a, b, c, d, e, f, g, hh))
    return [(x + y) & M for x, y in zip(h, (a, b, c, d, e, f, g, hh))]

def block1(h, block, trace):
    w = [int.from_bytes(block[4*i:4*i+4], "big") for i in range(16)]
    for t in range(16, 80):
        w.append(rotl(w[t-3] ^ w[t-8] ^ w[t-14] ^ w[t-16], 1))
    a, b, c, d, e = h
    for t in range(80):
        if t < 20: f = (b & c) | (~b & M & d)
        elif t < 40: f = b ^ c ^ d
        elif t < 60: f = (b & c) | (b & d) | (c & d)
        else: f = b ^ c ^ d
        a, b, c, d, e = (rotl(a, 5) + f + e + K1[t // 20] + w[t]) & M, a, rotl(b, 30), c, d
        trace.append((a, b, c, d, e))
    return [(x + y) & M for x, y in zip(h, (a, b, c, d, e))]

def words(ws): return " ".join(f"{x:08x}" for x in ws)

out = []
out += [f"sha256 K{i} {k:08x}" for i, k in enumerate(K256)]
out += [f"sha1 K{i} {K1[i // 20]:08x}" for i in range(80)]
names = ["abc", "448-bit message", "64 bytes"]
for vector in range(3):
    pad = padded(message(vector))
    for kind, h0, block, digest in (("sha256", H256, block256, hashlib.sha256), ("sha1", H1, block1, hashlib.sha1)):
        h = list(h0)
        for b in range(len(pad) // 64):
            trace = []
            h = block(h, pad[64*b:64*b+64], trace)
            if vector < 2:
                for t, state in enumerate(trace):
                    out.append(f"{names[vector]} block {b} {kind} t={t:02d} {words(state)}")
        assert b"".join(x.to_bytes(4, "big") for x in h) == digest(message(vector)).digest()
        out.append(f"{names[vector]} {kind} digest {words(h)} differing=0")
# the published first rounds of "abc" (FIPS 180-2 appendix B.1 and SHA-1's A.1)
assert "abc block 0 sha256 t=00 5d6aebcd 6a09e667 bb67ae85 3c6ef372 fa2a4622 510e527f 9b05688c 1f83d9ab" in out
assert "abc block 0 sha1 t=00 0116fc33 67452301 7bf36ae2 98badcfe 10325476" in out
assert "abc block 0 sha1 t=79 42541b35 5738d5e1 21834873 681e6df6 d8fdf6ad" in out
open(sys.argv[1], "w").write("\n".join(out) + "\n")
with open(sys.argv[2], "w") as f:
    f.write("sha256_k " + " ".join(f"{k:08x}" for k in K256) + "\n")
    f.write("sha256_h " + " ".join(f"{k:08x}" for k in H256) + "\n")
