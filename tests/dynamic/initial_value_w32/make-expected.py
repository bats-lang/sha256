#!/usr/bin/env python3
"""Writes `expected`: SHA-256's H(0) from the definition (FIPS 180-4 5.3.3:
the first 32 bits of the fractional parts of the square roots of the first
eight primes; floor(sqrt(p) * 2^32) = isqrt(p * 2^64)), and SHA-1's (5.3.1)."""
from math import isqrt
primes = [2, 3, 5, 7, 11, 13, 17, 19]
words = [isqrt(p << 64) & 0xffffffff for p in primes]
print("sha256 " + "".join("%08x " % w for w in words))
print("sha1 " + "".join("%08x " % w for w in (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0)))
