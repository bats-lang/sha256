#!/usr/bin/env python3
"""Writes `expected` (sha256#78, keyword: nth-prime): the 64 round constants K_t
as the cube-root definition gives them (FIPS 180-4 4.2.2: the first 32 bits of
the fractional part of the cube root of the (t+1)-th prime, floor(cbrt(p) * 2^32)
= icbrt(p * 2^96)), each followed by `same` when the lookup of the proof of the
primes (sha256_k_nth_w32) and the published one (sha256_k_w32) give the same
word, and H(0) (5.3.3) the same way. The primes are found by trial division here,
not copied."""


def icbrt(n):
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def isqrt(n):
    lo, hi = 0, 1
    while hi * hi <= n:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid * mid <= n:
            lo = mid
        else:
            hi = mid
    return lo


primes = []
n = 2
while len(primes) < 64:
    if all(n % q for q in primes if q * q <= n):
        primes.append(n)
    n += 1

for t, p in enumerate(primes):
    print("k %d %08x same" % (t, icbrt(p << 96) & 0xffffffff))
print("iv " + "".join("%08x " % (isqrt(p << 64) & 0xffffffff) for p in primes[:8]) + "same")
