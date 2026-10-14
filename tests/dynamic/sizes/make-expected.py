import hashlib
def msg(n): return bytes(97 + i % 26 for i in range(n))
for n in [4095,4096,4097,8191,8192,8193,65535,65536,65537]:
    print("sha256", n, hashlib.sha256(msg(n)).hexdigest())
    print("sha1", n, hashlib.sha1(msg(n)).hexdigest())
for k in [0,4100,5000]:
    print("prefix", k, "of", 5000, hashlib.sha256(msg(k)).hexdigest())
