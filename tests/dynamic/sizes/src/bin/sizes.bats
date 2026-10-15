#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* proved_hash and sha1_digest run the proved code in pieces of 4096 bytes
   copied from the caller's array (sha256#29, stage E); hash is the fast
   SHA-256. This prints the SHA-256 (hash and proved_hash) and the SHA-1
   (sha1_digest) of the first n bytes of the pattern
   "abcdefghijklmnopqrstuvwxyz" repeated, for n on both sides of the piece
   (4095, 4096, 4097, 8191, 8192, 8193), of the one-shot proved functions'
   limit (65535, 65536, 65537); and update given the first k
   bytes of an array of n (k under n, k = 0). The harness compares the
   output with `expected` (Python's hashlib). *)
fn hex_digit (d: int): int = let
  val e = g1ofg0(d)
in if e >= 0 then (if e < 10 then 48 + e else if e < 16 then 87 + e else 63) else 63 end

fun pr {l:agz}{m:nat}{i:nat | i <= m} .<m - i>. (o: !$A.arr(byte, l, m), m: int m, i: int i): void =
  if i >= m then ()
  else let
    val b = byte2int0($A.get<byte>(o, i))
    val high = b / 16
    val low = b - 16 * high
    val () = print_char(int2char0(hex_digit(high)))
    val () = print_char(int2char0(hex_digit(low)))
  in pr(o, m, i + 1) end

fun fill {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(97 + nmod(i, 26)))
  in fill(d, n, i + 1) end

(* the 64 characters finish wrote *)
fun pr_text {l:agz}{i:nat | i <= 64} .<64 - i>. (o: !$A.arr(byte, l, 64), i: int i): void =
  if i >= 64 then ()
  else let val () = print_char(int2char0(byte2int0($A.get<byte>(o, i)))) in pr_text(o, i + 1) end

fn run {n:pos | n <= 1048576} (n: int n): void = let
  val d = $A.alloc<byte>(n)
  val () = fill(d, n, 0)
  val o = $A.alloc<byte>(64)
  val () = $SHA.hash(d, n, o)
  val () = print!("sha256 ", n, " ")
  val () = pr_text(o, 0)
  val () = print_newline()
  val () = $SHA.proved_hash(d, n, o)
  val () = print!("proved-sha256 ", n, " ")
  val () = pr_text(o, 0)
  val () = print_newline()
  val () = $A.free<byte>(o)
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val s = $A.alloc<byte>(20)
  val () = $SHA.sha1_digest(borrowed, n, s)
  val () = print!("sha1 ", n, " ")
  val () = pr(s, 20, 0)
  val () = print_newline()
  val () = $A.free<byte>(s)
  val () = $A.drop<byte>(frozen, borrowed)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in end

(* update given k of the n bytes of the array *)
fn run_prefix {n:pos | n <= 1048576}{k:nat | k <= n} (n: int n, k: int k): void = let
  val d = $A.alloc<byte>(n)
  val () = fill(d, n, 0)
  val c = $SHA.init()
  val () = $SHA.update(c, d, k)
  val o = $A.alloc<byte>(64)
  val () = $SHA.finish(c, o)
  val () = print!("prefix ", k, " of ", n, " ")
  val () = pr_text(o, 0)
  val () = print_newline()
  val c2 = $SHA.proved_init()
  val () = $SHA.proved_update(c2, d, k)
  val () = $SHA.proved_finish(c2, o)
  val () = print!("proved-prefix ", k, " of ", n, " ")
  val () = pr_text(o, 0)
  val () = print_newline()
  val () = $A.free<byte>(o)
  val () = $A.free<byte>(d)
in end

implement main0 () = let
  val () = run(4095)
  val () = run(4096)
  val () = run(4097)
  val () = run(8191)
  val () = run(8192)
  val () = run(8193)
  val () = run(65535)
  val () = run(65536)
  val () = run(65537)
  val () = run_prefix(5000, 0)
  val () = run_prefix(5000, 4100)
  val () = run_prefix(5000, 5000)
in end
