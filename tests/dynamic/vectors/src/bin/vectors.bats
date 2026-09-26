#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Prints the hash of each vector; the harness compares the output with
   `expected` (from Python's hashlib). Lengths 3, 55, 56 and 64 cover
   one and two padding blocks; 1000 covers many blocks. *)
fun pr {l:agz}{i:nat | i <= 64} .<64 - i>. (o: !$A.arr(byte, l, 64), i: int i): void =
  if i >= 64 then ()
  else let val () = print_char(int2char0(byte2int0($A.get<byte>(o, i)))) in pr(o, i + 1) end

(* data[i] = the i-th byte of the repeating pattern "abcdefghij..." of
   period p (1 <= p <= 26) *)
fun fill {l:agz}{n:pos}{p:int | 1 <= p; p <= 26}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, p: int p, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(97 + nmod(i, p)))
  in fill(d, n, p, i + 1) end

fn run {n:pos | n <= 1048576}{p:int | 1 <= p; p <= 26}
  (name: string, n: int n, p: int p): void = let
  val d = $A.alloc<byte>(n)
  val () = fill(d, n, p, 0)
  val o = $A.alloc<byte>(64)
  val () = $SHA.hash(d, n, o)
  val () = print!(name, " ")
  val () = pr(o, 0)
  val () = print_newline()
  val () = $A.free<byte>(o)
  val () = $A.free<byte>(d)
in end

implement main0 () = let
  val () = run("abc", 3, 3)
  val () = run("a55", 55, 1)
  val () = run("a56", 56, 1)
  val () = run("az64", 64, 26)
  val () = run("aj1000", 1000, 10)
in end
