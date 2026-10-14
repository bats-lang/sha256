#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Prints the SHA-1 of each vector as 40 lowercase hex digits; the harness
   compares the output with `expected` (from Python's hashlib). Lengths 1,
   3, 55, 56, 63, 64, 65, 119 and 120 sit on both sides of the padding's
   one-block and two-block edges; 1000 and 100000 cover many blocks.
   Known answers only: the proof is owed. *)
fn hex_digit {d:nat | d < 16} (d: int d): int =
  if d < 10 then 48 + d else 87 + d

fun pr {l:agz}{i:nat | i <= 20} .<20 - i>. (o: !$A.arr(byte, l, 20), i: int i): void =
  if i >= 20 then ()
  else let
    val b = byte2int0($A.get<byte>(o, i))
    val high = nmod(b / 16, 16)
    val low = nmod(b, 16)
    val () = print_char(int2char0(hex_digit(high)))
    val () = print_char(int2char0(hex_digit(low)))
  in pr(o, i + 1) end

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
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val o = $A.alloc<byte>(20)
  val () = $SHA.sha1_digest(borrowed, n, o)
  val () = print!(name, " ")
  val () = pr(o, 0)
  val () = print_newline()
  val () = $A.free<byte>(o)
  val () = $A.drop<byte>(frozen, borrowed)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in end

implement main0 () = let
  val () = run("a1", 1, 1)
  val () = run("abc", 3, 3)
  val () = run("a55", 55, 1)
  val () = run("a56", 56, 1)
  val () = run("a63", 63, 1)
  val () = run("a64", 64, 1)
  val () = run("a65", 65, 1)
  val () = run("az64", 64, 26)
  val () = run("a119", 119, 1)
  val () = run("a120", 120, 1)
  val () = run("aj1000", 1000, 10)
  val () = run("az100000", 100000, 26)
  val () = run("a1000000", 1000000, 1)
in end
