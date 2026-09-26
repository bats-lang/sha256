#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Prints the hash of each vector; the harness compares the output with
   `expected` (from Python's hashlib). Lengths 3, 55, 56 and 64 cover
   one and two padding blocks; 1000 covers many blocks. The incremental
   API hashes aj1000 in 7-byte pieces and 2000000 bytes, more than an
   array holds, in 1000-byte pieces. *)
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

(* The same pattern fed to update in pieces of c bytes, t times: the
   pieces continue the pattern since c is a multiple of p. *)
fun feed {l:agz}{c:pos | c <= 1048576}{t:nat} .<t>.
  (x: !$SHA.ctx, d: !$A.arr(byte, l, c), c: int c, t: int t): void =
  if t <= 0 then ()
  else let val () = $SHA.update(x, d, c) in feed(x, d, c, t - 1) end

fn run_pieces {c:pos | c <= 1048576}{t:nat}{p:int | 1 <= p; p <= 26}
  (name: string, c: int c, t: int t, p: int p): void = let
  val d = $A.alloc<byte>(c)
  val () = fill(d, c, p, 0)
  val x = $SHA.init()
  val () = feed(x, d, c, t)
  val o = $A.alloc<byte>(64)
  val () = $SHA.finish(x, o)
  val () = print!(name, " ")
  val () = pr(o, 0)
  val () = print_newline()
  val () = $A.free<byte>(o)
  val () = $A.free<byte>(d)
in end

(* aj1000 in pieces of 7 bytes: a fed piece crosses block boundaries;
   the last piece is a prefix of a whole one *)
fun feed7 {l:agz}{i:nat | i <= 1000} .<1000 - i>.
  (x: !$SHA.ctx, d: !$A.arr(byte, l, 7), i: int i): void =
  if i >= 1000 then ()
  else let
    fun put {j:nat | j <= 7} .<7 - j>. (d: !$A.arr(byte, l, 7), j: int j): void =
      if j >= 7 then ()
      else let val () = $A.set<byte>(d, j, $A.int2byte(97 + nmod(i + j, 10))) in put(d, j + 1) end
    val () = put(d, 0)
    val k = (if 1000 - i < 7 then 1000 - i else 7): [k:pos | k <= 7; i + k <= 1000] int k
    val () = $SHA.update(x, d, k)
  in feed7(x, d, i + k) end

fn run_sevens (): void = let
  val d = $A.alloc<byte>(7)
  val x = $SHA.init()
  val () = feed7(x, d, 0)
  val o = $A.alloc<byte>(64)
  val () = $SHA.finish(x, o)
  val () = print!("aj1000/7 ")
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
  val () = run_sevens()
  val () = run_pieces("aj2000000/1000", 1000, 2000, 10)
in end
