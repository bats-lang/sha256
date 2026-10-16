#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Prints the digests of the proved API of stage D; the harness compares the
   output with `expected`, made by hashlib (make-expected.py) from the same
   messages. A message is made of its bytes by a rule of the byte's index:
   mode 0 repeats the letters a to z from `a` in a period p; mode 1 is the
   448-bit message of FIPS 180-2 B.2, "abcdbcdecdefdefg...nopq" (the i-th
   byte is a + i / 4 + i mod 4, for i under 56). *)

(* i modulo p *)
fun modulo {i:nat}{period:pos} .<i>. (i: int i, period: int period): [result:nat | result < period] int result =
  if i < period then i else modulo(i - period, period)

fn byte_at {i:nat}{period:int} (mode: int, period: int period, i: int i): [value:nat | value < 256] int value =
  if mode = 0 then (if period >= 1 then (if period <= 26 then 97 + modulo(i, period) else 97) else 97)
  else 97 + modulo(i / 4, 20) + modulo(i, 4)

(* cells base to base + n - 1 of the message written to the buffer *)
fun fill {loc:agz}{n:nat}{cells:$A.cells}{base:nat}{period:int}{i:nat | i <= n} .<n - i>.
  (block: $A.barr(loc, n, cells), n: int n, base: int base, mode: int, period: int period, i: int i)
  : [cells_after:$A.cells] $A.barr(loc, n, cells_after) =
  if i >= n then block
  else let
    val (_ | block) = $A.barr_set(block, i, byte_at(mode, period, base + i))
  in fill(block, n, base, mode, period, i + 1) end

fun pr {loc:agz}{cells:$A.cells}{i:nat | i <= 64} .<64 - i>. (digits: !$A.barr(loc, 64, cells), i: int i): void =
  if i >= 64 then ()
  else let
    val (_ | value) = $A.barr_get(digits, i)
  in print_char(int2char0(value)); pr(digits, i + 1) end

(* The message of total bytes fed in pieces of at most `piece` bytes *)
fun feed {message:$A.cells}{offset:nat}{total:nat | offset <= total}{piece:pos | piece <= 1048576}{period:int} .<total - offset>.
  (context: $SHA.ctx256(message), mode: int, period: int period, total: int total, offset: int offset, piece: int piece)
  : [message_after:$A.cells] $SHA.ctx256(message_after) =
  if offset >= total then context
  else let
    val taken = (if total - offset < piece then total - offset else piece): [taken:pos | taken <= piece; offset + taken <= total] int taken
    val (_ | data) = $A.barr_alloc(piece)
    val data = fill(data, piece, offset, mode, period, 0)
    val result = $SHA.update256_proved(context, data, taken)
    val () = $A.barr_free(data)
  in
    case+ result of
    | ~$SHA.Updated256(_ | context_after) => feed(context_after, mode, period, total, offset + taken, piece)
    | ~$SHA.Stopped256(_ | context_after) => context_after
  end

fn run {total:nat}{piece:pos | piece <= 1048576}{period:int}
  (name: string, mode: int, period: int period, total: int total, piece: int piece): void = let
  val context = $SHA.init256_proved()
  val context = feed(context, mode, period, total, 0, piece)
  val (_ | out) = $A.barr_alloc(64)
  val (_, _ | out) = $SHA.finish256_proved(context, out)
  val () = print!(name, " ")
  val () = pr(out, 0)
  val () = print_newline()
  val () = $A.barr_free(out)
in end

(* The same message in one call *)
fn run_once {total:nat | total <= 65535}{period:int}
  (name: string, mode: int, period: int period, total: int total): void = let
  val (_ | data) = $A.barr_alloc(total + 1)
  val data = fill(data, total + 1, 0, mode, period, 0)
  val (_ | out) = $A.barr_alloc(64)
  val (_, _, _ | out) = $SHA.sha256_digest_proved(data, total, out)
  val () = print!(name, " ")
  val () = pr(out, 0)
  val () = print_newline()
  val () = $A.barr_free(out)
  val () = $A.barr_free(data)
in end

fun pr20 {loc:agz}{cells:$A.cells}{i:nat | i <= 20} .<20 - i>. (offset: !$A.barr(loc, 20, cells), i: int i): void =
  if i >= 20 then ()
  else let
    val (_ | value) = $A.barr_get(offset, i)
    val high_nibble = value / 16
    val low_nibble = value - 16 * high_nibble
    val () = print_char(int2char0(if high_nibble < 10 then 48 + high_nibble else 87 + high_nibble))
    val () = print_char(int2char0(if low_nibble < 10 then 48 + low_nibble else 87 + low_nibble))
  in pr20(offset, i + 1) end

fn run_sha1 {total:nat | total <= 65535}{period:int}
  (name: string, mode: int, period: int period, total: int total): void = let
  val (_ | data) = $A.barr_alloc(total + 1)
  val data = fill(data, total + 1, 0, mode, period, 0)
  val (_ | out) = $A.barr_alloc(20)
  val (_, _, _ | out) = $SHA.sha1_digest_proved(data, total, out)
  val () = print!("sha1 ", name, " ")
  val () = pr20(out, 0)
  val () = print_newline()
  val () = $A.barr_free(out)
  val () = $A.barr_free(data)
in end

implement main0 () = let
  (* the message of FIPS 180-2 B.1, the empty message, B.2, and the lengths
     around the padding's edges: 55 (one block), 56 (two), 63, 64, 65 *)
  val () = run("empty", 0, 26, 0, 1)
  val () = run("abc", 0, 26, 3, 64)
  val () = run("b2", 1, 0, 56, 64)
  val () = run("a55", 0, 26, 55, 64)
  val () = run("a56", 0, 26, 56, 64)
  val () = run("a63", 0, 26, 63, 64)
  val () = run("a64", 0, 26, 64, 64)
  val () = run("a65", 0, 26, 65, 64)
  val () = run("a119", 0, 26, 119, 64)
  val () = run("a120", 0, 26, 120, 64)
  val () = run("a128", 0, 26, 128, 64)
  val () = run("aj1000", 0, 10, 1000, 1000)
  (* the same messages in other pieces *)
  val () = run("abc/1", 0, 26, 3, 1)
  val () = run("b2/1", 1, 0, 56, 1)
  val () = run("a56/7", 0, 26, 56, 7)
  val () = run("a64/64", 0, 26, 64, 64)
  val () = run("a65/64", 0, 26, 65, 64)
  val () = run("a120/13", 0, 26, 120, 13)
  val () = run("aj1000/7", 0, 10, 1000, 7)
  val () = run("aj1000/64", 0, 10, 1000, 64)
  val () = run("aj1000/1", 0, 10, 1000, 1)
  val () = run("aj10000/4097", 0, 10, 10000, 4097)
  (* in one call *)
  val () = run_once("empty", 0, 26, 0)
  val () = run_once("abc", 0, 26, 3)
  val () = run_once("b2", 1, 0, 56)
  val () = run_once("a55", 0, 26, 55)
  val () = run_once("a56", 0, 26, 56)
  val () = run_once("a63", 0, 26, 63)
  val () = run_once("a64", 0, 26, 64)
  val () = run_once("a65", 0, 26, 65)
  val () = run_once("a119", 0, 26, 119)
  val () = run_once("a120", 0, 26, 120)
  val () = run_once("a128", 0, 26, 128)
  val () = run_once("aj1000", 0, 10, 1000)
  val () = run_once("aj10000", 0, 10, 10000)
  (* SHA-1, in one call *)
  val () = run_sha1("empty", 0, 26, 0)
  val () = run_sha1("abc", 0, 26, 3)
  val () = run_sha1("b2", 1, 0, 56)
  val () = run_sha1("a55", 0, 26, 55)
  val () = run_sha1("a56", 0, 26, 56)
  val () = run_sha1("a63", 0, 26, 63)
  val () = run_sha1("a64", 0, 26, 64)
  val () = run_sha1("a65", 0, 26, 65)
  val () = run_sha1("a119", 0, 26, 119)
  val () = run_sha1("a120", 0, 26, 120)
  val () = run_sha1("a128", 0, 26, 128)
  val () = run_sha1("aj1000", 0, 10, 1000)
  val () = run_sha1("aj10000", 0, 10, 10000)
in end
