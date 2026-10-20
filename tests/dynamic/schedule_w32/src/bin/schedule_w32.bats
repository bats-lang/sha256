#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use sha256 as SHA

(* The proved message schedules (SHA-256's 64 words, SHA-1's 80) on the
   padded blocks of the standard's examples ("abc", FIPS 180-2 appendix
   B.1 and SHA-1's appendix A.1; the 448-bit message of B.2 and A.2, two
   blocks) and of a block of 64 other bytes. Each word the schedule wrote
   into its array is compared with the words of an independent
   implementation, written here in C unsigned arithmetic from the
   standard's formulas. Prints, per block, how many of the words differ,
   and some words of the schedule of "abc"; the harness compares the
   output with `expected` (made by an implementation in Python). *)

fn _u (x: int): uint = g0int2uint_int_uint(x)

(* byte i of the message of a vector: 0 is "abc"; 1 is the 448-bit message
   "abcdbcdecdef...nopq" of 56 bytes; 2 is 64 bytes that are not text *)
fn byte_at (vector: int, i: int): int =
  if vector = 0 then 97 + i
  else if vector = 1 then 97 + $AR.div_int_int(i, 4) + $AR.mod_int_int(i, 4)
  else $AR.mod_int_int(i * 7 + 3, 256)

fn message_length (vector: int): int =
  if vector = 0 then 3 else if vector = 1 then 56 else 64

(* the padded message of a vector in 128 bytes (of which the first 64 or
   all are used): the message, the 0x80 byte, zeros and the length in bits
   as 64 bits, big endian *)
fun pad_fill {l:agz}{i:nat | i <= 128} .<128 - i>.
  (cells: !$A.arr(byte, l, 128), vector: int, i: int i): void =
  if i >= 128 then ()
  else let
    val length = message_length(vector)
    val padded_length = (if vector = 0 then 64 else 128): int
    val value =
      (if i < length then byte_at(vector, i)
       else if i = length then 128
       else if i = padded_length - 1 then $AR.mod_int_int(length * 8, 256)
       else if i = padded_length - 2 then $AR.div_int_int(length * 8, 256)
       else 0): int
    val () = $A.set<byte>(cells, i, $A.int2byte($AR.low_byte(value)))
  in pad_fill(cells, vector, i + 1) end

fn hex_digit (d: int): char = if d < 10 then int2char0(48 + d) else int2char0(87 + d)

fn print_word (word: uint): void = let
  fun go {i:nat | i <= 8} .<8 - i>. (i: int i): void =
    if i >= 8 then ()
    else let
      val digit = g0uint2int_uint_int((word >> (28 - 4 * i)) land 0xfu)
      val () = print_char(hex_digit(digit))
    in go(i + 1) end
in go(0) end

(* word t of the block at `at`, big endian, from the bytes *)
fn block_word {l:agz}{at:nat | at + 64 <= 128}{t:nat | t < 16}
  (data: !$A.arr(byte, l, 128), at: int at, t: int t): uint = let
  val b0 = _u(byte2int0($A.get<byte>(data, at + 4 * t)))
  val b1 = _u(byte2int0($A.get<byte>(data, at + 4 * t + 1)))
  val b2 = _u(byte2int0($A.get<byte>(data, at + 4 * t + 2)))
  val b3 = _u(byte2int0($A.get<byte>(data, at + 4 * t + 3)))
in (b0 << 24) lor (b1 << 16) lor (b2 << 8) lor b3 end

fn rotr {k:int | 0 < k; k < 32} (x: uint, k: int k): uint = (x >> k) lor (x << (32 - k))

(* the independent SHA-256 schedule (FIPS 180-4, section 6.2.2) *)
fun reference256 {l,lw:agz}{at:nat | at + 64 <= 128}{t:nat | t <= 64} .<64 - t>.
  (data: !$A.arr(byte, l, 128), at: int at, w: !$A.arr(uint, lw, 64), t: int t): void =
  if t >= 64 then ()
  else let
    val value =
      (if t < 16 then block_word(data, at, t)
       else let
         val x = $A.get<uint>(w, t - 2)
         val y = $A.get<uint>(w, t - 15)
         val s1 = rotr(x, 17) lxor rotr(x, 19) lxor (x >> 10)
         val s0 = rotr(y, 7) lxor rotr(y, 18) lxor (y >> 3)
       in s1 + $A.get<uint>(w, t - 7) + s0 + $A.get<uint>(w, t - 16) end): uint
    val () = $A.set<uint>(w, t, value)
  in reference256(data, at, w, t + 1) end

(* the independent SHA-1 schedule (section 6.1.2) *)
fun reference1 {l,lw:agz}{at:nat | at + 64 <= 128}{t:nat | t <= 80} .<80 - t>.
  (data: !$A.arr(byte, l, 128), at: int at, w: !$A.arr(uint, lw, 80), t: int t): void =
  if t >= 80 then ()
  else let
    val value =
      (if t < 16 then block_word(data, at, t)
       else let
         val x = $A.get<uint>(w, t - 3) lxor $A.get<uint>(w, t - 8)
                 lxor $A.get<uint>(w, t - 14) lxor $A.get<uint>(w, t - 16)
       in (x << 1) lor (x >> 31) end): uint
    val () = $A.set<uint>(w, t, value)
  in reference1(data, at, w, t + 1) end

(* a word as the unsigned int it is, from its four bytes *)
fn word_uint {h,l:nat | h < 65536; l < 65536} (w: $AR.word32(h, l)): uint = let
  val (_ | b0) = $AR.word32_byte(w, 0)
  val (_ | b1) = $AR.word32_byte(w, 1)
  val (_ | b2) = $AR.word32_byte(w, 2)
  val (_ | b3) = $AR.word32_byte(w, 3)
in (_u(b0) << 24) lor (_u(b1) << 16) lor (_u(b2) << 8) lor _u(b3) end

(* how many of the first count words of the array the reference differs in *)
fun differing {lw,lr:agz}{nw:nat}{cs:$A.cells}{count:nat | 4 * count <= nw}{t:nat | t <= count} .<count - t>.
  (array: !$A.barr(lw, nw, cs), reference: !$A.arr(uint, lr, count), count: int count, t: int t, found: int): int =
  if t >= count then found
  else let
    val (_ | word_value) = $SHA.word_get_w32(array, 4 * t)
    val word = word_uint(word_value)
    val bad = (if word = $A.get<uint>(reference, t) then 0 else 1): int
  in differing(array, reference, count, t + 1, found + bad) end

fn show {lw,lr:agz}{nw:nat}{cs:$A.cells}{count:nat | 4 * count <= nw}
  (array: !$A.barr(lw, nw, cs), reference: !$A.arr(uint, lr, count), count: int count, shown: int): void = let
  val () = print!(" differing=", differing(array, reference, count, 0, 0))
in
  if shown > 0 then let
    val () = print_string(" W16..W21=")
    fun go {t:nat | t <= count} .<count - t>. (r: !$A.arr(uint, lr, count), count: int count, t: int t): void =
      if t >= 22 then ()
      else if t >= count then ()
      else let
        val () = (if t >= 16 then (print_word($A.get<uint>(r, t)); print_char(' ')) else ())
      in go(r, count, t + 1) end
  in go(reference, count, 0) end
  else ()
end

(* One block of one vector, through both schedules *)
fn run (name: string, vector: int, at: [a:nat | a + 64 <= 128] int a, shown: int): void = let
  val data = $A.alloc<byte>(128)
  val () = pad_fill(data, vector, 0)
  val ref256 = $A.alloc<uint>(64)
  val () = reference256(data, at, ref256, 0)
  val ref1 = $A.alloc<uint>(80)
  val () = reference1(data, at, ref1, 0)
  val (_ | message) = $A.barr_of_arr(data)
  val (_ | words256) = $A.barr_alloc(256)
  val (_ | words256) = $SHA.schedule_sha256(message, at, words256)
  val (_ | words1) = $A.barr_alloc(320)
  val (_ | words1) = $SHA.schedule_sha1(message, at, words1)
  val () = print!(name, " sha256")
  val () = show(words256, ref256, 64, shown)
  val () = print!("\n", name, " sha1")
  val () = show(words1, ref1, 80, shown)
  val () = print_newline()
  val () = $A.barr_free(words256)
  val () = $A.barr_free(words1)
  val () = $A.barr_free(message)
  val () = $A.free<uint>(ref256)
  val () = $A.free<uint>(ref1)
in end

implement main0 () = let
  val () = run("abc block 0", 0, 0, 1)
  val () = run("448-bit message block 0", 1, 0, 1)
  val () = run("448-bit message block 1", 1, 64, 1)
  val () = run("64 bytes block 0", 2, 0, 1)
  val () = run("64 bytes block 1", 2, 64, 1)
in end
