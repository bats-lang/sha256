#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use sha256 as SHA

(* The proved rounds and chaining add of SHA-256 and SHA-1 (stage C of
   sha256#29) on the standard's vectors: "abc" (FIPS 180-2 appendix B.1,
   SHA-1's A.1), the 448-bit message (B.2, A.2; two blocks) and 64 bytes
   that are not text. For each round of the first two vectors it prints the
   working variables after the round, made by sha256_round and sha1_round
   from the constants of sha256_k and sha1_k and the words of the proved
   schedule. For each vector it prints the digest that sha256_compress and
   sha1_compress chain the blocks into (the proved chaining add) and how many
   of its words differ from an independent implementation written here in C
   unsigned arithmetic from the formulas, with a table of constants of its
   own (computed in Python from their definitions; the library's is not
   used). The harness compares the output with `expected`, written by
   make-test.py with an implementation in Python integers that also hashes
   the vectors to hashlib's digests. *)

fn _u (x: int): uint = g0int2uint_int_uint(x)

(* byte i of the message of a vector: 0 is "abc"; 1 is the 448-bit message
   "abcdbcdecdef...nopq" of 56 bytes; 2 is 64 bytes that are not text *)
fn byte_at (vector: int, i: int): int =
  if vector = 0 then 97 + i
  else if vector = 1 then 97 + $AR.div_int_int(i, 4) + $AR.mod_int_int(i, 4)
  else $AR.mod_int_int(i * 7 + 3, 256)

fn message_length (vector: int): int =
  if vector = 0 then 3 else if vector = 1 then 56 else 64

fn name_of (vector: int): string =
  if vector = 0 then "abc" else if vector = 1 then "448-bit message" else "64 bytes"

(* the padded message of a vector in 128 bytes (64 are used for "abc"): the
   message, the 0x80 byte, zeros and the length in bits as 64 bits, big endian *)
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

(* a word as the unsigned int it is, from its four bytes *)
fn word_uint {h,l:nat | h < 65536; l < 65536} (w: $AR.word32(h, l)): uint = let
  val (_ | b0) = $AR.word32_byte(w, 0)
  val (_ | b1) = $AR.word32_byte(w, 1)
  val (_ | b2) = $AR.word32_byte(w, 2)
  val (_ | b3) = $AR.word32_byte(w, 3)
in (_u(b0) << 24) lor (_u(b1) << 16) lor (_u(b2) << 8) lor _u(b3) end

fn print_value {h,l:nat | h < 65536; l < 65536} (w: $AR.word32(h, l)): void =
  (print_char(' '); print_word(word_uint(w)))

fn print_round (name: string, block: int, kind: string, t: int): void = let
  val () = print!(name, " block ", block, " ", kind, " t=")
  val () = (if t < 10 then print_char('0') else ())
in print!(t) end

(* ---- the independent references, in C unsigned arithmetic ---- *)

fn rotr {k:int | 0 < k; k < 32} (x: uint, k: int k): uint = (x >> k) lor (x << (32 - k))
fn rotl {k:int | 0 < k; k < 32} (x: uint, k: int k): uint = (x << k) lor (x >> (32 - k))

(* the constants of SHA-256 (section 4.2.2) and the first hash value
   (section 5.3.3), from integer cube and square roots *)
fn reference_k (i: int): uint =
  if i = 0 then 0x428a2f98u
  else if i = 1 then 0x71374491u
  else if i = 2 then 0xb5c0fbcfu
  else if i = 3 then 0xe9b5dba5u
  else if i = 4 then 0x3956c25bu
  else if i = 5 then 0x59f111f1u
  else if i = 6 then 0x923f82a4u
  else if i = 7 then 0xab1c5ed5u
  else if i = 8 then 0xd807aa98u
  else if i = 9 then 0x12835b01u
  else if i = 10 then 0x243185beu
  else if i = 11 then 0x550c7dc3u
  else if i = 12 then 0x72be5d74u
  else if i = 13 then 0x80deb1feu
  else if i = 14 then 0x9bdc06a7u
  else if i = 15 then 0xc19bf174u
  else if i = 16 then 0xe49b69c1u
  else if i = 17 then 0xefbe4786u
  else if i = 18 then 0x0fc19dc6u
  else if i = 19 then 0x240ca1ccu
  else if i = 20 then 0x2de92c6fu
  else if i = 21 then 0x4a7484aau
  else if i = 22 then 0x5cb0a9dcu
  else if i = 23 then 0x76f988dau
  else if i = 24 then 0x983e5152u
  else if i = 25 then 0xa831c66du
  else if i = 26 then 0xb00327c8u
  else if i = 27 then 0xbf597fc7u
  else if i = 28 then 0xc6e00bf3u
  else if i = 29 then 0xd5a79147u
  else if i = 30 then 0x06ca6351u
  else if i = 31 then 0x14292967u
  else if i = 32 then 0x27b70a85u
  else if i = 33 then 0x2e1b2138u
  else if i = 34 then 0x4d2c6dfcu
  else if i = 35 then 0x53380d13u
  else if i = 36 then 0x650a7354u
  else if i = 37 then 0x766a0abbu
  else if i = 38 then 0x81c2c92eu
  else if i = 39 then 0x92722c85u
  else if i = 40 then 0xa2bfe8a1u
  else if i = 41 then 0xa81a664bu
  else if i = 42 then 0xc24b8b70u
  else if i = 43 then 0xc76c51a3u
  else if i = 44 then 0xd192e819u
  else if i = 45 then 0xd6990624u
  else if i = 46 then 0xf40e3585u
  else if i = 47 then 0x106aa070u
  else if i = 48 then 0x19a4c116u
  else if i = 49 then 0x1e376c08u
  else if i = 50 then 0x2748774cu
  else if i = 51 then 0x34b0bcb5u
  else if i = 52 then 0x391c0cb3u
  else if i = 53 then 0x4ed8aa4au
  else if i = 54 then 0x5b9cca4fu
  else if i = 55 then 0x682e6ff3u
  else if i = 56 then 0x748f82eeu
  else if i = 57 then 0x78a5636fu
  else if i = 58 then 0x84c87814u
  else if i = 59 then 0x8cc70208u
  else if i = 60 then 0x90befffau
  else if i = 61 then 0xa4506cebu
  else if i = 62 then 0xbef9a3f7u
  else 0xc67178f2u

fn reference_h (i: int): uint =
  if i = 0 then 0x6a09e667u
  else if i = 1 then 0xbb67ae85u
  else if i = 2 then 0x3c6ef372u
  else if i = 3 then 0xa54ff53au
  else if i = 4 then 0x510e527fu
  else if i = 5 then 0x9b05688cu
  else if i = 6 then 0x1f83d9abu
  else 0x5be0cd19u

fn reference_h1 (i: int): uint =
  if i = 0 then 0x67452301u
  else if i = 1 then 0xefcdab89u
  else if i = 2 then 0x98badcfeu
  else if i = 3 then 0x10325476u
  else 0xc3d2e1f0u

fn block_word {l:agz}{at:nat | at + 64 <= 128}{t:nat | t < 16}
  (data: !$A.arr(byte, l, 128), at: int at, t: int t): uint = let
  val b0 = _u(byte2int0($A.get<byte>(data, at + 4 * t)))
  val b1 = _u(byte2int0($A.get<byte>(data, at + 4 * t + 1)))
  val b2 = _u(byte2int0($A.get<byte>(data, at + 4 * t + 2)))
  val b3 = _u(byte2int0($A.get<byte>(data, at + 4 * t + 3)))
in (b0 << 24) lor (b1 << 16) lor (b2 << 8) lor b3 end

(* the independent schedule of SHA-256 (section 6.2.2) *)
fun reference_schedule256 {l,lw:agz}{at:nat | at + 64 <= 128}{t:nat | t <= 64} .<64 - t>.
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
  in reference_schedule256(data, at, w, t + 1) end

(* the independent 64 rounds of SHA-256 on the working variables v *)
fun reference_rounds256 {lw,lv:agz}{t:nat | t <= 64} .<64 - t>.
  (w: !$A.arr(uint, lw, 64), v: !$A.arr(uint, lv, 8), t: int t): void =
  if t >= 64 then ()
  else let
    val a = $A.get<uint>(v, 0) val b = $A.get<uint>(v, 1) val c = $A.get<uint>(v, 2) val d = $A.get<uint>(v, 3)
    val e = $A.get<uint>(v, 4) val f = $A.get<uint>(v, 5) val g = $A.get<uint>(v, 6) val h = $A.get<uint>(v, 7)
    val t1 = h + (rotr(e, 6) lxor rotr(e, 11) lxor rotr(e, 25)) + ((e land f) lxor ((lnot e) land g))
             + reference_k(t) + $A.get<uint>(w, t)
    val t2 = (rotr(a, 2) lxor rotr(a, 13) lxor rotr(a, 22)) + ((a land b) lxor (a land c) lxor (b land c))
    val () = $A.set<uint>(v, 0, t1 + t2) val () = $A.set<uint>(v, 1, a) val () = $A.set<uint>(v, 2, b)
    val () = $A.set<uint>(v, 3, c) val () = $A.set<uint>(v, 4, d + t1) val () = $A.set<uint>(v, 5, e)
    val () = $A.set<uint>(v, 6, f) val () = $A.set<uint>(v, 7, g)
  in reference_rounds256(w, v, t + 1) end

fun add_into {lh,lv:agz}{n:nat}{i:nat | i <= n} .<n - i>.
  (h: !$A.arr(uint, lh, n), v: !$A.arr(uint, lv, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<uint>(h, i, $A.get<uint>(h, i) + $A.get<uint>(v, i))
  in add_into(h, v, n, i + 1) end

fun load_into {lv,lh:agz}{n:nat}{i:nat | i <= n} .<n - i>.
  (v: !$A.arr(uint, lv, n), h: !$A.arr(uint, lh, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<uint>(v, i, $A.get<uint>(h, i))
  in load_into(v, h, n, i + 1) end

(* the independent compression of one block of SHA-256 onto h *)
fn reference256 {l,lh:agz}{at:nat | at + 64 <= 128}
  (data: !$A.arr(byte, l, 128), at: int at, h: !$A.arr(uint, lh, 8)): void = let
  val w = $A.alloc<uint>(64)
  val () = reference_schedule256(data, at, w, 0)
  val v = $A.alloc<uint>(8)
  val () = load_into(v, h, 8, 0)
  val () = reference_rounds256(w, v, 0)
  val () = add_into(h, v, 8, 0)
  val () = $A.free<uint>(w)
  val () = $A.free<uint>(v)
in end

(* the independent SHA-1 (sections 4.1.1, 4.2.1, 6.1.2) *)
fun reference_schedule1 {l,lw:agz}{at:nat | at + 64 <= 128}{t:nat | t <= 80} .<80 - t>.
  (data: !$A.arr(byte, l, 128), at: int at, w: !$A.arr(uint, lw, 80), t: int t): void =
  if t >= 80 then ()
  else let
    val value =
      (if t < 16 then block_word(data, at, t)
       else rotl($A.get<uint>(w, t - 3) lxor $A.get<uint>(w, t - 8)
                 lxor $A.get<uint>(w, t - 14) lxor $A.get<uint>(w, t - 16), 1)): uint
    val () = $A.set<uint>(w, t, value)
  in reference_schedule1(data, at, w, t + 1) end

fun reference_rounds1 {lw,lv:agz}{t:nat | t <= 80} .<80 - t>.
  (w: !$A.arr(uint, lw, 80), v: !$A.arr(uint, lv, 5), t: int t): void =
  if t >= 80 then ()
  else let
    val a = $A.get<uint>(v, 0) val b = $A.get<uint>(v, 1) val c = $A.get<uint>(v, 2)
    val d = $A.get<uint>(v, 3) val e = $A.get<uint>(v, 4)
    val f =
      (if t < 20 then (b land c) lor ((lnot b) land d)
       else if t < 40 then b lxor c lxor d
       else if t < 60 then (b land c) lor (b land d) lor (c land d)
       else b lxor c lxor d): uint
    val k =
      (if t < 20 then 0x5a827999u else if t < 40 then 0x6ed9eba1u
       else if t < 60 then 0x8f1bbcdcu else 0xca62c1d6u): uint
    val () = $A.set<uint>(v, 0, rotl(a, 5) + f + e + k + $A.get<uint>(w, t))
    val () = $A.set<uint>(v, 1, a) val () = $A.set<uint>(v, 2, rotl(b, 30))
    val () = $A.set<uint>(v, 3, c) val () = $A.set<uint>(v, 4, d)
  in reference_rounds1(w, v, t + 1) end

fn reference1 {l,lh:agz}{at:nat | at + 64 <= 128}
  (data: !$A.arr(byte, l, 128), at: int at, h: !$A.arr(uint, lh, 5)): void = let
  val w = $A.alloc<uint>(80)
  val () = reference_schedule1(data, at, w, 0)
  val v = $A.alloc<uint>(5)
  val () = load_into(v, h, 5, 0)
  val () = reference_rounds1(w, v, 0)
  val () = add_into(h, v, 5, 0)
  val () = $A.free<uint>(w)
  val () = $A.free<uint>(v)
in end

(* ---- the proved rounds, one at a time ---- *)

fun trace256 {lw:agz}{words:$A.cells}{t:nat | t <= 64}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low:nat | a_high < 65536; a_low < 65536; b_high < 65536; b_low < 65536; c_high < 65536; c_low < 65536; d_high < 65536; d_low < 65536; e_high < 65536; e_low < 65536; f_high < 65536; f_low < 65536; g_high < 65536; g_low < 65536; h_high < 65536; h_low < 65536} .<64 - t>.
  (name: string, block: int, schedule: !$A.barr(lw, 256, words), t: int t, a_word: $AR.word32(a_high, a_low), b_word: $AR.word32(b_high, b_low), c_word: $AR.word32(c_high, c_low), d_word: $AR.word32(d_high, d_low), e_word: $AR.word32(e_high, e_low), f_word: $AR.word32(f_high, f_low), g_word: $AR.word32(g_high, g_low), h_word: $AR.word32(h_high, h_low)): void =
  if t >= 64 then ()
  else let
    val (_ | k_word) = $SHA.sha256_k_w32(t)
    val (_ | w_word) = $SHA.word_get_w32(schedule, 4 * t)
    val (_ | @(new_a_word, new_e_word)) =
      $SHA.sha256_round_w32(a_word, b_word, c_word, d_word, e_word, f_word, g_word, h_word, k_word, w_word)
    val () = print_round(name, block, "sha256", t)
    val () = print_value(new_a_word)
    val () = print_value(a_word)
    val () = print_value(b_word)
    val () = print_value(c_word)
    val () = print_value(new_e_word)
    val () = print_value(e_word)
    val () = print_value(f_word)
    val () = print_value(g_word)
    val () = print_newline()
  in trace256(name, block, schedule, t + 1,
       new_a_word, a_word, b_word, c_word,
       new_e_word, e_word, f_word, g_word) end

fun trace1 {lw:agz}{words:$A.cells}{t:nat | t <= 80}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low:nat | a_high < 65536; a_low < 65536; b_high < 65536; b_low < 65536; c_high < 65536; c_low < 65536; d_high < 65536; d_low < 65536; e_high < 65536; e_low < 65536} .<80 - t>.
  (name: string, block: int, schedule: !$A.barr(lw, 320, words), t: int t, a_word: $AR.word32(a_high, a_low), b_word: $AR.word32(b_high, b_low), c_word: $AR.word32(c_high, c_low), d_word: $AR.word32(d_high, d_low), e_word: $AR.word32(e_high, e_low)): void =
  if t >= 80 then ()
  else let
    val (_ | k_word) = $SHA.sha1_k_w32(t)
    val (_ | w_word) = $SHA.word_get_w32(schedule, 4 * t)
    val (_ | @(new_a_word, new_c_word)) =
      $SHA.sha1_round_w32(t, a_word, b_word, c_word, d_word, e_word, k_word, w_word)
    val () = print_round(name, block, "sha1", t)
    val () = print_value(new_a_word)
    val () = print_value(a_word)
    val () = print_value(new_c_word)
    val () = print_value(c_word)
    val () = print_value(d_word)
    val () = print_newline()
  in trace1(name, block, schedule, t + 1,
       new_a_word, a_word, new_c_word, c_word, d_word) end

(* how many of the n words of the chaining value differ from the reference *)
fun differing {lc,lr:agz}{size:nat}{cs:$A.cells}{n:nat | 4 * n <= size}{i:nat | i <= n} .<n - i>.
  (chaining: !$A.barr(lc, size, cs), reference: !$A.arr(uint, lr, n), n: int n, i: int i, found: int): int =
  if i >= n then found
  else let
    val (_ | word_value) = $SHA.word_get_w32(chaining, 4 * i)
    val word = word_uint(word_value)
    val bad = (if word = $A.get<uint>(reference, i) then 0 else 1): int
  in differing(chaining, reference, n, i + 1, found + bad) end

fun print_chaining {lc:agz}{size:nat}{cs:$A.cells}{n:nat | 4 * n <= size}{i:nat | i <= n} .<n - i>.
  (chaining: !$A.barr(lc, size, cs), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val (_ | word_value) = $SHA.word_get_w32(chaining, 4 * i)
    val () = print_value(word_value)
  in print_chaining(chaining, n, i + 1) end

(* the blocks of a vector, one after the other, through sha256_compress: the
   proof of each block's chaining value is the next block's *)
fun blocks256 {lm,lw,lc,lr:agz}{msg,words,chain:$A.cells}{at:nat}{left:nat | at + 64 * left <= 128}
  {h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536; h5_high < 65536; h5_low < 65536; h6_high < 65536; h6_low < 65536; h7_high < 65536; h7_low < 65536} .<left>.
  (name: string, block: int, message: !$A.barr(lm, 128, msg), at: int at,
   schedule: $A.barr(lw, 256, words), chaining: $A.barr(lc, 32, chain),
   have: $SHA.EIGHT_AT(chain, 0, $SHA.eight($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low), $SHA.w32(h5_high, h5_low), $SHA.w32(h6_high, h6_low), $SHA.w32(h7_high, h7_low))), left: int left,
   reference: !$A.arr(uint, lr, 8), traced: bool): void =
  if left = 0 then let
    val () = print!(name, " sha256 digest")
    val () = print_chaining(chaining, 8, 0)
    val () = print!(" differing=", differing(chaining, reference, 8, 0, 0))
    val () = print_newline()
    val () = $A.barr_free(schedule)
    val () = $A.barr_free(chaining)
  in end
  else let
    val (_ | scratch) = $A.barr_alloc(256)
    val (_ | scratch) = $SHA.schedule_sha256(message, at, scratch)
    val @(h0_word, h1_word, h2_word, h3_word, h4_word, h5_word, h6_word, h7_word) = $SHA.eight_get_w32(chaining, 0, have)
    val () = (if traced then
      trace256(name, block, scratch, 0, h0_word, h1_word, h2_word, h3_word, h4_word, h5_word, h6_word, h7_word) else ())
    val () = $A.barr_free(scratch)
    val (_, have_next | @(schedule, chaining)) = $SHA.sha256_compress(message, at, schedule, chaining, have)
  in blocks256(name, block + 1, message, at + 64, schedule, chaining, have_next, left - 1, reference, traced) end

fun blocks1 {lm,lw,lc,lr:agz}{msg,words,chain:$A.cells}{at:nat}{left:nat | at + 64 * left <= 128}
  {h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536} .<left>.
  (name: string, block: int, message: !$A.barr(lm, 128, msg), at: int at,
   schedule: $A.barr(lw, 320, words), chaining: $A.barr(lc, 20, chain),
   have: $SHA.FIVE_AT(chain, 0, $SHA.five($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low))), left: int left,
   reference: !$A.arr(uint, lr, 5), traced: bool): void =
  if left = 0 then let
    val () = print!(name, " sha1 digest")
    val () = print_chaining(chaining, 5, 0)
    val () = print!(" differing=", differing(chaining, reference, 5, 0, 0))
    val () = print_newline()
    val () = $A.barr_free(schedule)
    val () = $A.barr_free(chaining)
  in end
  else let
    val (_ | scratch) = $A.barr_alloc(320)
    val (_ | scratch) = $SHA.schedule_sha1(message, at, scratch)
    val @(h0_word, h1_word, h2_word, h3_word, h4_word) = $SHA.five_get_w32(chaining, 0, have)
    val () = (if traced then
      trace1(name, block, scratch, 0, h0_word, h1_word, h2_word, h3_word, h4_word) else ())
    val () = $A.barr_free(scratch)
    val (_, have_next | @(schedule, chaining)) = $SHA.sha1_compress(message, at, schedule, chaining, have)
  in blocks1(name, block + 1, message, at + 64, schedule, chaining, have_next, left - 1, reference, traced) end

fun init_reference {lr:agz}{n:nat}{i:nat | i <= n} .<n - i>.
  (r: !$A.arr(uint, lr, n), n: int n, i: int i, five: bool): void =
  if i >= n then ()
  else let
    val () = (if five then $A.set<uint>(r, i, reference_h1(i)) else $A.set<uint>(r, i, reference_h(i)))
  in init_reference(r, n, i + 1, five) end

fun reference_blocks256 {l,lh:agz}{at:nat}{left:nat | at + 64 * left <= 128} .<left>.
  (data: !$A.arr(byte, l, 128), at: int at, left: int left, h: !$A.arr(uint, lh, 8)): void =
  if left = 0 then ()
  else let
    val () = reference256(data, at, h)
  in reference_blocks256(data, at + 64, left - 1, h) end

fun reference_blocks1 {l,lh:agz}{at:nat}{left:nat | at + 64 * left <= 128} .<left>.
  (data: !$A.arr(byte, l, 128), at: int at, left: int left, h: !$A.arr(uint, lh, 5)): void =
  if left = 0 then ()
  else let
    val () = reference1(data, at, h)
  in reference_blocks1(data, at + 64, left - 1, h) end

fn run (vector: int): void = let
  val name = name_of(vector)
  val data = $A.alloc<byte>(128)
  val () = pad_fill(data, vector, 0)
  val two = (vector > 0): bool
  val reference256_value = $A.alloc<uint>(8)
  val () = init_reference(reference256_value, 8, 0, false)
  val left = (if two then 2 else 1): [l:nat | 1 <= l; l <= 2] int l
  val () = reference_blocks256(data, 0, left, reference256_value)
  val reference1_value = $A.alloc<uint>(5)
  val () = init_reference(reference1_value, 5, 0, true)
  val () = reference_blocks1(data, 0, left, reference1_value)
  val (_ | message) = $A.barr_of_arr(data)
  val traced = (vector < 2): bool
  val (_ | chain256) = $A.barr_alloc(32)
  val (have256 | chain256) = $SHA.eight_set_w32(chain256, 0, $AR.word32_pack(0x6a, 0x09, 0xe6, 0x67), $AR.word32_pack(0xbb, 0x67, 0xae, 0x85), $AR.word32_pack(0x3c, 0x6e, 0xf3, 0x72), $AR.word32_pack(0xa5, 0x4f, 0xf5, 0x3a), $AR.word32_pack(0x51, 0x0e, 0x52, 0x7f), $AR.word32_pack(0x9b, 0x05, 0x68, 0x8c), $AR.word32_pack(0x1f, 0x83, 0xd9, 0xab), $AR.word32_pack(0x5b, 0xe0, 0xcd, 0x19))
  val (_ | schedule256) = $A.barr_alloc(256)
  val () = blocks256(name, 0, message, 0, schedule256, chain256, have256, left, reference256_value, traced)
  val (_ | chain1) = $A.barr_alloc(20)
  val (have1 | chain1) = $SHA.five_set_w32(chain1, 0, $AR.word32_pack(0x67, 0x45, 0x23, 0x01), $AR.word32_pack(0xef, 0xcd, 0xab, 0x89), $AR.word32_pack(0x98, 0xba, 0xdc, 0xfe), $AR.word32_pack(0x10, 0x32, 0x54, 0x76), $AR.word32_pack(0xc3, 0xd2, 0xe1, 0xf0))
  val (_ | schedule1) = $A.barr_alloc(320)
  val () = blocks1(name, 0, message, 0, schedule1, chain1, have1, left, reference1_value, traced)
  val () = $A.barr_free(message)
  val () = $A.free<uint>(reference256_value)
  val () = $A.free<uint>(reference1_value)
in end

(* every constant of the tables, as the proved lookup gives it *)
fun print_constants256 {t:nat | t <= 64} .<64 - t>. (t: int t): void =
  if t >= 64 then ()
  else let
    val (_ | word_value) = $SHA.sha256_k_w32(t)
    val () = print!("sha256 K", t, " ")
    val () = (print_word(word_uint(word_value)); print_newline())
  in print_constants256(t + 1) end

fun print_constants1 {t:nat | t <= 80} .<80 - t>. (t: int t): void =
  if t >= 80 then ()
  else let
    val (_ | word_value) = $SHA.sha1_k_w32(t)
    val () = print!("sha1 K", t, " ")
    val () = (print_word(word_uint(word_value)); print_newline())
  in print_constants1(t + 1) end

implement main0 () = let
  val () = print_constants256(0)
  val () = print_constants1(0)
  val () = run(0)
  val () = run(1)
  val () = run(2)
in end
