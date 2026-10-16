(* sha256 -- SHA-256 and SHA-1 (FIPS 180-4) in Bats
   No C code, no $UNSAFE, no praxi. Two implementations of SHA-256 sit side
   by side. hash, init, update and finish (below) are the fast one: 32-bit
   words are uint, and C unsigned arithmetic wraps modulo 2^32 by definition,
   so no operation overflows (signed int arithmetic would); it assumes a
   32-bit unsigned int, as on every bats target (LP64 and ILP32 native,
   wasm32); it is tested, not proved. proved_hash, proved_init, proved_update
   and proved_finish, and sha1_digest, run the proved code: a 32-bit word is
   its two 16-bit halves (arith's ROTR, SHR, ADD32) and the digest is the one
   the proofs are about (sha256#29). The proved code is about 30 times slower
   (sha256#34), so the fast API is not replaced by it. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR

(* ============================================================
   Public API
   ============================================================ *)

(* The SHA-256 of data[0, data_len) as 64 lowercase hex digits in out. *)
#pub fn hash
  {l:agz}{n:pos}{lo:agz}
  (data: !$A.arr(byte, l, n), data_len: int n,
   out: !$A.arr(byte, lo, 64)): void

(* An incremental SHA-256: init, update with each piece of the input in
   order, then finish. For input that does not fit one array, such as a
   file read in chunks. *)
#pub datavtype ctx =
  | {lh,lw,lb:agz}{b:nat | b < 64} ctx_mk of (
      $A.arr(uint, lh, 8),   (* the hash state *)
      $A.arr(uint, lw, 64),  (* the message schedule *)
      $A.arr(byte, lb, 64),  (* the bytes of the block being filled *)
      int b,                 (* how many of them there are *)
      uint, uint             (* the bytes hashed so far, high and low words *)
    )

#pub fn init (): ctx

(* Hashes data[0, len) after everything given so far. *)
#pub fn update
  {l:agz}{n:pos}{k:nat | k <= n}
  (c: !ctx, data: !$A.arr(byte, l, n), len: int k): void

(* The SHA-256 of everything given, as 64 lowercase hex digits in out. *)
#pub fn finish {lo:agz} (c: ctx, out: !$A.arr(byte, lo, 64)): void

(* ============================================================
   Word functions (FIPS 180-4, section 4.1.2)
   ============================================================ *)

fn _rotr {k:int | 0 < k; k < 32} (x: uint, k: int k): uint =
  (x >> k) lor (x << (32 - k))

fn _ch (x: uint, y: uint, z: uint): uint = (x land y) lxor ((lnot x) land z)

fn _maj (x: uint, y: uint, z: uint): uint =
  (x land y) lxor (x land z) lxor (y land z)

fn _bsig0 (x: uint): uint = _rotr(x, 2) lxor _rotr(x, 13) lxor _rotr(x, 22)
fn _bsig1 (x: uint): uint = _rotr(x, 6) lxor _rotr(x, 11) lxor _rotr(x, 25)
fn _ssig0 (x: uint): uint = _rotr(x, 7) lxor _rotr(x, 18) lxor (x >> 3)
fn _ssig1 (x: uint): uint = _rotr(x, 17) lxor _rotr(x, 19) lxor (x >> 10)

fn _u (x: int): uint = g0int2uint_int_uint(x)

(* ============================================================
   The word functions, proved (FIPS 180-4, section 4.1.2)

   A word is its two 16-bit halves (arith's ROTR, SHR, ADD32: the solver
   is 32-bit, so no proof names 2 to the 32). Each relation below is the
   standard's definition of the function, composed from arith's
   specifications of the bit operations; each function returns the proof
   that its result is related to its arguments (sha256#29).
   ============================================================ *)

(* CH(xh, xl, yh, yl, zh, zl, rh, rl): r is Ch(x, y, z) = (x and y) xor
   ((not x) and z) *)
#pub dataprop CH(int, int, int, int, int, int, int, int) =
  | {xh,xl,yh,yl,zh,zl,ah,al,nh,nl,bh,bl,rh,rl:nat}
    CH_mk(xh, xl, yh, yl, zh, zl, rh, rl) of (
      $AR.AND(xh, yh, ah), $AR.AND(xl, yl, al),
      $AR.NOT32(xh, xl, nh, nl),
      $AR.AND(nh, zh, bh), $AR.AND(nl, zl, bl),
      $AR.XOR(ah, bh, rh), $AR.XOR(al, bl, rl))

(* MAJ(xh, xl, yh, yl, zh, zl, rh, rl): r is Maj(x, y, z) = (x and y) xor
   (x and z) xor (y and z) *)
#pub dataprop MAJ(int, int, int, int, int, int, int, int) =
  | {xh,xl,yh,yl,zh,zl,ah,al,bh,bl,ch,cl,sh,sl,rh,rl:nat}
    MAJ_mk(xh, xl, yh, yl, zh, zl, rh, rl) of (
      $AR.AND(xh, yh, ah), $AR.AND(xl, yl, al),
      $AR.AND(xh, zh, bh), $AR.AND(xl, zl, bl),
      $AR.AND(yh, zh, ch), $AR.AND(yl, zl, cl),
      $AR.XOR(ah, bh, sh), $AR.XOR(al, bl, sl),
      $AR.XOR(sh, ch, rh), $AR.XOR(sl, cl, rl))

(* BIG_SIGMA_0(xh, xl, rh, rl): r is the upper case sigma 0 of x,
   ROTR 2 xor ROTR 13 xor ROTR 22; BIG_SIGMA_1: ROTR 6, 11, 25 *)
#pub dataprop BIG_SIGMA_0(int, int, int, int) =
  | {xh,xl,ah,al,bh,bl,ch,cl,sh,sl,rh,rl:nat}
    BIG_SIGMA_0_mk(xh, xl, rh, rl) of (
      $AR.ROTR(2, xh, xl, ah, al), $AR.ROTR(13, xh, xl, bh, bl), $AR.ROTR(22, xh, xl, ch, cl),
      $AR.XOR(ah, bh, sh), $AR.XOR(al, bl, sl),
      $AR.XOR(sh, ch, rh), $AR.XOR(sl, cl, rl))

#pub dataprop BIG_SIGMA_1(int, int, int, int) =
  | {xh,xl,ah,al,bh,bl,ch,cl,sh,sl,rh,rl:nat}
    BIG_SIGMA_1_mk(xh, xl, rh, rl) of (
      $AR.ROTR(6, xh, xl, ah, al), $AR.ROTR(11, xh, xl, bh, bl), $AR.ROTR(25, xh, xl, ch, cl),
      $AR.XOR(ah, bh, sh), $AR.XOR(al, bl, sl),
      $AR.XOR(sh, ch, rh), $AR.XOR(sl, cl, rl))

(* SMALL_SIGMA_0(xh, xl, rh, rl): r is the lower case sigma 0 of x, ROTR 7
   xor ROTR 18 xor SHR 3; SMALL_SIGMA_1: ROTR 17 xor ROTR 19 xor SHR 10 *)
#pub dataprop SMALL_SIGMA_0(int, int, int, int) =
  | {xh,xl,ah,al,bh,bl,ch,cl,sh,sl,rh,rl:nat}
    SMALL_SIGMA_0_mk(xh, xl, rh, rl) of (
      $AR.ROTR(7, xh, xl, ah, al), $AR.ROTR(18, xh, xl, bh, bl), $AR.SHR(3, xh, xl, ch, cl),
      $AR.XOR(ah, bh, sh), $AR.XOR(al, bl, sl),
      $AR.XOR(sh, ch, rh), $AR.XOR(sl, cl, rl))

#pub dataprop SMALL_SIGMA_1(int, int, int, int) =
  | {xh,xl,ah,al,bh,bl,ch,cl,sh,sl,rh,rl:nat}
    SMALL_SIGMA_1_mk(xh, xl, rh, rl) of (
      $AR.ROTR(17, xh, xl, ah, al), $AR.ROTR(19, xh, xl, bh, bl), $AR.SHR(10, xh, xl, ch, cl),
      $AR.XOR(ah, bh, sh), $AR.XOR(al, bl, sl),
      $AR.XOR(sh, ch, rh), $AR.XOR(sl, cl, rl))

#pub fun word_ch {xh,xl,yh,yl,zh,zl:nat | xh < 65536; xl < 65536; yh < 65536; yl < 65536; zh < 65536; zl < 65536}
  (xh: int xh, xl: int xl, yh: int yh, yl: int yl, zh: int zh, zl: int zl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (CH(xh, xl, yh, yl, zh, zl, rh, rl) | @(int rh, int rl))

implement word_ch (xh, xl, yh, yl, zh, zl) = let
  val (pah, pal | @(ah, al)) = $AR.and32(xh, xl, yh, yl)
  val (pnot | @(nh, nl)) = $AR.not32(xh, xl)
  val (pbh, pbl | @(bh, bl)) = $AR.and32(nh, nl, zh, zl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(ah, al, bh, bl)
in (CH_mk(pah, pal, pnot, pbh, pbl, prh, prl) | @(rh, rl)) end

#pub fun word_maj {xh,xl,yh,yl,zh,zl:nat | xh < 65536; xl < 65536; yh < 65536; yl < 65536; zh < 65536; zl < 65536}
  (xh: int xh, xl: int xl, yh: int yh, yl: int yl, zh: int zh, zl: int zl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (MAJ(xh, xl, yh, yl, zh, zl, rh, rl) | @(int rh, int rl))

implement word_maj (xh, xl, yh, yl, zh, zl) = let
  val (pah, pal | @(ah, al)) = $AR.and32(xh, xl, yh, yl)
  val (pbh, pbl | @(bh, bl)) = $AR.and32(xh, xl, zh, zl)
  val (pch, pcl | @(ch, cl)) = $AR.and32(yh, yl, zh, zl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (MAJ_mk(pah, pal, pbh, pbl, pch, pcl, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun big_sigma_0 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (BIG_SIGMA_0(xh, xl, rh, rl) | @(int rh, int rl))

implement big_sigma_0 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr_fast(2, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr_fast(13, xh, xl)
  val (pc | @(ch, cl)) = $AR.rotr_fast(22, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (BIG_SIGMA_0_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun big_sigma_1 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (BIG_SIGMA_1(xh, xl, rh, rl) | @(int rh, int rl))

implement big_sigma_1 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr_fast(6, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr_fast(11, xh, xl)
  val (pc | @(ch, cl)) = $AR.rotr_fast(25, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (BIG_SIGMA_1_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun small_sigma_0 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (SMALL_SIGMA_0(xh, xl, rh, rl) | @(int rh, int rl))

implement small_sigma_0 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr_fast(7, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr_fast(18, xh, xl)
  val (pc | @(ch, cl)) = $AR.shr(3, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (SMALL_SIGMA_0_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun small_sigma_1 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (SMALL_SIGMA_1(xh, xl, rh, rl) | @(int rh, int rl))

implement small_sigma_1 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr_fast(17, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr_fast(19, xh, xl)
  val (pc | @(ch, cl)) = $AR.shr(10, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (SMALL_SIGMA_1_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

(* ============================================================
   Words in an array, and the message schedules, proved
   (FIPS 180-4, sections 6.1.2 and 6.2.2, step 1)

   The cells of a byte array are known to the types (array's barr). A
   word of an array is four of its cells, the most significant byte
   first, so a word needs no array of its own and a message block's words
   are read from the bytes the block is: WORD_AT(cells, at, high, low) says
   that the four cells from `at` are the word high:low (high = 256 * b0 +
   b1, low = 256 * b2 + b3), and WORD_SET that setting four cells made the
   word. The words of the schedule are stored at 4 * t.
   ============================================================ *)

(* WORD_AT(cs, at, high, low): the cells at, at + 1, at + 2 and at + 3 of
   cs are the word high:low, big endian *)
#pub dataprop WORD_AT($A.cells, int, int, int) =
  | {cs:$A.cells}{at,b0,b1,b2,b3:nat | b0 < 256; b1 < 256; b2 < 256; b3 < 256}
    WORD_AT_mk(cs, at, 256*b0 + b1, 256*b2 + b3) of (
      $A.NTH(cs, at, b0), $A.NTH(cs, at + 1, b1),
      $A.NTH(cs, at + 2, b2), $A.NTH(cs, at + 3, b3))

(* WORD_SET(cs, at, high, low, cs2): cs2 is cs with the four cells from
   `at` set to the word high:low, one after the other *)
#pub dataprop WORD_SET($A.cells, int, int, int, $A.cells) =
  | {cs,cs1,cs2,cs3,cs4:$A.cells}{at,b0,b1,b2,b3:nat | b0 < 256; b1 < 256; b2 < 256; b3 < 256}
    WORD_SET_mk(cs, at, 256*b0 + b1, 256*b2 + b3, cs4) of (
      $A.SETC(cs, at, b0, cs1), $A.SETC(cs1, at + 1, b1, cs2),
      $A.SETC(cs2, at + 2, b2, cs3), $A.SETC(cs3, at + 3, b3, cs4))

(* The word at `at`, with the proof that it is *)
#pub fun word_get {l:agz}{n,at:nat | at + 3 < n}{cs:$A.cells}
  (cells: !$A.barr(l, n, cs), at: int at)
  : [high,low:nat | high < 65536; low < 65536] (WORD_AT(cs, at, high, low) | @(int high, int low))

implement word_get {l}{n,at}{cs} (cells, at) = let
  val (first | b0) = $A.barr_get(cells, at)
  val (second | b1) = $A.barr_get(cells, at + 1)
  val (third | b2) = $A.barr_get(cells, at + 2)
  val (fourth | b3) = $A.barr_get(cells, at + 3)
in (WORD_AT_mk(first, second, third, fourth) | @(256 * b0 + b1, 256 * b2 + b3)) end

(* The four cells from `at` set to the word, with the proof that they are *)
#pub fun word_set {l:agz}{n,at:nat | at + 3 < n}{cs:$A.cells}{high,low:nat | high < 65536; low < 65536}
  (cells: $A.barr(l, n, cs), at: int at, high: int high, low: int low)
  : [cs2:$A.cells] (WORD_SET(cs, at, high, low, cs2) | $A.barr(l, n, cs2))

implement word_set {l}{n,at}{cs}{high,low} (cells, at, high, low) = let
  val b0 = high / 256
  val b1 = high - 256 * b0
  val b2 = low / 256
  val b3 = low - 256 * b2
  val (first | cells) = $A.barr_set(cells, at, b0)
  val (second | cells) = $A.barr_set(cells, at + 1, b1)
  val (third | cells) = $A.barr_set(cells, at + 2, b2)
  val (fourth | cells) = $A.barr_set(cells, at + 3, b3)
in (WORD_SET_mk(first, second, third, fourth) | cells) end

(* What was set is the word that is read there afterwards *)
#pub prfun word_set_at {cs,cs2:$A.cells}{at,high,low:nat}
  (WORD_SET(cs, at, high, low, cs2)): WORD_AT(cs2, at, high, low)

primplement word_set_at {cs,cs2}{at,high,low} (set) = let
  prval WORD_SET_mk(s0, s1, s2, s3) = set
  prval n3 = $A.setc_nth_same(s3)
  prval n2 = $A.setc_nth_other(s3, $A.setc_nth_same(s2))
  prval n1 = $A.setc_nth_other(s3, $A.setc_nth_other(s2, $A.setc_nth_same(s1)))
  prval n0 = $A.setc_nth_other(s3, $A.setc_nth_other(s2, $A.setc_nth_other(s1, $A.setc_nth_same(s0))))
in WORD_AT_mk(n0, n1, n2, n3) end

(* A word whose cells are not the four set is as it was *)
#pub prfun word_set_other {cs,cs2:$A.cells}{at,high,low,other,other_high,other_low:nat | at + 4 <= other || other + 4 <= at}
  (WORD_SET(cs, at, high, low, cs2), WORD_AT(cs, other, other_high, other_low))
  : WORD_AT(cs2, other, other_high, other_low)

primplement word_set_other {cs,cs2}{at,high,low,other,other_high,other_low} (set, word) = let
  prval WORD_SET_mk(s0, s1, s2, s3) = set
  prval WORD_AT_mk(n0, n1, n2, n3) = word
  prfn through {c0,c1,c2,c3,c4:$A.cells}{b0,b1,b2,b3:nat}{index,value:nat | index + 1 <= at || at + 4 <= index}
    (s0: $A.SETC(c0, at, b0, c1), s1: $A.SETC(c1, at + 1, b1, c2), s2: $A.SETC(c2, at + 2, b2, c3),
     s3: $A.SETC(c3, at + 3, b3, c4), n: $A.NTH(c0, index, value)): $A.NTH(c4, index, value) =
    $A.setc_nth_other(s3, $A.setc_nth_other(s2, $A.setc_nth_other(s1, $A.setc_nth_other(s0, n))))
in WORD_AT_mk(through(s0, s1, s2, s3, n0), through(s0, s1, s2, s3, n1),
              through(s0, s1, s2, s3, n2), through(s0, s1, s2, s3, n3)) end

(* A word is one word: the cells are one value *)
#pub prfun word_at_functional {cs:$A.cells}{at,high,low,high2,low2:nat}
  (WORD_AT(cs, at, high, low), WORD_AT(cs, at, high2, low2)): [high == high2; low == low2] void

primplement word_at_functional {cs}{at,high,low,high2,low2} (first, second) = let
  prval WORD_AT_mk(a0, a1, a2, a3) = first
  prval WORD_AT_mk(b0, b1, b2, b3) = second
  prval () = $A.nth_functional(a0, b0)
  prval () = $A.nth_functional(a1, b1)
  prval () = $A.nth_functional(a2, b2)
  prval () = $A.nth_functional(a3, b3)
in end

(* ============================================================
   The schedule words of the standard

   SCHEDULE(kind, msg, at, t, high, low): W_t of the block that is the 64
   bytes from `at` of the cells msg is the word high:low, by the standard's
   definition and nothing of any array: for t under 16 the t-th word of the
   block (section 6.1.2 step 1, 6.2.2 step 1), and above:
     SHA-256: W_t = sigma1(W_t-2) + W_t-7 + sigma0(W_t-15) + W_t-16,
       added in that order, each modulo 2 to the 32 (ADD32)
     SHA-1: W_t = ROTL 1 (W_t-3 xor W_t-8 xor W_t-14 xor W_t-16), the
       rotation left by one being the rotation right by 31
   ============================================================ *)

#pub datasort schedule_kind =
  | sha256_kind of ()
  | sha1_kind of ()

#pub dataprop SCHEDULE(schedule_kind, $A.cells, int, int, int, int) =
  | {kind:schedule_kind}{msg:$A.cells}{at,t:nat | t < 16}{high,low:nat}
    SCHEDULE_message(kind, msg, at, t, high, low) of WORD_AT(msg, at + 4*t, high, low)
  | {msg:$A.cells}{at,t:nat | 16 <= t}
    {back2_high,back2_low,back7_high,back7_low,back15_high,back15_low,back16_high,back16_low:nat}
    {s1_high,s1_low,s0_high,s0_low,sum1_high,sum1_low,sum2_high,sum2_low,high,low:nat}
    SCHEDULE_sha256(sha256_kind(), msg, at, t, high, low) of (
      SCHEDULE(sha256_kind(), msg, at, t-2, back2_high, back2_low),
      SCHEDULE(sha256_kind(), msg, at, t-7, back7_high, back7_low),
      SCHEDULE(sha256_kind(), msg, at, t-15, back15_high, back15_low),
      SCHEDULE(sha256_kind(), msg, at, t-16, back16_high, back16_low),
      SMALL_SIGMA_1(back2_high, back2_low, s1_high, s1_low),
      SMALL_SIGMA_0(back15_high, back15_low, s0_high, s0_low),
      $AR.ADD32(s1_high, s1_low, back7_high, back7_low, sum1_high, sum1_low),
      $AR.ADD32(sum1_high, sum1_low, s0_high, s0_low, sum2_high, sum2_low),
      $AR.ADD32(sum2_high, sum2_low, back16_high, back16_low, high, low))
  | {msg:$A.cells}{at,t:nat | 16 <= t}
    {back3_high,back3_low,back8_high,back8_low,back14_high,back14_low,back16_high,back16_low:nat}
    {x1_high,x1_low,x2_high,x2_low,x3_high,x3_low,high,low:nat}
    SCHEDULE_sha1(sha1_kind(), msg, at, t, high, low) of (
      SCHEDULE(sha1_kind(), msg, at, t-3, back3_high, back3_low),
      SCHEDULE(sha1_kind(), msg, at, t-8, back8_high, back8_low),
      SCHEDULE(sha1_kind(), msg, at, t-14, back14_high, back14_low),
      SCHEDULE(sha1_kind(), msg, at, t-16, back16_high, back16_low),
      $AR.XOR(back3_high, back8_high, x1_high), $AR.XOR(back3_low, back8_low, x1_low),
      $AR.XOR(x1_high, back14_high, x2_high), $AR.XOR(x1_low, back14_low, x2_low),
      $AR.XOR(x2_high, back16_high, x3_high), $AR.XOR(x2_low, back16_low, x3_low),
      $AR.ROTR(31, x3_high, x3_low, high, low))

(* SCHEDULE_ARRAY(kind, words, msg, at, count): the first count words of
   the array whose cells are `words`, at 4 * t, are W_0 to W_count-1 of
   the block *)
#pub dataprop SCHEDULE_ARRAY(schedule_kind, $A.cells, $A.cells, int, int) =
  | {kind:schedule_kind}{words,msg:$A.cells}{at:nat}
    SCHEDULE_ARRAY_nil(kind, words, msg, at, 0)
  | {kind:schedule_kind}{words,msg:$A.cells}{at,count:nat}{high,low:nat}
    SCHEDULE_ARRAY_cons(kind, words, msg, at, count + 1) of (
      SCHEDULE_ARRAY(kind, words, msg, at, count),
      WORD_AT(words, 4*count, high, low),
      SCHEDULE(kind, msg, at, count, high, low))

(* Word i of the first count words of the array, and what the standard
   says it is *)
#pub prfun schedule_array_get {kind:schedule_kind}{words,msg:$A.cells}{at,count,i:nat | i < count}
  (SCHEDULE_ARRAY(kind, words, msg, at, count))
  : [high,low:nat] (WORD_AT(words, 4*i, high, low), SCHEDULE(kind, msg, at, i, high, low))

primplement schedule_array_get {kind}{words,msg}{at,count,i} (listed) =
  case+ listed of
  | SCHEDULE_ARRAY_cons(rest, word, specified) =>
      sif i == count - 1 then (word, specified)
      else schedule_array_get{kind}{words,msg}{at,count-1,i}(rest)

(* Setting a word beyond the first count leaves the first count as they were *)
#pub prfun schedule_array_frame {kind:schedule_kind}{words,words2,msg:$A.cells}{at,count,set_at,high,low:nat | 4*count <= set_at}
  (WORD_SET(words, set_at, high, low, words2), SCHEDULE_ARRAY(kind, words, msg, at, count))
  : SCHEDULE_ARRAY(kind, words2, msg, at, count)

primplement schedule_array_frame {kind}{words,words2,msg}{at,count,set_at,high,low} (set, listed) =
  case+ listed of
  | SCHEDULE_ARRAY_nil() => SCHEDULE_ARRAY_nil()
  | SCHEDULE_ARRAY_cons(rest, word, specified) =>
      SCHEDULE_ARRAY_cons(schedule_array_frame{kind}{words,words2,msg}{at,count-1,set_at,high,low}(set, rest),
                          word_set_other(set, word), specified)

(* Words 0 to 15 of the array are the block's own words *)
fun _schedule_load {kind:schedule_kind}{lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}
  {lw:agz}{nw:nat | 64 <= nw}{words:$A.cells}{t:nat | t <= 16} .<16 - t>.
  (message: !$A.barr(lm, nm, msg), at: int at, array: $A.barr(lw, nw, words), t: int t,
   loaded: SCHEDULE_ARRAY(kind, words, msg, at, t))
  : [words2:$A.cells] (SCHEDULE_ARRAY(kind, words2, msg, at, 16) | $A.barr(lw, nw, words2)) =
  if t >= 16 then (loaded | array)
  else let
    val (read | @(high, low)) = word_get(message, at + 4 * t)
    val (set | array) = word_set(array, 4 * t, high, low)
    prval kept = schedule_array_frame(set, loaded)
  in _schedule_load(message, at, array, t + 1,
       SCHEDULE_ARRAY_cons(kept, word_set_at(set), SCHEDULE_message(read))) end

(* Word i of the array read and tied to the standard's W_i *)
fn _scheduled {kind:schedule_kind}{lw:agz}{nw:nat}{words,msg:$A.cells}{at,count,i:nat | i < count; 4*i + 3 < nw}
  (array: !$A.barr(lw, nw, words), listed: SCHEDULE_ARRAY(kind, words, msg, at, count), i: int i)
  : [high,low:nat | high < 65536; low < 65536] (SCHEDULE(kind, msg, at, i, high, low) | @(int high, int low)) = let
  val (read | @(high, low)) = word_get(array, 4 * i)
  prval @(known, specified) = schedule_array_get{kind}{words,msg}{at,count,i}(listed)
  prval () = word_at_functional(read, known)
in (specified | @(high, low)) end

(* W_t for t from 16 to 63 of SHA-256, each from the earlier ones *)
fun _schedule_sha256_expand {lw:agz}{words:$A.cells}{msg:$A.cells}{at:nat}{t:nat | 16 <= t; t <= 64} .<64 - t>.
  (array: $A.barr(lw, 256, words), t: int t,
   listed: SCHEDULE_ARRAY(sha256_kind(), words, msg, at, t))
  : [words2:$A.cells] (SCHEDULE_ARRAY(sha256_kind(), words2, msg, at, 64) | $A.barr(lw, 256, words2)) =
  if t >= 64 then (listed | array)
  else let
    val (back2 | @(back2_high, back2_low)) = _scheduled(array, listed, t - 2)
    val (back7 | @(back7_high, back7_low)) = _scheduled(array, listed, t - 7)
    val (back15 | @(back15_high, back15_low)) = _scheduled(array, listed, t - 15)
    val (back16 | @(back16_high, back16_low)) = _scheduled(array, listed, t - 16)
    val (sigma1 | @(s1_high, s1_low)) = small_sigma_1(back2_high, back2_low)
    val (sigma0 | @(s0_high, s0_low)) = small_sigma_0(back15_high, back15_low)
    val (add1 | @(sum1_high, sum1_low)) = $AR.add32(s1_high, s1_low, back7_high, back7_low)
    val (add2 | @(sum2_high, sum2_low)) = $AR.add32(sum1_high, sum1_low, s0_high, s0_low)
    val (add3 | @(high, low)) = $AR.add32(sum2_high, sum2_low, back16_high, back16_low)
    val (set | array) = word_set(array, 4 * t, high, low)
    prval kept = schedule_array_frame(set, listed)
    prval specified = SCHEDULE_sha256(back2, back7, back15, back16, sigma1, sigma0, add1, add2, add3)
  in _schedule_sha256_expand(array, t + 1,
       SCHEDULE_ARRAY_cons(kept, word_set_at(set), specified)) end

(* W_t for t from 16 to 79 of SHA-1, each from the earlier ones *)
fun _schedule_sha1_expand {lw:agz}{words:$A.cells}{msg:$A.cells}{at:nat}{t:nat | 16 <= t; t <= 80} .<80 - t>.
  (array: $A.barr(lw, 320, words), t: int t,
   listed: SCHEDULE_ARRAY(sha1_kind(), words, msg, at, t))
  : [words2:$A.cells] (SCHEDULE_ARRAY(sha1_kind(), words2, msg, at, 80) | $A.barr(lw, 320, words2)) =
  if t >= 80 then (listed | array)
  else let
    val (back3 | @(back3_high, back3_low)) = _scheduled(array, listed, t - 3)
    val (back8 | @(back8_high, back8_low)) = _scheduled(array, listed, t - 8)
    val (back14 | @(back14_high, back14_low)) = _scheduled(array, listed, t - 14)
    val (back16 | @(back16_high, back16_low)) = _scheduled(array, listed, t - 16)
    val (xor1_high, xor1_low | @(x1_high, x1_low)) = $AR.xor32(back3_high, back3_low, back8_high, back8_low)
    val (xor2_high, xor2_low | @(x2_high, x2_low)) = $AR.xor32(x1_high, x1_low, back14_high, back14_low)
    val (xor3_high, xor3_low | @(x3_high, x3_low)) = $AR.xor32(x2_high, x2_low, back16_high, back16_low)
    val (turned | @(high, low)) = $AR.rotr_fast(31, x3_high, x3_low)
    val (set | array) = word_set(array, 4 * t, high, low)
    prval kept = schedule_array_frame(set, listed)
    prval specified = SCHEDULE_sha1(back3, back8, back14, back16, xor1_high, xor1_low, xor2_high, xor2_low, xor3_high, xor3_low, turned)
  in _schedule_sha1_expand(array, t + 1,
       SCHEDULE_ARRAY_cons(kept, word_set_at(set), specified)) end

(* The 64 words of SHA-256's message schedule of the block of 64 bytes
   from `at` of the message, in the array at 4 * t, with the proof that
   each is the standard's W_t *)
#pub fun schedule_sha256 {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}{lw:agz}{words:$A.cells}
  (message: !$A.barr(lm, nm, msg), at: int at, array: $A.barr(lw, 256, words))
  : [words2:$A.cells] (SCHEDULE_ARRAY(sha256_kind(), words2, msg, at, 64) | $A.barr(lw, 256, words2))

implement schedule_sha256 {lm}{nm}{msg}{at}{lw}{words} (message, at, array) = let
  val (loaded | array) = _schedule_load{sha256_kind()}(message, at, array, 0, SCHEDULE_ARRAY_nil())
in _schedule_sha256_expand(array, 16, loaded) end

(* The 80 words of SHA-1's message schedule, likewise *)
#pub fun schedule_sha1 {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}{lw:agz}{words:$A.cells}
  (message: !$A.barr(lm, nm, msg), at: int at, array: $A.barr(lw, 320, words))
  : [words2:$A.cells] (SCHEDULE_ARRAY(sha1_kind(), words2, msg, at, 80) | $A.barr(lw, 320, words2))

implement schedule_sha1 {lm}{nm}{msg}{at}{lw}{words} (message, at, array) = let
  val (loaded | array) = _schedule_load{sha1_kind()}(message, at, array, 0, SCHEDULE_ARRAY_nil())
in _schedule_sha1_expand(array, 16, loaded) end

(* ============================================================
   The round constants, the rounds and the block's chaining add
   (FIPS 180-4, sections 4.2.2, 5.3.3 and 6.2.2 steps 2 to 4 for SHA-256;
   4.1.1, 4.2.1, 5.3.1 and 6.1.2 steps 2 to 4 for SHA-1), proved against
   the standard (bats-lang/sha256#29, stage C)

   The state of the rounds is eight words (SHA-1: five), each a word as its
   two 16-bit halves. `word` is the sort of a word, w32(high, low), and
   `eight_words` and `five_words` those of the states, so a relation between
   states names every word of both, and the register shifts of a round are
   in the indices: the state after a round of SHA-256 is
   eight(new a, a, b, c, new e, e, f, g).
   ============================================================ *)

#pub datasort word = | w32 of (int, int)

#pub datasort eight_words =
  | eight of (word, word, word, word, word, word, word, word)

#pub datasort five_words = | five of (word, word, word, word, word)

(* The words of a state in an array: EIGHT_AT(cs, at, s) says the 32 cells
   from `at` of cs are the eight words of s, in order, big endian (the
   chaining value H of SHA-256 is kept so); FIVE_AT the 20 cells of SHA-1's *)
#pub dataprop EIGHT_AT($A.cells, int, eight_words) =
  | {cs:$A.cells}{at:nat}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat}
    EIGHT_AT_mk(cs, at, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low))) of (
      WORD_AT(cs, at + 0, h0_high, h0_low),
      WORD_AT(cs, at + 4, h1_high, h1_low),
      WORD_AT(cs, at + 8, h2_high, h2_low),
      WORD_AT(cs, at + 12, h3_high, h3_low),
      WORD_AT(cs, at + 16, h4_high, h4_low),
      WORD_AT(cs, at + 20, h5_high, h5_low),
      WORD_AT(cs, at + 24, h6_high, h6_low),
      WORD_AT(cs, at + 28, h7_high, h7_low))

#pub dataprop FIVE_AT($A.cells, int, five_words) =
  | {cs:$A.cells}{at:nat}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat}
    FIVE_AT_mk(cs, at, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low))) of (
      WORD_AT(cs, at + 0, h0_high, h0_low),
      WORD_AT(cs, at + 4, h1_high, h1_low),
      WORD_AT(cs, at + 8, h2_high, h2_low),
      WORD_AT(cs, at + 12, h3_high, h3_low),
      WORD_AT(cs, at + 16, h4_high, h4_low))

(* The 8 words of a state at `at`, read from the array; the proof says what
   they are, and the values returned are those the proof names *)
#pub fun eight_get {lc:agz}{n,at:nat | at + 31 < n}{cs:$A.cells}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536; h5_high < 65536; h5_low < 65536; h6_high < 65536; h6_low < 65536; h7_high < 65536; h7_low < 65536}
  (cells: !$A.barr(lc, n, cs), at: int at,
   have: EIGHT_AT(cs, at, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low))))
  : @(int h0_high, int h0_low, int h1_high, int h1_low, int h2_high, int h2_low, int h3_high, int h3_low, int h4_high, int h4_low, int h5_high, int h5_low, int h6_high, int h6_low, int h7_high, int h7_low)

implement eight_get {lc}{n,at}{cs}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low} (cells, at, have) = let
  prval EIGHT_AT_mk(known0, known1, known2, known3, known4, known5, known6, known7) = have
  val (read0 | @(read0_high, read0_low)) = word_get(cells, at + 0)
  prval () = word_at_functional(read0, known0)
  val (read1 | @(read1_high, read1_low)) = word_get(cells, at + 4)
  prval () = word_at_functional(read1, known1)
  val (read2 | @(read2_high, read2_low)) = word_get(cells, at + 8)
  prval () = word_at_functional(read2, known2)
  val (read3 | @(read3_high, read3_low)) = word_get(cells, at + 12)
  prval () = word_at_functional(read3, known3)
  val (read4 | @(read4_high, read4_low)) = word_get(cells, at + 16)
  prval () = word_at_functional(read4, known4)
  val (read5 | @(read5_high, read5_low)) = word_get(cells, at + 20)
  prval () = word_at_functional(read5, known5)
  val (read6 | @(read6_high, read6_low)) = word_get(cells, at + 24)
  prval () = word_at_functional(read6, known6)
  val (read7 | @(read7_high, read7_low)) = word_get(cells, at + 28)
  prval () = word_at_functional(read7, known7)
in @(read0_high, read0_low, read1_high, read1_low, read2_high, read2_low, read3_high, read3_low, read4_high, read4_low, read5_high, read5_low, read6_high, read6_low, read7_high, read7_low) end

(* The 8 words written at `at`, with the proof that they are there *)
#pub fun eight_set {lc:agz}{n,at:nat | at + 31 < n}{cs:$A.cells}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536; h5_high < 65536; h5_low < 65536; h6_high < 65536; h6_low < 65536; h7_high < 65536; h7_low < 65536}
  (cells: $A.barr(lc, n, cs), at: int at, h0_high: int h0_high, h0_low: int h0_low, h1_high: int h1_high, h1_low: int h1_low, h2_high: int h2_high, h2_low: int h2_low, h3_high: int h3_high, h3_low: int h3_low, h4_high: int h4_high, h4_low: int h4_low, h5_high: int h5_high, h5_low: int h5_low, h6_high: int h6_high, h6_low: int h6_low, h7_high: int h7_high, h7_low: int h7_low)
  : [cs2:$A.cells] (EIGHT_AT(cs2, at, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low))) | $A.barr(lc, n, cs2))

implement eight_set {lc}{n,at}{cs}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low} (cells, at, h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low, h5_high, h5_low, h6_high, h6_low, h7_high, h7_low) = let
  val (set0 | cells) = word_set(cells, at + 0, h0_high, h0_low)
  val (set1 | cells) = word_set(cells, at + 4, h1_high, h1_low)
  val (set2 | cells) = word_set(cells, at + 8, h2_high, h2_low)
  val (set3 | cells) = word_set(cells, at + 12, h3_high, h3_low)
  val (set4 | cells) = word_set(cells, at + 16, h4_high, h4_low)
  val (set5 | cells) = word_set(cells, at + 20, h5_high, h5_low)
  val (set6 | cells) = word_set(cells, at + 24, h6_high, h6_low)
  val (set7 | cells) = word_set(cells, at + 28, h7_high, h7_low)
  prval stored0 = word_set_other(set7, word_set_other(set6, word_set_other(set5, word_set_other(set4, word_set_other(set3, word_set_other(set2, word_set_other(set1, word_set_at(set0))))))))
  prval stored1 = word_set_other(set7, word_set_other(set6, word_set_other(set5, word_set_other(set4, word_set_other(set3, word_set_other(set2, word_set_at(set1)))))))
  prval stored2 = word_set_other(set7, word_set_other(set6, word_set_other(set5, word_set_other(set4, word_set_other(set3, word_set_at(set2))))))
  prval stored3 = word_set_other(set7, word_set_other(set6, word_set_other(set5, word_set_other(set4, word_set_at(set3)))))
  prval stored4 = word_set_other(set7, word_set_other(set6, word_set_other(set5, word_set_at(set4))))
  prval stored5 = word_set_other(set7, word_set_other(set6, word_set_at(set5)))
  prval stored6 = word_set_other(set7, word_set_at(set6))
  prval stored7 = word_set_at(set7)
in (EIGHT_AT_mk(stored0, stored1, stored2, stored3, stored4, stored5, stored6, stored7) | cells) end

(* The 5 words of a state at `at`, read from the array; the proof says what
   they are, and the values returned are those the proof names *)
#pub fun five_get {lc:agz}{n,at:nat | at + 19 < n}{cs:$A.cells}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536}
  (cells: !$A.barr(lc, n, cs), at: int at,
   have: FIVE_AT(cs, at, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low))))
  : @(int h0_high, int h0_low, int h1_high, int h1_low, int h2_high, int h2_low, int h3_high, int h3_low, int h4_high, int h4_low)

implement five_get {lc}{n,at}{cs}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low} (cells, at, have) = let
  prval FIVE_AT_mk(known0, known1, known2, known3, known4) = have
  val (read0 | @(read0_high, read0_low)) = word_get(cells, at + 0)
  prval () = word_at_functional(read0, known0)
  val (read1 | @(read1_high, read1_low)) = word_get(cells, at + 4)
  prval () = word_at_functional(read1, known1)
  val (read2 | @(read2_high, read2_low)) = word_get(cells, at + 8)
  prval () = word_at_functional(read2, known2)
  val (read3 | @(read3_high, read3_low)) = word_get(cells, at + 12)
  prval () = word_at_functional(read3, known3)
  val (read4 | @(read4_high, read4_low)) = word_get(cells, at + 16)
  prval () = word_at_functional(read4, known4)
in @(read0_high, read0_low, read1_high, read1_low, read2_high, read2_low, read3_high, read3_low, read4_high, read4_low) end

(* The 5 words written at `at`, with the proof that they are there *)
#pub fun five_set {lc:agz}{n,at:nat | at + 19 < n}{cs:$A.cells}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536}
  (cells: $A.barr(lc, n, cs), at: int at, h0_high: int h0_high, h0_low: int h0_low, h1_high: int h1_high, h1_low: int h1_low, h2_high: int h2_high, h2_low: int h2_low, h3_high: int h3_high, h3_low: int h3_low, h4_high: int h4_high, h4_low: int h4_low)
  : [cs2:$A.cells] (FIVE_AT(cs2, at, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low))) | $A.barr(lc, n, cs2))

implement five_set {lc}{n,at}{cs}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low} (cells, at, h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low) = let
  val (set0 | cells) = word_set(cells, at + 0, h0_high, h0_low)
  val (set1 | cells) = word_set(cells, at + 4, h1_high, h1_low)
  val (set2 | cells) = word_set(cells, at + 8, h2_high, h2_low)
  val (set3 | cells) = word_set(cells, at + 12, h3_high, h3_low)
  val (set4 | cells) = word_set(cells, at + 16, h4_high, h4_low)
  prval stored0 = word_set_other(set4, word_set_other(set3, word_set_other(set2, word_set_other(set1, word_set_at(set0)))))
  prval stored1 = word_set_other(set4, word_set_other(set3, word_set_other(set2, word_set_at(set1))))
  prval stored2 = word_set_other(set4, word_set_other(set3, word_set_at(set2)))
  prval stored3 = word_set_other(set4, word_set_at(set3))
  prval stored4 = word_set_at(set4)
in (FIVE_AT_mk(stored0, stored1, stored2, stored3, stored4) | cells) end

(* BEGIN generated by scripts/gen-roots.py *)

(* LIMB_SQUARE(x0, x1, x2, s0, ..., s5): s is x * x. A number is its limbs of
   12 bits, least significant first (4096 = 2 to the 12), so that a product of
   two limbs is under 2 to the 24 and every equation below stays far under the
   solver's 2 to the 29: x0 + 4096 * x1 + 4096^2 * x2 is x. Each constructor
   writes the schoolbook product column by column: the column's products and
   the carry in are its limb and 4096 times the carry out (a witness the
   caller gives); the carry out of the last column is the top limb. *)
#pub dataprop LIMB_SQUARE(int,int,int,int,int,int,int,int,int) =
  | {x0,x1,x2,s0,s1,s2,s3,s4,s5,c0,c1,c2,c3:nat | x0 < 4096; x1 < 4096; x2 < 4096; s0 < 4096; s1 < 4096; s2 < 4096; s3 < 4096; s4 < 4096; s5 < 4096;
      x0*x0 == s0 + 4096*c0;
      x0*x1 + x1*x0 + c0 == s1 + 4096*c1;
      x0*x2 + x1*x1 + x2*x0 + c1 == s2 + 4096*c2;
      x1*x2 + x2*x1 + c2 == s3 + 4096*c3;
      x2*x2 + c3 == s4 + 4096*s5}
    LIMB_SQUARE_mk(x0,x1,x2,s0,s1,s2,s3,s4,s5)

(* LIMB_MULTIPLY(s0, ..., s5, x0, x1, x2, y0, ..., y8): y is s * x *)
#pub dataprop LIMB_MULTIPLY(int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int) =
  | {s0,s1,s2,s3,s4,s5,x0,x1,x2,y0,y1,y2,y3,y4,y5,y6,y7,y8,c0,c1,c2,c3,c4,c5,c6:nat | s0 < 4096; s1 < 4096; s2 < 4096; s3 < 4096; s4 < 4096; s5 < 4096; x0 < 4096; x1 < 4096; x2 < 4096; y0 < 4096; y1 < 4096; y2 < 4096; y3 < 4096; y4 < 4096; y5 < 4096; y6 < 4096; y7 < 4096; y8 < 4096;
      s0*x0 == y0 + 4096*c0;
      s0*x1 + s1*x0 + c0 == y1 + 4096*c1;
      s0*x2 + s1*x1 + s2*x0 + c1 == y2 + 4096*c2;
      s1*x2 + s2*x1 + s3*x0 + c2 == y3 + 4096*c3;
      s2*x2 + s3*x1 + s4*x0 + c3 == y4 + 4096*c4;
      s3*x2 + s4*x1 + s5*x0 + c4 == y5 + 4096*c5;
      s4*x2 + s5*x1 + c5 == y6 + 4096*c6;
      s5*x2 + c6 == y7 + 4096*y8}
    LIMB_MULTIPLY_mk(s0,s1,s2,s3,s4,s5,x0,x1,x2,y0,y1,y2,y3,y4,y5,y6,y7,y8)

(* LIMB_CUBE(x0, x1, x2, y0, ..., y8): y is x * x * x *)
#pub dataprop LIMB_CUBE(int,int,int,int,int,int,int,int,int,int,int,int) =
  | {x0,x1,x2,s0,s1,s2,s3,s4,s5,y0,y1,y2,y3,y4,y5,y6,y7,y8:nat}
    LIMB_CUBE_mk(x0,x1,x2,y0,y1,y2,y3,y4,y5,y6,y7,y8) of (
      LIMB_SQUARE(x0,x1,x2,s0,s1,s2,s3,s4,s5),
      LIMB_MULTIPLY(s0,s1,s2,s3,s4,s5,x0,x1,x2,y0,y1,y2,y3,y4,y5,y6,y7,y8))

(* LIMB_ADD(a0, ..., a8, b0, ..., b8, carry_in, c0, ..., c8): c is a + b +
   carry_in, of 9 limbs with no carry out of the last (k8 is 0) *)
#pub dataprop LIMB_ADD(int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int) =
  | {a0,a1,a2,a3,a4,a5,a6,a7,a8,b0,b1,b2,b3,b4,b5,b6,b7,b8,c0,c1,c2,c3,c4,c5,c6,c7,c8,k0,k1,k2,k3,k4,k5,k6,k7,k8,carry_in:nat | carry_in <= 1;
      a0 < 4096; a1 < 4096; a2 < 4096; a3 < 4096; a4 < 4096; a5 < 4096; a6 < 4096; a7 < 4096; a8 < 4096; b0 < 4096; b1 < 4096; b2 < 4096; b3 < 4096; b4 < 4096; b5 < 4096; b6 < 4096; b7 < 4096; b8 < 4096; c0 < 4096; c1 < 4096; c2 < 4096; c3 < 4096; c4 < 4096; c5 < 4096; c6 < 4096; c7 < 4096; c8 < 4096;
      a0 + b0 + carry_in == c0 + 4096*k0;
      a1 + b1 + k0 == c1 + 4096*k1;
      a2 + b2 + k1 == c2 + 4096*k2;
      a3 + b3 + k2 == c3 + 4096*k3;
      a4 + b4 + k3 == c4 + 4096*k4;
      a5 + b5 + k4 == c5 + 4096*k5;
      a6 + b6 + k5 == c6 + 4096*k6;
      a7 + b7 + k6 == c7 + 4096*k7;
      a8 + b8 + k7 == c8 + 4096*k8; k8 == 0}
    LIMB_ADD_mk(a0,a1,a2,a3,a4,a5,a6,a7,a8,b0,b1,b2,b3,b4,b5,b6,b7,b8,carry_in,c0,c1,c2,c3,c4,c5,c6,c7,c8)

(* CUBE_ROOT_FRAC32(p, high, low): high:low (two 16-bit halves) is the first
   32 bits of the fractional part of the cube root of p, FIPS 180-4's
   definition of SHA-256's constants: with x = floor(cbrt(p) * 2 to the 32) =
   q * 2 to the 32 + high * 2 to the 16 + low (the root's integer part q is
   the part over 32 bits), x^3 <= p * 2 to the 96 < (x + 1)^3. The relation
   says x^3 + d = p * 2 to the 96 (d, a natural number, is the difference) and
   (x + 1)^3 = p * 2 to the 96 + e + 1; p * 2 to the 96 is the limb p after 8
   zero limbs. The first line of guards ties the limbs of x to high and low. *)
#pub dataprop CUBE_ROOT_FRAC32(int,int,int) =
  | {p,high,low,r,u,v,q,x0,x1,x2,xp0,xp1,xp2,y0,y1,y2,y3,y4,y5,y6,y7,y8,d0,d1,d2,d3,d4,d5,d6,d7,d8,z0,z1,z2,z3,z4,z5,z6,z7,z8,e0,e1,e2,e3,e4,e5,e6,e7,e8:nat | p < 4096; high < 65536; low < 65536;
      x0 < 4096; x1 < 4096; x2 < 4096; xp0 < 4096; xp1 < 4096; xp2 < 4096; y0 < 4096; y1 < 4096; y2 < 4096; y3 < 4096; y4 < 4096; y5 < 4096; y6 < 4096; y7 < 4096; y8 < 4096; d0 < 4096; d1 < 4096; d2 < 4096; d3 < 4096; d4 < 4096; d5 < 4096; d6 < 4096; d7 < 4096; d8 < 4096; z0 < 4096; z1 < 4096; z2 < 4096; z3 < 4096; z4 < 4096; z5 < 4096; z6 < 4096; z7 < 4096; z8 < 4096; e0 < 4096; e1 < 4096; e2 < 4096; e3 < 4096; e4 < 4096; e5 < 4096; e6 < 4096; e7 < 4096; e8 < 4096;
      x0 + 4096*r == low; x1 == r + 16*u; u + 256*v == high; x2 == v + 256*q}
    CUBE_ROOT_FRAC32_mk(p,high,low) of (
      LIMB_CUBE(x0,x1,x2,y0,y1,y2,y3,y4,y5,y6,y7,y8),
      LIMB_ADD(y0,y1,y2,y3,y4,y5,y6,y7,y8,d0,d1,d2,d3,d4,d5,d6,d7,d8,0,0,0,0,0,0,0,0,0,p),
      LIMB_ADD(x0,x1,x2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,xp0,xp1,xp2,0,0,0,0,0,0),
      LIMB_CUBE(xp0,xp1,xp2,z0,z1,z2,z3,z4,z5,z6,z7,z8),
      LIMB_ADD(0,0,0,0,0,0,0,0,p,e0,e1,e2,e3,e4,e5,e6,e7,e8,1,z0,z1,z2,z3,z4,z5,z6,z7,z8))

(* SQUARE_ROOT_FRAC30(n, high, low): high:low (two 16-bit halves) is the
   integer part of 2 to the 30 times the square root of n, FIPS 180-4's
   definition of SHA-1's constants: with y = high * 2 to the 16 + low,
   y^2 <= n * 2 to the 60 < (y + 1)^2 (n * 2 to the 60 is the limb n after 5
   zero limbs). Written like CUBE_ROOT_FRAC32 on the 6 low limbs of LIMB_ADD. *)
#pub dataprop SQUARE_ROOT_FRAC30(int,int,int) =
  | {n,high,low,r,u,y0,y1,y2,yp0,yp1,yp2,q0,q1,q2,q3,q4,q5,d0,d1,d2,d3,d4,d5,z0,z1,z2,z3,z4,z5,e0,e1,e2,e3,e4,e5:nat | n < 4096; high < 65536; low < 65536;
      y0 < 4096; y1 < 4096; y2 < 4096; yp0 < 4096; yp1 < 4096; yp2 < 4096; q0 < 4096; q1 < 4096; q2 < 4096; q3 < 4096; q4 < 4096; q5 < 4096; d0 < 4096; d1 < 4096; d2 < 4096; d3 < 4096; d4 < 4096; d5 < 4096; z0 < 4096; z1 < 4096; z2 < 4096; z3 < 4096; z4 < 4096; z5 < 4096; e0 < 4096; e1 < 4096; e2 < 4096; e3 < 4096; e4 < 4096; e5 < 4096;
      y0 + 4096*r == low; y1 == r + 16*u; u + 256*y2 == high}
    SQUARE_ROOT_FRAC30_mk(n,high,low) of (
      LIMB_SQUARE(y0,y1,y2,q0,q1,q2,q3,q4,q5),
      LIMB_ADD(q0,q1,q2,q3,q4,q5,0,0,0,d0,d1,d2,d3,d4,d5,0,0,0,0,0,0,0,0,0,n,0,0,0),
      LIMB_ADD(y0,y1,y2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,yp0,yp1,yp2,0,0,0,0,0,0),
      LIMB_SQUARE(yp0,yp1,yp2,z0,z1,z2,z3,z4,z5),
      LIMB_ADD(0,0,0,0,0,n,0,0,0,e0,e1,e2,e3,e4,e5,0,0,0,1,z0,z1,z2,z3,z4,z5,0,0,0))

(* The proofs of the constants: each is the proof of its table entry's word
   (the annotation says which), written out by scripts/gen-roots.py with the
   carries of the schoolbook products as the constructors' arguments. *)
prfn cube_root_of_2 (): CUBE_ROOT_FRAC32(2, 0x428a, 0x2f98) =
  CUBE_ROOT_FRAC32_mk{2,17034,12184,2,138,66,1,3992,2210,322,3993,2210,322,1536,813,1267,2502,3934,4031,4095,4095,1,2560,3282,2828,1593,161,64,0,0,0,905,4046,3556,1461,638,12,0,0,2,904,4046,3556,1461,638,12,0,0,0}(
    LIMB_CUBE_mk{3992,2210,322,2624,2962,440,3749,1631,25,1536,813,1267,2502,3934,4031,4095,4095,1}(LIMB_SQUARE_mk{3992,2210,322,2624,2962,440,3749,1631,25,3890,4308,1821,347}(), LIMB_MULTIPLY_mk{2624,2962,440,3749,1631,25,3992,2210,322,1536,813,1267,2502,3934,4031,4095,4095,1,2557,4303,2234,4124,3647,1199,141}()),
    LIMB_ADD_mk{1536,813,1267,2502,3934,4031,4095,4095,1,2560,3282,2828,1593,161,64,0,0,0,0,0,0,0,0,0,0,0,2,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3992,2210,322,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3993,2210,322,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3993,2210,322,2417,3288,1085,3749,1631,25,905,4046,3556,1461,638,12,0,0,2}(LIMB_SQUARE_mk{3993,2210,322,2417,3288,1085,3749,1631,25,3892,4309,1821,347}(), LIMB_MULTIPLY_mk{2417,3288,1085,3749,1631,25,3993,2210,322,905,4046,3556,1461,638,12,0,0,2,2356,4509,3022,4499,3699,1200,142}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,2,904,4046,3556,1461,638,12,0,0,0,905,4046,3556,1461,638,12,0,0,2,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_3 (): CUBE_ROOT_FRAC32(3, 0x7137, 0x4491) =
  CUBE_ROOT_FRAC32_mk{3,28983,17553,4,55,113,1,1169,884,369,1170,884,369,177,349,1533,1823,4033,4081,4095,4095,2,3919,3746,2562,2272,62,14,0,0,0,3272,3034,1008,2316,3394,85,0,0,3,3271,3034,1008,2316,3394,85,0,0,0}(
    LIMB_CUBE_mk{1169,884,369,2593,2741,2186,1529,1152,33,177,349,1533,1823,4033,4081,4095,4095,2}(LIMB_SQUARE_mk{1169,884,369,2593,2741,2186,1529,1152,33,333,504,401,159}(), LIMB_MULTIPLY_mk{2593,2741,2186,1529,1152,33,1169,884,369,177,349,1533,1823,4033,4081,4095,4095,2,740,1342,1449,1155,855,395,110}()),
    LIMB_ADD_mk{177,349,1533,1823,4033,4081,4095,4095,2,3919,3746,2562,2272,62,14,0,0,0,0,0,0,0,0,0,0,0,3,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1169,884,369,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1170,884,369,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1170,884,369,836,414,2925,1529,1152,33,3272,3034,1008,2316,3394,85,0,0,3}(LIMB_SQUARE_mk{1170,884,369,836,414,2925,1529,1152,33,334,505,401,159}(), LIMB_MULTIPLY_mk{836,414,2925,1529,1152,33,1170,884,369,3272,3034,1008,2316,3394,85,0,0,3,238,298,1000,1105,922,396,111}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,3,3271,3034,1008,2316,3394,85,0,0,0,3272,3034,1008,2316,3394,85,0,0,3,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_5 (): CUBE_ROOT_FRAC32(5, 0xb5c0, 0xfbcf) =
  CUBE_ROOT_FRAC32_mk{5,46528,64463,15,192,181,1,3023,3087,437,3024,3087,437,2159,3082,2115,642,1830,3966,4095,4095,4,1937,1013,1980,3453,2265,129,0,0,0,0,2341,3985,1786,3275,10,0,0,5,4095,2340,3985,1786,3275,10,0,0,0}(
    LIMB_CUBE_mk{3023,3087,437,353,761,2916,1746,3212,46,2159,3082,2115,642,1830,3966,4095,4095,4}(LIMB_SQUARE_mk{3023,3087,437,353,761,2916,1746,3212,46,2231,4557,2972,659}(), LIMB_MULTIPLY_mk{353,761,2916,1746,3212,46,3023,3087,437,2159,3082,2115,642,1830,3966,4095,4095,4,260,827,2763,3568,3998,2641,377}()),
    LIMB_ADD_mk{2159,3082,2115,642,1830,3966,4095,4095,4,1937,1013,1980,3453,2265,129,0,0,0,0,0,0,0,0,0,0,0,5,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3023,3087,437,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3024,3087,437,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3024,3087,437,2304,2840,3791,1746,3212,46,0,2341,3985,1786,3275,10,0,0,5}(LIMB_SQUARE_mk{3024,3087,437,2304,2840,3791,1746,3212,46,2232,4558,2972,659}(), LIMB_MULTIPLY_mk{2304,2840,3791,1746,3212,46,3024,3087,437,0,2341,3985,1786,3275,10,0,0,5,1701,3833,5185,4450,4092,2642,378}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,5,4095,2340,3985,1786,3275,10,0,0,0,0,2341,3985,1786,3275,10,0,0,5,1,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_7 (): CUBE_ROOT_FRAC32(7, 0xe9b5, 0xdba5) =
  CUBE_ROOT_FRAC32_mk{7,59829,56229,13,181,233,1,2981,2909,489,2982,2909,489,1117,271,381,3552,495,4007,4095,4095,6,2979,3824,3714,543,3600,88,0,0,0,88,2107,3395,2638,3144,86,0,0,7,87,2107,3395,2638,3144,86,0,0,0}(
    LIMB_CUBE_mk{2981,2909,489,2137,3163,3245,1060,2248,58,1117,271,381,3552,495,4007,4095,4095,6}(LIMB_SQUARE_mk{2981,2909,489,2137,3163,3245,1060,2248,58,2169,4234,2778,695}(), LIMB_MULTIPLY_mk{2137,3163,3245,1060,2248,58,2981,2909,489,1117,271,381,3552,495,4007,4095,4095,6,1555,3820,4864,3454,2777,1765,309}()),
    LIMB_ADD_mk{1117,271,381,3552,495,4007,4095,4095,6,2979,3824,3714,543,3600,88,0,0,0,0,0,0,0,0,0,0,0,7,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2981,2909,489,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2982,2909,489,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2982,2909,489,4004,790,129,1061,2248,58,88,2107,3395,2638,3144,86,0,0,7}(LIMB_SQUARE_mk{2982,2909,489,4004,790,129,1061,2248,58,2170,4236,2779,695}(), LIMB_MULTIPLY_mk{4004,790,129,1061,2248,58,2982,2909,489,88,2107,3395,2638,3144,86,0,0,7,2915,3419,1133,958,2405,1766,310}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,7,87,2107,3395,2638,3144,86,0,0,0,88,2107,3395,2638,3144,86,0,0,7,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_11 (): CUBE_ROOT_FRAC32(11, 0x3956, 0xc25b) =
  CUBE_ROOT_FRAC32_mk{11,14678,49755,12,86,57,2,603,1388,569,604,1388,569,1443,2237,2045,2122,1558,3870,4095,4095,10,2653,1858,2050,1973,2537,225,0,0,0,448,2660,3509,3596,3246,11,0,0,11,447,2660,3509,3596,3246,11,0,0,0}(
    LIMB_CUBE_mk{603,1388,569,3161,2848,4014,3221,562,79,1443,2237,2045,2122,1558,3870,4095,4095,10}(LIMB_SQUARE_mk{603,1388,569,3161,2848,4014,3221,562,79,88,408,637,385}(), LIMB_MULTIPLY_mk{3161,2848,4014,3221,562,79,603,1388,569,1443,2237,2045,2122,1558,3870,4095,4095,10,465,1490,1995,2230,1732,649,104}()),
    LIMB_ADD_mk{1443,2237,2045,2122,1558,3870,4095,4095,10,2653,1858,2050,1973,2537,225,0,0,0,0,0,0,0,0,0,0,0,11,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{603,1388,569,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,604,1388,569,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{604,1388,569,272,1529,1057,3222,562,79,448,2660,3509,3596,3246,11,0,0,11}(LIMB_SQUARE_mk{604,1388,569,272,1529,1057,3222,562,79,89,409,638,385}(), LIMB_MULTIPLY_mk{272,1529,1057,3222,562,79,604,1388,569,448,2660,3509,3596,3246,11,0,0,11,40,317,711,1045,1321,650,105}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,11,447,2660,3509,3596,3246,11,0,0,0,448,2660,3509,3596,3246,11,0,0,11,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_13 (): CUBE_ROOT_FRAC32(13, 0x59f1, 0x11f1) =
  CUBE_ROOT_FRAC32_mk{13,23025,4593,1,241,89,2,497,3857,601,498,3857,601,2257,2790,4001,2281,1257,3907,4095,4095,12,1839,1305,94,1814,2838,188,0,0,0,3400,2260,1984,3750,2818,76,0,0,13,3399,2260,1984,3750,2818,76,0,0,0}(
    LIMB_CUBE_mk{497,3857,601,1249,62,91,3220,1885,88,2257,2790,4001,2281,1257,3907,4095,4095,12}(LIMB_SQUARE_mk{497,3857,601,1249,62,91,3220,1885,88,60,936,3778,1132}(), LIMB_MULTIPLY_mk{1249,62,91,3220,1885,88,497,3857,601,2257,2790,4001,2281,1257,3907,4095,4095,12,151,1183,252,485,3274,2258,359}()),
    LIMB_ADD_mk{2257,2790,4001,2281,1257,3907,4095,4095,12,1839,1305,94,1814,2838,188,0,0,0,0,0,0,0,0,0,0,0,13,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{497,3857,601,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,498,3857,601,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{498,3857,601,2244,3680,1294,3220,1885,88,3400,2260,1984,3750,2818,76,0,0,13}(LIMB_SQUARE_mk{498,3857,601,2244,3680,1294,3220,1885,88,60,937,3778,1132}(), LIMB_MULTIPLY_mk{2244,3680,1294,3220,1885,88,498,3857,601,3400,2260,1984,3750,2818,76,0,0,13,272,2560,3952,2150,3451,2259,360}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,13,3399,2260,1984,3750,2818,76,0,0,0,3400,2260,1984,3750,2818,76,0,0,13,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_17 (): CUBE_ROOT_FRAC32(17, 0x923f, 0x82a4) =
  CUBE_ROOT_FRAC32_mk{17,37439,33444,8,63,146,2,676,1016,658,677,1016,658,3648,3354,3272,3466,3841,3878,4095,4095,16,448,741,823,629,254,217,0,0,0,349,2962,605,1963,1185,100,0,0,17,348,2962,605,1963,1185,100,0,0,0}(
    LIMB_CUBE_mk{676,1016,658,2320,1583,1183,2229,3210,105,3648,3354,3272,3466,3841,3878,4095,4095,16}(LIMB_SQUARE_mk{676,1016,658,2320,1583,1183,2229,3210,105,111,335,469,326}(), LIMB_MULTIPLY_mk{2320,1583,1183,2229,3210,105,676,1016,658,3648,3354,3272,3466,3841,3878,4095,4095,16,382,836,960,915,1272,1171,541}()),
    LIMB_ADD_mk{3648,3354,3272,3466,3841,3878,4095,4095,16,448,741,823,629,254,217,0,0,0,0,0,0,0,0,0,0,0,17,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{676,1016,658,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,677,1016,658,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{677,1016,658,3673,3615,2499,2229,3210,105,349,2962,605,1963,1185,100,0,0,17}(LIMB_SQUARE_mk{677,1016,658,3673,3615,2499,2229,3210,105,111,335,469,326}(), LIMB_MULTIPLY_mk{3673,3615,2499,2229,3210,105,677,1016,658,349,2962,605,1963,1185,100,0,0,17,607,1508,1900,1569,1485,1172,542}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,17,348,2962,605,1963,1185,100,0,0,0,349,2962,605,1963,1185,100,0,0,17,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_19 (): CUBE_ROOT_FRAC32(19, 0xab1c, 0x5ed5) =
  CUBE_ROOT_FRAC32_mk{19,43804,24277,5,28,171,2,3797,453,683,3798,453,683,3693,4035,1586,1979,1572,3804,4095,4095,18,403,60,2509,2116,2523,291,0,0,0,664,1995,2691,2739,661,50,0,0,19,663,1995,2691,2739,661,50,0,0,0}(
    LIMB_CUBE_mk{3797,453,683,3385,2961,2415,1618,3792,113,3693,4035,1586,1979,1572,3804,4095,4095,18}(LIMB_SQUARE_mk{3797,453,683,3385,2961,2415,1618,3792,113,3519,840,1316,151}(), LIMB_MULTIPLY_mk{3385,2961,2415,1618,3792,113,3797,453,683,3693,4035,1586,1979,1572,3804,4095,4095,18,3137,3119,3131,2261,4097,794,644}()),
    LIMB_ADD_mk{3693,4035,1586,1979,1572,3804,4095,4095,18,403,60,2509,2116,2523,291,0,0,0,0,0,0,0,0,0,0,0,19,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3797,453,683,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3798,453,683,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3798,453,683,2788,3869,3781,1618,3792,113,664,1995,2691,2739,661,50,0,0,19}(LIMB_SQUARE_mk{3798,453,683,2788,3869,3781,1618,3792,113,3521,840,1316,151}(), LIMB_MULTIPLY_mk{2788,3869,3781,1618,3792,113,3798,453,683,664,1995,2691,2739,661,50,0,0,19,2585,3896,4399,2564,4326,795,645}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,19,663,1995,2691,2739,661,50,0,0,0,664,1995,2691,2739,661,50,0,0,19,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_23 (): CUBE_ROOT_FRAC32(23, 0xd807, 0xaa98) =
  CUBE_ROOT_FRAC32_mk{23,55303,43672,10,7,216,2,2712,122,728,2713,122,728,1536,1553,1529,1876,3299,3848,4095,4095,22,2560,2542,2566,2219,796,247,0,0,0,1161,1836,83,1100,38,141,0,0,23,1160,1836,83,1100,38,141,0,0,0}(
    LIMB_CUBE_mk{2712,122,728,2624,4067,2885,2471,1643,129,1536,1553,1529,1876,3299,3848,4095,4095,22}(LIMB_SQUARE_mk{2712,122,728,2624,4067,2885,2471,1643,129,1795,161,967,43}(), LIMB_MULTIPLY_mk{2624,4067,2885,2471,1643,129,2712,122,728,1536,1553,1529,1876,3299,3848,4095,4095,22,1737,2771,2498,2445,1674,573,295}()),
    LIMB_ADD_mk{1536,1553,1529,1876,3299,3848,4095,4095,22,2560,2542,2566,2219,796,247,0,0,0,0,0,0,0,0,0,0,0,23,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2712,122,728,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2713,122,728,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2713,122,728,3953,216,246,2472,1643,129,1161,1836,83,1100,38,141,0,0,23}(LIMB_SQUARE_mk{2713,122,728,3953,216,246,2472,1643,129,1796,162,968,43}(), LIMB_MULTIPLY_mk{3953,216,246,2472,1643,129,2713,122,728,1161,1836,83,1100,38,141,0,0,23,2618,261,872,1683,1206,574,296}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,23,1160,1836,83,1100,38,141,0,0,0,1161,1836,83,1100,38,141,0,0,23,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_29 (): CUBE_ROOT_FRAC32(29, 0x1283, 0x5b01) =
  CUBE_ROOT_FRAC32_mk{29,4739,23297,5,131,18,3,2817,2101,786,2818,2101,786,257,2385,161,2780,425,3973,4095,4095,28,3839,1710,3934,1315,3670,122,0,0,0,1032,996,783,1159,746,330,0,0,29,1031,996,783,1159,746,330,0,0,0}(
    LIMB_CUBE_mk{2817,2101,786,1537,1531,2151,3555,106,151,257,2385,161,2780,425,3973,4095,4095,28}(LIMB_SQUARE_mk{2817,2101,786,1537,1531,2151,3555,106,151,1937,2890,2159,806}(), LIMB_MULTIPLY_mk{1537,1531,2151,3555,106,151,2817,2101,786,257,2385,161,2780,425,3973,4095,4095,28,1057,1841,2560,3842,2310,840,97}()),
    LIMB_ADD_mk{257,2385,161,2780,425,3973,4095,4095,28,3839,1710,3934,1315,3670,122,0,0,0,0,0,0,0,0,0,0,0,29,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2817,2101,786,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2818,2101,786,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2818,2101,786,3076,1638,3724,3555,106,151,1032,996,783,1159,746,330,0,0,29}(LIMB_SQUARE_mk{2818,2101,786,3076,1638,3724,3555,106,151,1938,2891,2159,806}(), LIMB_MULTIPLY_mk{3076,1638,3724,3555,106,151,2818,2101,786,1032,996,783,1159,746,330,0,0,29,2116,2705,3993,4671,2612,841,98}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,29,1031,996,783,1159,746,330,0,0,0,1032,996,783,1159,746,330,0,0,29,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_31 (): CUBE_ROOT_FRAC32(31, 0x2431, 0x85be) =
  CUBE_ROOT_FRAC32_mk{31,9265,34238,8,49,36,3,1470,792,804,1471,792,804,1272,638,1376,1899,96,3950,4095,4095,30,2824,3457,2719,2196,3999,145,0,0,0,319,2262,134,3131,2869,327,0,0,31,318,2262,134,3131,2869,327,0,0,0}(
    LIMB_CUBE_mk{1470,792,804,2308,2479,1512,410,3655,157,1272,638,1376,1899,96,3950,4095,4095,30}(LIMB_SQUARE_mk{1470,792,804,2308,2479,1512,410,3655,157,527,568,730,311}(), LIMB_MULTIPLY_mk{2308,2479,1512,410,3655,157,1470,792,804,1272,638,1376,1899,96,3950,4095,4095,30,828,1336,1475,926,1688,843,747}()),
    LIMB_ADD_mk{1272,638,1376,1899,96,3950,4095,4095,30,2824,3457,2719,2196,3999,145,0,0,0,0,0,0,0,0,0,0,0,31,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1470,792,804,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1471,792,804,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1471,792,804,1153,4064,3120,410,3655,157,319,2262,134,3131,2869,327,0,0,31}(LIMB_SQUARE_mk{1471,792,804,1153,4064,3120,410,3655,157,528,568,730,311}(), LIMB_MULTIPLY_mk{1153,4064,3120,410,3655,157,1471,792,804,319,2262,134,3131,2869,327,0,0,31,414,1682,2133,1548,2004,844,748}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,31,318,2262,134,3131,2869,327,0,0,0,319,2262,134,3131,2869,327,0,0,31,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_37 (): CUBE_ROOT_FRAC32(37, 0x550c, 0x7dc3) =
  CUBE_ROOT_FRAC32_mk{37,21772,32195,7,12,85,3,3523,199,853,3524,199,853,859,3501,394,270,1910,3650,4095,4095,36,3237,594,3701,3825,2185,445,0,0,0,1088,773,28,3280,1818,87,0,0,37,1087,773,28,3280,1818,87,0,0,0}(
    LIMB_CUBE_mk{3523,199,853,649,256,390,1003,2700,177,859,3501,394,270,1910,3650,4095,4095,36}(LIMB_SQUARE_mk{3523,199,853,649,256,390,1003,2700,177,3030,343,1477,83}(), LIMB_MULTIPLY_mk{649,256,390,1003,2700,177,3523,199,853,859,3501,394,270,1910,3650,4095,4095,36,558,251,483,935,2452,492,570}()),
    LIMB_ADD_mk{859,3501,394,270,1910,3650,4095,4095,36,3237,594,3701,3825,2185,445,0,0,0,0,0,0,0,0,0,0,0,37,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3523,199,853,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3524,199,853,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3524,199,853,3600,655,2096,1003,2700,177,1088,773,28,3280,1818,87,0,0,37}(LIMB_SQUARE_mk{3524,199,853,3600,655,2096,1003,2700,177,3031,343,1477,83}(), LIMB_MULTIPLY_mk{3600,655,2096,1003,2700,177,3524,199,853,1088,773,28,3280,1818,87,0,0,37,3097,739,2585,1101,2808,493,571}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,37,1087,773,28,3280,1818,87,0,0,0,1088,773,28,3280,1818,87,0,0,37,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_41 (): CUBE_ROOT_FRAC32(41, 0x72be, 0x5d74) =
  CUBE_ROOT_FRAC32_mk{41,29374,23924,5,190,114,3,3444,3045,882,3445,3045,882,320,972,996,3920,1663,3555,4095,4095,40,3776,3123,3099,175,2432,540,0,0,0,3917,1540,1211,3353,556,30,0,0,41,3916,1540,1211,3353,556,30,0,0,0}(
    LIMB_CUBE_mk{3444,3045,882,3216,1239,554,1176,996,190,320,972,996,3920,1663,3555,4095,4095,40}(LIMB_SQUARE_mk{3444,3045,882,3216,1239,554,1176,996,190,2895,5121,3748,1312}(), LIMB_MULTIPLY_mk{3216,1239,554,1176,996,190,3444,3045,882,320,972,996,3920,1663,3555,4095,4095,40,2704,3433,2080,1667,1831,1153,355}()),
    LIMB_ADD_mk{320,972,996,3920,1663,3555,4095,4095,40,3776,3123,3099,175,2432,540,0,0,0,0,0,0,0,0,0,0,0,41,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3444,3045,882,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3445,3045,882,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3445,3045,882,1913,3235,2319,1176,996,190,3917,1540,1211,3353,556,30,0,0,41}(LIMB_SQUARE_mk{3445,3045,882,1913,3235,2319,1176,996,190,2897,5122,3748,1312}(), LIMB_MULTIPLY_mk{1913,3235,2319,1176,996,190,3445,3045,882,3917,1540,1211,3353,556,30,0,0,41,1608,4143,4768,3410,2212,1154,356}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,41,3916,1540,1211,3353,556,30,0,0,0,3917,1540,1211,3353,556,30,0,0,41,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_43 (): CUBE_ROOT_FRAC32(43, 0x80de, 0xb1fe) =
  CUBE_ROOT_FRAC32_mk{43,32990,45566,11,222,128,3,510,3563,896,511,3563,896,2040,3461,2331,3772,73,3960,4095,4095,42,2056,634,1764,323,4022,135,0,0,0,1535,1281,1327,3245,656,453,0,0,43,1534,1281,1327,3245,656,453,0,0,0}(
    LIMB_CUBE_mk{510,3563,896,2052,1171,2864,2554,1559,196,2040,3461,2331,3772,73,3960,4095,4095,42}(LIMB_SQUARE_mk{510,3563,896,2052,1171,2864,2554,1559,196,63,887,3322,1559}(), LIMB_MULTIPLY_mk{2052,1171,2864,2554,1559,196,510,3563,896,2040,3461,2331,3772,73,3960,4095,4095,42,255,1930,1824,3065,3043,1939,511}()),
    LIMB_ADD_mk{2040,3461,2331,3772,73,3960,4095,4095,42,2056,634,1764,323,4022,135,0,0,0,0,0,0,0,0,0,0,0,43,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{510,3563,896,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,511,3563,896,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{511,3563,896,3073,105,562,2555,1559,196,1535,1281,1327,3245,656,453,0,0,43}(LIMB_SQUARE_mk{511,3563,896,3073,105,562,2555,1559,196,63,889,3323,1559}(), LIMB_MULTIPLY_mk{3073,105,562,2555,1559,196,511,3563,896,1535,1281,1327,3245,656,453,0,0,43,383,2686,834,830,2540,1940,512}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,43,1534,1281,1327,3245,656,453,0,0,0,1535,1281,1327,3245,656,453,0,0,43,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_47 (): CUBE_ROOT_FRAC32(47, 0x9bdc, 0x06a7) =
  CUBE_ROOT_FRAC32_mk{47,39900,1703,0,220,155,3,1703,3520,923,1704,3520,923,823,2944,1876,3149,3070,4003,4095,4095,46,3273,1151,2219,946,1025,92,0,0,0,2560,3725,3363,3137,3619,532,0,0,47,2559,3725,3363,3137,3619,532,0,0,0}(
    LIMB_CUBE_mk{1703,3520,923,241,836,937,1361,1548,208,823,2944,1876,3149,3070,4003,4095,4095,46}(LIMB_SQUARE_mk{1703,3520,923,241,836,937,1361,1548,208,708,2927,3793,1587}(), LIMB_MULTIPLY_mk{241,836,937,1361,1548,208,1703,3520,923,823,2944,1876,3149,3070,4003,4095,4095,46,100,554,1162,1559,2024,1723,527}()),
    LIMB_ADD_mk{823,2944,1876,3149,3070,4003,4095,4095,46,3273,1151,2219,946,1025,92,0,0,0,0,0,0,0,0,0,0,0,47,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1703,3520,923,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1704,3520,923,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1704,3520,923,3648,3780,2784,1361,1548,208,2560,3725,3363,3137,3619,532,0,0,47}(LIMB_SQUARE_mk{1704,3520,923,3648,3780,2784,1361,1548,208,708,2928,3793,1587}(), LIMB_MULTIPLY_mk{3648,3780,2784,1361,1548,208,1704,3520,923,2560,3725,3363,3137,3619,532,0,0,47,1517,4707,5229,3811,2441,1724,528}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,47,2559,3725,3363,3137,3619,532,0,0,0,2560,3725,3363,3137,3619,532,0,0,47,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_53 (): CUBE_ROOT_FRAC32(53, 0xc19b, 0xf174) =
  CUBE_ROOT_FRAC32_mk{53,49563,61812,15,155,193,3,372,2495,961,373,2495,961,320,3944,2016,651,1152,3547,4095,4095,52,3776,151,2079,3444,2943,548,0,0,0,2893,1618,2224,2657,2236,128,0,0,53,2892,1618,2224,2657,2236,128,0,0,0}(
    LIMB_CUBE_mk{372,2495,961,3216,825,1838,668,3092,225,320,3944,2016,651,1152,3547,4095,4095,52}(LIMB_SQUARE_mk{372,2495,961,3216,825,1838,668,3092,225,33,453,1694,1171}(), LIMB_MULTIPLY_mk{3216,825,1838,668,3092,225,372,2495,961,320,3944,2016,651,1152,3547,4095,4095,52,292,2033,1424,1374,1119,2060,862}()),
    LIMB_ADD_mk{320,3944,2016,651,1152,3547,4095,4095,52,3776,151,2079,3444,2943,548,0,0,0,0,0,0,0,0,0,0,0,53,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{372,2495,961,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,373,2495,961,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{373,2495,961,3961,1719,3761,668,3092,225,2893,1618,2224,2657,2236,128,0,0,53}(LIMB_SQUARE_mk{373,2495,961,3961,1719,3761,668,3092,225,33,454,1694,1171}(), LIMB_MULTIPLY_mk{3961,1719,3761,668,3092,225,373,2495,961,2893,1618,2224,2657,2236,128,0,0,53,360,2569,2319,2755,1571,2061,863}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,53,2892,1618,2224,2657,2236,128,0,0,0,2893,1618,2224,2657,2236,128,0,0,53,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_59 (): CUBE_ROOT_FRAC32(59, 0xe49b, 0x69c1) =
  CUBE_ROOT_FRAC32_mk{59,58523,27073,6,155,228,3,2497,2486,996,2498,2486,996,3393,950,2301,3787,1401,3644,4095,4095,58,703,3145,1794,308,2694,451,0,0,0,1288,1013,437,3912,3286,275,0,0,59,1287,1013,437,3912,3286,275,0,0,0}(
    LIMB_CUBE_mk{2497,2486,996,897,1630,3843,2771,1993,242,3393,950,2301,3787,1401,3644,4095,4095,58}(LIMB_SQUARE_mk{2497,2486,996,897,1630,3843,2771,1993,242,1522,3031,2723,1209}(), LIMB_MULTIPLY_mk{897,1630,3843,2771,1993,242,2497,2486,996,3393,950,2301,3787,1401,3644,4095,4095,58,546,1538,3550,4418,3832,2031,631}()),
    LIMB_ADD_mk{3393,950,2301,3787,1401,3644,4095,4095,58,703,3145,1794,308,2694,451,0,0,0,0,0,0,0,0,0,0,0,59,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2497,2486,996,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2498,2486,996,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2498,2486,996,1796,2507,1740,2772,1993,242,1288,1013,437,3912,3286,275,0,0,59}(LIMB_SQUARE_mk{2498,2486,996,1796,2507,1740,2772,1993,242,1523,3032,2724,1209}(), LIMB_MULTIPLY_mk{1796,2507,1740,2772,1993,242,2498,2486,996,1288,1013,437,3912,3286,275,0,0,59,1095,2619,3020,3356,3321,2032,632}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,59,1287,1013,437,3912,3286,275,0,0,0,1288,1013,437,3912,3286,275,0,0,59,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_61 (): CUBE_ROOT_FRAC32(61, 0xefbe, 0x4786) =
  CUBE_ROOT_FRAC32_mk{61,61374,18310,4,190,239,3,1926,3044,1007,1927,3044,1007,2776,2474,3397,672,1612,3932,4095,4095,60,1320,1621,698,3423,2483,163,0,0,0,4055,2052,1133,2919,827,580,0,0,61,4054,2052,1133,2919,827,580,0,0,0}(
    LIMB_CUBE_mk{1926,3044,1007,2596,3641,3698,2113,3834,247,2776,2474,3397,672,1612,3932,4095,4095,60}(LIMB_SQUARE_mk{1926,3044,1007,2596,3641,3698,2113,3834,247,905,2862,3209,1497}(), LIMB_MULTIPLY_mk{2596,3641,3698,2113,3834,247,1926,3044,1007,2776,2474,3397,672,1612,3932,4095,4095,60,1220,3641,5083,4638,4283,3485,1126}()),
    LIMB_ADD_mk{2776,2474,3397,672,1612,3932,4095,4095,60,1320,1621,698,3423,2483,163,0,0,0,0,0,0,0,0,0,0,0,61,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1926,3044,1007,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1927,3044,1007,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1927,3044,1007,2353,1538,1618,2114,3834,247,4055,2052,1133,2919,827,580,0,0,61}(LIMB_SQUARE_mk{1927,3044,1007,2353,1538,1618,2114,3834,247,906,2864,3210,1497}(), LIMB_MULTIPLY_mk{2353,1538,1618,2114,3834,247,1927,3044,1007,4055,2052,1133,2919,827,580,0,0,61,1106,2472,2483,2575,3773,3486,1127}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,61,4054,2052,1133,2919,827,580,0,0,0,4055,2052,1133,2919,827,580,0,0,61,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_67 (): CUBE_ROOT_FRAC32(67, 0x0fc1, 0x9dc6) =
  CUBE_ROOT_FRAC32_mk{67,4033,40390,9,193,15,4,3526,3097,1039,3527,3097,1039,3544,90,909,3428,1502,3664,4095,4095,66,552,4005,3186,667,2593,431,0,0,0,1687,2622,1321,1690,750,360,0,0,67,1686,2622,1321,1690,750,360,0,0,0}(
    LIMB_CUBE_mk{3526,3097,1039,1316,3207,3193,785,3845,263,3544,90,909,3428,1502,3664,4095,4095,66}(LIMB_SQUARE_mk{3526,3097,1039,1316,3207,3193,785,3845,263,3035,5332,4131,1572}(), LIMB_MULTIPLY_mk{1316,3207,3193,785,3845,263,3526,3097,1039,3544,90,909,3428,1502,3664,4095,4095,66,1132,3756,5508,3904,4714,3333,1174}()),
    LIMB_ADD_mk{3544,90,909,3428,1502,3664,4095,4095,66,552,4005,3186,667,2593,431,0,0,0,0,0,0,0,0,0,0,0,67,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3526,3097,1039,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3527,3097,1039,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3527,3097,1039,177,1211,1177,786,3845,263,1687,2622,1321,1690,750,360,0,0,67}(LIMB_SQUARE_mk{3527,3097,1039,177,1211,1177,786,3845,263,3037,5334,4132,1572}(), LIMB_MULTIPLY_mk{177,1211,1177,786,3845,263,3527,3097,1039,1687,2622,1321,1690,750,360,0,0,67,152,1176,1974,1874,4204,3334,1175}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,67,1686,2622,1321,1690,750,360,0,0,0,1687,2622,1321,1690,750,360,0,0,67,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_71 (): CUBE_ROOT_FRAC32(71, 0x240c, 0xa1cc) =
  CUBE_ROOT_FRAC32_mk{71,9228,41420,10,12,36,4,460,202,1060,461,202,1060,2752,3507,1567,3482,1039,3711,4095,4095,70,1344,588,2528,613,3056,384,0,0,0,4053,636,1376,2803,1145,438,0,0,71,4052,636,1376,2803,1145,438,0,0,0}(
    LIMB_CUBE_mk{460,202,1060,2704,1571,241,2504,1400,274,2752,3507,1567,3482,1039,3711,4095,4095,70}(LIMB_SQUARE_mk{460,202,1060,2704,1571,241,2504,1400,274,51,45,248,104}(), LIMB_MULTIPLY_mk{2704,1571,241,2504,1400,274,460,202,1060,2752,3507,1567,3482,1039,3711,4095,4095,70,303,309,804,699,343,747,375}()),
    LIMB_ADD_mk{2752,3507,1567,3482,1039,3711,4095,4095,70,1344,588,2528,613,3056,384,0,0,0,0,0,0,0,0,0,0,0,71,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{460,202,1060,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,461,202,1060,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{461,202,1060,3625,1975,2361,2504,1400,274,4053,636,1376,2803,1145,438,0,0,71}(LIMB_SQUARE_mk{461,202,1060,3625,1975,2361,2504,1400,274,51,45,248,104}(), LIMB_MULTIPLY_mk{3625,1975,2361,2504,1400,274,461,202,1060,4053,636,1376,2803,1145,438,0,0,71,407,401,1301,909,892,748,376}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,71,4052,636,1376,2803,1145,438,0,0,0,4053,636,1376,2803,1145,438,0,0,71,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_73 (): CUBE_ROOT_FRAC32(73, 0x2de9, 0x2c6f) =
  CUBE_ROOT_FRAC32_mk{73,11753,11375,2,233,45,4,3183,3730,1069,3184,3730,1069,591,1294,3000,1445,3978,3803,4095,4095,72,3505,2801,1095,2650,117,292,0,0,0,0,1431,785,3821,1561,546,0,0,73,4095,1430,785,3821,1561,546,0,0,0}(
    LIMB_CUBE_mk{3183,3730,1069,2081,3141,2287,791,1925,279,591,1294,3000,1445,3978,3803,4095,4095,72}(LIMB_SQUARE_mk{3183,3730,1069,2081,3141,2287,791,1925,279,2473,5797,5059,1948}(), LIMB_MULTIPLY_mk{2081,3141,2287,791,1925,279,3183,3730,1069,591,1294,3000,1445,3978,3803,4095,4095,72,1617,4336,5181,3518,2813,2176,756}()),
    LIMB_ADD_mk{591,1294,3000,1445,3978,3803,4095,4095,72,3505,2801,1095,2650,117,292,0,0,0,0,0,0,0,0,0,0,0,73,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3183,3730,1069,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3184,3730,1069,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3184,3730,1069,256,2411,331,792,1925,279,0,1431,785,3821,1561,546,0,0,73}(LIMB_SQUARE_mk{3184,3730,1069,256,2411,331,792,1925,279,2475,5799,5060,1948}(), LIMB_MULTIPLY_mk{256,2411,331,792,1925,279,3184,3730,1069,0,1431,785,3821,1561,546,0,0,73,199,2107,2520,1546,2304,2177,757}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,73,4095,1430,785,3821,1561,546,0,0,0,0,1431,785,3821,1561,546,0,0,73,1,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_79 (): CUBE_ROOT_FRAC32(79, 0x4a74, 0x84aa) =
  CUBE_ROOT_FRAC32_mk{79,19060,33962,8,116,74,4,1194,1864,1098,1195,1864,1098,1896,3002,116,1074,66,3714,4095,4095,78,2200,1093,3979,3021,4029,381,0,0,0,2067,2183,3496,1668,3109,501,0,0,79,2066,2183,3496,1668,3109,501,0,0,0}(
    LIMB_CUBE_mk{1194,1864,1098,228,3324,2758,2928,2379,294,1896,3002,116,1074,66,3714,4095,4095,78}(LIMB_SQUARE_mk{1194,1864,1098,228,3324,2758,2928,2379,294,348,1086,1488,999}(), LIMB_MULTIPLY_mk{228,3324,2758,2928,2379,294,1194,1864,1098,1896,3002,116,1074,66,3714,4095,4095,78,66,1072,2378,3000,2766,1953,771}()),
    LIMB_ADD_mk{1896,3002,116,1074,66,3714,4095,4095,78,2200,1093,3979,3021,4029,381,0,0,0,0,0,0,0,0,0,0,0,79,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1194,1864,1098,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1195,1864,1098,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1195,1864,1098,2617,2956,859,2929,2379,294,2067,2183,3496,1668,3109,501,0,0,79}(LIMB_SQUARE_mk{1195,1864,1098,2617,2956,859,2929,2379,294,348,1087,1489,999}(), LIMB_MULTIPLY_mk{2617,2956,859,2929,2379,294,1195,1864,1098,2067,2183,3496,1668,3109,501,0,0,79,763,2053,2297,2038,2257,1954,772}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,79,2066,2183,3496,1668,3109,501,0,0,0,2067,2183,3496,1668,3109,501,0,0,79,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_83 (): CUBE_ROOT_FRAC32(83, 0x5cb0, 0xa9dc) =
  CUBE_ROOT_FRAC32_mk{83,23728,43484,10,176,92,4,2524,2826,1116,2525,2826,1116,2496,3666,2690,1926,3226,3420,4095,4095,82,1600,429,1405,2169,869,675,0,0,0,1669,2364,2038,3089,472,238,0,0,83,1668,2364,2038,3089,472,238,0,0,0}(
    LIMB_CUBE_mk{2524,2826,1116,1296,835,31,3118,1812,304,2496,3666,2690,1926,3226,3420,4095,4095,82}(LIMB_SQUARE_mk{2524,2826,1116,1296,835,31,3118,1812,304,1555,3483,3326,1540}(), LIMB_MULTIPLY_mk{1296,835,31,3118,1812,304,2524,2826,1116,2496,3666,2690,1926,3226,3420,4095,4095,82,798,1408,948,2170,3276,2287,703}()),
    LIMB_ADD_mk{2496,3666,2690,1926,3226,3420,4095,4095,82,1600,429,1405,2169,869,675,0,0,0,0,0,0,0,0,0,0,0,83,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2524,2826,1116,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2525,2826,1116,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2525,2826,1116,2249,2392,2264,3118,1812,304,1669,2364,2038,3089,472,238,0,0,83}(LIMB_SQUARE_mk{2525,2826,1116,2249,2392,2264,3118,1812,304,1556,3484,3326,1540}(), LIMB_MULTIPLY_mk{2249,2392,2264,3118,1812,304,2525,2826,1116,1669,2364,2038,3089,472,238,0,0,83,1386,3026,3659,4136,3886,2288,704}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,83,1668,2364,2038,3089,472,238,0,0,0,1669,2364,2038,3089,472,238,0,0,83,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_89 (): CUBE_ROOT_FRAC32(89, 0x76f9, 0x88da) =
  CUBE_ROOT_FRAC32_mk{89,30457,35034,8,249,118,4,2266,3992,1142,2267,3992,1142,1448,2167,3093,394,489,3606,4095,4095,88,2648,1928,1002,3701,3606,489,0,0,0,3363,657,1766,3669,3886,466,0,0,89,3362,657,1766,3669,3886,466,0,0,0}(
    LIMB_CUBE_mk{2266,3992,1142,2468,965,1145,1091,3863,318,1448,2167,3093,394,489,3606,4095,4095,88}(LIMB_SQUARE_mk{2266,3992,1142,2468,965,1145,1091,3863,318,1253,4417,5155,2227}(), LIMB_MULTIPLY_mk{2468,965,1145,1091,3863,318,2266,3992,1142,1448,2167,3093,394,489,3606,4095,4095,88,1365,2939,2262,1989,3520,4245,1387}()),
    LIMB_ADD_mk{1448,2167,3093,394,489,3606,4095,4095,88,2648,1928,1002,3701,3606,489,0,0,0,0,0,0,0,0,0,0,0,89,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2266,3992,1142,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2267,3992,1142,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2267,3992,1142,2905,758,3431,1091,3863,318,3363,657,1766,3669,3886,466,0,0,89}(LIMB_SQUARE_mk{2267,3992,1142,2905,758,3431,1091,3863,318,1254,4419,5155,2227}(), LIMB_MULTIPLY_mk{2905,758,3431,1091,3863,318,2267,3992,1142,3363,657,1766,3669,3886,466,0,0,89,1607,3251,3448,4159,4158,4246,1388}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,89,3362,657,1766,3669,3886,466,0,0,0,3363,657,1766,3669,3886,466,0,0,89,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_97 (): CUBE_ROOT_FRAC32(97, 0x983e, 0x5152) =
  CUBE_ROOT_FRAC32_mk{97,38974,20818,5,62,152,4,338,997,1176,339,997,1176,1480,335,1672,366,1305,3152,4095,4095,96,2616,3760,2423,3729,2790,943,0,0,0,1163,1902,2793,3677,2702,69,0,0,97,1162,1902,2793,3677,2702,69,0,0,0}(
    LIMB_CUBE_mk{338,997,1176,3652,2255,3293,2468,3196,337,1480,335,1672,366,1305,3152,4095,4095,96}(LIMB_SQUARE_mk{338,997,1176,3652,2255,3293,2468,3196,337,27,164,436,572}(), LIMB_MULTIPLY_mk{3652,2255,3293,2468,3196,337,338,997,1176,1480,335,1672,366,1305,3152,4095,4095,96,301,1075,1869,1653,1810,1514,999}()),
    LIMB_ADD_mk{1480,335,1672,366,1305,3152,4095,4095,96,2616,3760,2423,3729,2790,943,0,0,0,0,0,0,0,0,0,0,0,97,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{338,997,1176,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,339,997,1176,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{339,997,1176,233,154,1550,2469,3196,337,1163,1902,2793,3677,2702,69,0,0,97}(LIMB_SQUARE_mk{339,997,1176,233,154,1550,2469,3196,337,28,165,437,572}(), LIMB_MULTIPLY_mk{233,154,1550,2469,3196,337,339,997,1176,1163,1902,2793,3677,2702,69,0,0,97,19,69,232,625,1310,1515,1000}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,97,1162,1902,2793,3677,2702,69,0,0,0,1163,1902,2793,3677,2702,69,0,0,97,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_101 (): CUBE_ROOT_FRAC32(101, 0xa831, 0xc66d) =
  CUBE_ROOT_FRAC32_mk{101,43057,50797,12,49,168,4,1645,796,1192,1646,796,1192,1205,166,4051,2817,603,3910,4095,4095,100,2891,3929,44,1278,3492,185,0,0,0,1848,833,2986,1611,650,855,0,0,101,1847,833,2986,1611,650,855,0,0,0}(
    LIMB_CUBE_mk{1645,796,1192,2665,2156,1183,2328,15,347,1205,166,4051,2817,603,3910,4095,4095,100}(LIMB_SQUARE_mk{1645,796,1192,2665,2156,1183,2328,15,347,660,639,1112,463}(), LIMB_MULTIPLY_mk{2665,2156,1183,2328,15,347,1645,796,1192,1205,166,4051,2817,603,3910,4095,4095,100,1070,1384,1669,1792,803,819,71}()),
    LIMB_ADD_mk{1205,166,4051,2817,603,3910,4095,4095,100,2891,3929,44,1278,3492,185,0,0,0,0,0,0,0,0,0,0,0,101,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1645,796,1192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1646,796,1192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1646,796,1192,1860,3749,3567,2328,15,347,1848,833,2986,1611,650,855,0,0,101}(LIMB_SQUARE_mk{1646,796,1192,1860,3749,3567,2328,15,347,661,639,1112,463}(), LIMB_MULTIPLY_mk{1860,3749,3567,2328,15,347,1646,796,1192,1848,833,2986,1611,650,855,0,0,101,747,1868,2703,2720,1497,820,72}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,101,1847,833,2986,1611,650,855,0,0,0,1848,833,2986,1611,650,855,0,0,101,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_103 (): CUBE_ROOT_FRAC32(103, 0xb003, 0x27c8) =
  CUBE_ROOT_FRAC32_mk{103,45059,10184,2,3,176,4,1992,50,1200,1993,50,1200,512,4021,1241,4079,2968,3465,4095,4095,102,3584,74,2854,16,1127,630,0,0,0,3609,2566,2504,3039,1777,424,0,0,103,3608,2566,2504,3039,1777,424,0,0,0}(
    LIMB_CUBE_mk{1992,50,1200,3136,3560,3316,2383,2333,351,512,4021,1241,4079,2968,3465,4095,4095,102}(LIMB_SQUARE_mk{1992,50,1200,3136,3560,3316,2383,2333,351,968,48,1167,29}(), LIMB_MULTIPLY_mk{3136,3560,3316,2383,2333,351,1992,50,1200,512,4021,1241,4079,2968,3465,4095,4095,102,1525,1769,2575,2242,2135,897,687}()),
    LIMB_ADD_mk{512,4021,1241,4079,2968,3465,4095,4095,102,3584,74,2854,16,1127,630,0,0,0,0,0,0,0,0,0,0,0,103,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1992,50,1200,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1993,50,1200,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1993,50,1200,3025,3661,1620,2384,2333,351,3609,2566,2504,3039,1777,424,0,0,103}(LIMB_SQUARE_mk{1993,50,1200,3025,3661,1620,2384,2333,351,969,48,1168,29}(), LIMB_MULTIPLY_mk{3025,3661,1620,2384,2333,351,1993,50,1200,3609,2566,2504,3039,1777,424,0,0,103,1471,1818,1719,2252,1639,898,688}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,103,3608,2566,2504,3039,1777,424,0,0,0,3609,2566,2504,3039,1777,424,0,0,103,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_107 (): CUBE_ROOT_FRAC32(107, 0xbf59, 0x7fc7) =
  CUBE_ROOT_FRAC32_mk{107,48985,32711,7,89,191,4,4039,1431,1215,4040,1431,1215,3223,2586,2236,4082,508,3289,4095,4095,106,873,1509,1859,13,3587,806,0,0,0,512,469,3609,4059,3956,274,0,0,107,511,469,3609,4059,3956,274,0,0,0}(
    LIMB_CUBE_mk{4039,1431,1215,3249,592,3338,2722,2514,360,3223,2586,2236,4082,508,3289,4095,4095,106}(LIMB_SQUARE_mk{4039,1431,1215,3249,592,3338,2722,2514,360,3982,2823,2896,849}(), LIMB_MULTIPLY_mk{3249,592,3338,2722,2514,360,4039,1431,1215,3223,2586,2236,4082,508,3289,4095,4095,106,3203,1719,4462,4026,4421,2041,871}()),
    LIMB_ADD_mk{3223,2586,2236,4082,508,3289,4095,4095,106,873,1509,1859,13,3587,806,0,0,0,0,0,0,0,0,0,0,0,107,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{4039,1431,1215,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4040,1431,1215,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{4040,1431,1215,3136,3456,1672,2723,2514,360,512,469,3609,4059,3956,274,0,0,107}(LIMB_SQUARE_mk{4040,1431,1215,3136,3456,1672,2723,2514,360,3984,2823,2897,849}(), LIMB_MULTIPLY_mk{3136,3456,1672,2723,2514,360,4040,1431,1215,512,469,3609,4059,3956,274,0,0,107,3093,4505,3787,4295,3927,2042,872}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,107,511,469,3609,4059,3956,274,0,0,0,512,469,3609,4059,3956,274,0,0,107,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_109 (): CUBE_ROOT_FRAC32(109, 0xc6e0, 0x0bf3) =
  CUBE_ROOT_FRAC32_mk{109,50912,3059,0,224,198,4,3059,3584,1222,3060,3584,1222,2923,3195,2439,3333,810,3832,4095,4095,108,1173,900,1656,762,3285,263,0,0,0,2368,3395,581,3886,1961,831,0,0,109,2367,3395,581,3886,1961,831,0,0,0}(
    LIMB_CUBE_mk{3059,3584,1222,2217,3308,2253,2914,383,365,2923,3195,2439,3333,810,3832,4095,4095,108}(LIMB_SQUARE_mk{3059,3584,1222,2217,3308,2253,2914,383,365,2284,5353,4962,2139}(), LIMB_MULTIPLY_mk{2217,3308,2253,2914,383,365,3059,3584,1222,2923,3195,2439,3333,810,3832,4095,4095,108,1655,4410,5239,5135,3509,1477,433}()),
    LIMB_ADD_mk{2923,3195,2439,3333,810,3832,4095,4095,108,1173,900,1656,762,3285,263,0,0,0,0,0,0,0,0,0,0,0,109,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3059,3584,1222,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3060,3584,1222,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3060,3584,1222,144,2286,603,2915,383,365,2368,3395,581,3886,1961,831,0,0,109}(LIMB_SQUARE_mk{3060,3584,1222,144,2286,603,2915,383,365,2286,5355,4963,2139}(), LIMB_MULTIPLY_mk{144,2286,603,2915,383,365,3060,3584,1222,2368,3395,581,3886,1961,831,0,0,109,107,1833,2494,3387,3017,1478,434}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,109,2367,3395,581,3886,1961,831,0,0,0,2368,3395,581,3886,1961,831,0,0,109,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_113 (): CUBE_ROOT_FRAC32(113, 0xd5a7, 0x9147) =
  CUBE_ROOT_FRAC32_mk{113,54695,37191,9,167,213,4,327,2681,1237,328,2681,1237,2327,1363,1478,1847,2427,3451,4095,4095,112,1769,2732,2617,2248,1668,644,0,0,0,512,2151,2384,3623,2081,477,0,0,113,511,2151,2384,3623,2081,477,0,0,0}(
    LIMB_CUBE_mk{327,2681,1237,433,312,1795,3322,3980,373,2327,1363,1478,1847,2427,3451,4095,4095,112}(LIMB_SQUARE_mk{327,2681,1237,433,312,1795,3322,3980,373,26,428,1952,1619}(), LIMB_MULTIPLY_mk{433,312,1795,3322,3980,373,327,2681,1237,2327,1363,1478,1847,2427,3451,4095,4095,112,34,308,478,1534,3034,3638,1446}()),
    LIMB_ADD_mk{2327,1363,1478,1847,2427,3451,4095,4095,112,1769,2732,2617,2248,1668,644,0,0,0,0,0,0,0,0,0,0,0,113,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{327,2681,1237,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,328,2681,1237,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{328,2681,1237,1088,1578,174,3323,3980,373,512,2151,2384,3623,2081,477,0,0,113}(LIMB_SQUARE_mk{328,2681,1237,1088,1578,174,3323,3980,373,26,429,1953,1619}(), LIMB_MULTIPLY_mk{1088,1578,174,3323,3980,373,328,2681,1237,512,2151,2384,3623,2081,477,0,0,113,87,838,1375,856,2546,3639,1447}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,113,511,2151,2384,3623,2081,477,0,0,0,512,2151,2384,3623,2081,477,0,0,113,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_127 (): CUBE_ROOT_FRAC32(127, 0x06ca, 0x6351) =
  CUBE_ROOT_FRAC32_mk{127,1738,25425,6,202,6,5,849,3238,1286,850,3238,1286,1265,718,3745,1057,3132,3034,4095,4095,126,2831,3377,350,3038,963,1061,0,0,0,3528,2548,1472,954,2174,151,0,0,127,3527,2548,1472,954,2174,151,0,0,0}(
    LIMB_CUBE_mk{849,3238,1286,4001,1467,686,4061,1045,404,1265,718,3745,1057,3132,3034,4095,4095,126}(LIMB_SQUARE_mk{849,3238,1286,4001,1467,686,4061,1045,404,175,1342,3093,2033}(), LIMB_MULTIPLY_mk{4001,1467,686,4061,1045,404,849,3238,1286,1265,718,3745,1057,3132,3034,4095,4095,126,829,3467,2558,1845,3642,2185,647}()),
    LIMB_ADD_mk{1265,718,3745,1057,3132,3034,4095,4095,126,2831,3377,350,3038,963,1061,0,0,0,0,0,0,0,0,0,0,0,127,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{849,3238,1286,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,850,3238,1286,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{850,3238,1286,1604,3848,3259,4061,1045,404,3528,2548,1472,954,2174,151,0,0,127}(LIMB_SQUARE_mk{850,3238,1286,1604,3848,3259,4061,1045,404,176,1343,3093,2033}(), LIMB_MULTIPLY_mk{1604,3848,3259,4061,1045,404,850,3238,1286,3528,2548,1472,954,2174,151,0,0,127,332,2066,4222,4628,4451,2186,648}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,127,3527,2548,1472,954,2174,151,0,0,0,3528,2548,1472,954,2174,151,0,0,127,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_131 (): CUBE_ROOT_FRAC32(131, 0x1429, 0x2967) =
  CUBE_ROOT_FRAC32_mk{131,5161,10599,2,41,20,5,2407,658,1300,2408,658,1300,1911,1183,169,1689,1491,4047,4095,4095,130,2185,2912,3926,2406,2604,48,0,0,0,2560,3422,1290,2607,1897,1189,0,0,131,2559,3422,1290,2607,1897,1189,0,0,0}(
    LIMB_CUBE_mk{2407,658,1300,1905,2818,3169,305,2866,412,1911,1183,169,1689,1491,4047,4095,4095,130}(LIMB_SQUARE_mk{2407,658,1300,1905,2818,3169,305,2866,412,1414,773,1633,418}(), LIMB_MULTIPLY_mk{1905,2818,3169,305,2866,412,2407,658,1300,1911,1183,169,1689,1491,4047,4095,4095,130,1119,1962,2920,1583,2739,799,975}()),
    LIMB_ADD_mk{1911,1183,169,1689,1491,4047,4095,4095,130,2185,2912,3926,2406,2604,48,0,0,0,0,0,0,0,0,0,0,0,131,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2407,658,1300,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2408,658,1300,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2408,658,1300,2624,39,1674,306,2866,412,2560,3422,1290,2607,1897,1189,0,0,131}(LIMB_SQUARE_mk{2408,658,1300,2624,39,1674,306,2866,412,1415,774,1634,418}(), LIMB_MULTIPLY_mk{2624,39,1674,306,2866,412,2408,658,1300,2560,3422,1290,2607,1897,1189,0,0,131,1542,444,1823,461,2265,800,976}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,131,2559,3422,1290,2607,1897,1189,0,0,0,2560,3422,1290,2607,1897,1189,0,0,131,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_137 (): CUBE_ROOT_FRAC32(137, 0x27b7, 0x0a85) =
  CUBE_ROOT_FRAC32_mk{137,10167,2693,0,183,39,5,2693,2928,1319,2694,2928,1319,1021,2909,923,653,435,3743,4095,4095,136,3075,1186,3172,3442,3660,352,0,0,0,3800,2446,1732,971,2978,922,0,0,137,3799,2446,1732,971,2978,922,0,0,0}(
    LIMB_CUBE_mk{2693,2928,1319,2329,2378,1680,2836,847,425,1021,2909,923,653,435,3743,4095,4095,136}(LIMB_SQUARE_mk{2693,2928,1319,2329,2378,1680,2836,847,425,1770,3850,3828,1886}(), LIMB_MULTIPLY_mk{2329,2378,1680,2836,847,425,2693,2928,1319,1021,2909,923,653,435,3743,4095,4095,136,1531,3228,3555,3832,3126,1798,576}()),
    LIMB_ADD_mk{1021,2909,923,653,435,3743,4095,4095,136,3075,1186,3172,3442,3660,352,0,0,0,0,0,0,0,0,0,0,0,137,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2693,2928,1319,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2694,2928,1319,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2694,2928,1319,3620,43,224,2837,847,425,3800,2446,1732,971,2978,922,0,0,137}(LIMB_SQUARE_mk{2694,2928,1319,3620,43,224,2837,847,425,1771,3852,3829,1886}(), LIMB_MULTIPLY_mk{3620,43,224,2837,847,425,2694,2928,1319,3800,2446,1732,971,2978,922,0,0,137,2380,2616,1344,2040,2657,1799,577}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,137,3799,2446,1732,971,2978,922,0,0,0,3800,2446,1732,971,2978,922,0,0,137,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_139 (): CUBE_ROOT_FRAC32(139, 0x2e1b, 0x2138) =
  CUBE_ROOT_FRAC32_mk{139,11803,8504,2,27,46,5,312,434,1326,313,434,1326,3584,2678,2048,1661,1477,3632,4095,4095,138,512,1417,2047,2434,2618,463,0,0,0,1641,1396,2045,2382,1500,824,0,0,139,1640,1396,2045,2382,1500,824,0,0,0}(
    LIMB_CUBE_mk{312,434,1326,3136,503,38,240,1373,429,3584,2678,2048,1661,1477,3632,4095,4095,138}(LIMB_SQUARE_mk{312,434,1326,3136,503,38,240,1373,429,23,66,248,281}(), LIMB_MULTIPLY_mk{3136,503,38,240,1373,429,312,434,1326,3584,2678,2048,1661,1477,3632,4095,4095,138,238,370,1071,185,142,255,489}()),
    LIMB_ADD_mk{3584,2678,2048,1661,1477,3632,4095,4095,138,512,1417,2047,2434,2618,463,0,0,0,0,0,0,0,0,0,0,0,139,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{312,434,1326,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,313,434,1326,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{313,434,1326,3761,1371,2690,240,1373,429,1641,1396,2045,2382,1500,824,0,0,139}(LIMB_SQUARE_mk{313,434,1326,3761,1371,2690,240,1373,429,23,66,248,281}(), LIMB_MULTIPLY_mk{3761,1371,2690,240,1373,429,313,434,1326,1641,1396,2045,2382,1500,824,0,0,139,287,503,1568,747,1001,256,490}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,139,1640,1396,2045,2382,1500,824,0,0,0,1641,1396,2045,2382,1500,824,0,0,139,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_149 (): CUBE_ROOT_FRAC32(149, 0x4d2c, 0x6dfc) =
  CUBE_ROOT_FRAC32_mk{149,19756,28156,6,44,77,5,3580,710,1357,3581,710,1357,4032,585,1465,3228,2793,3617,4095,4095,148,64,3510,2630,867,1302,478,0,0,0,2533,1209,3170,3887,3049,870,0,0,149,2532,1209,3170,3887,3049,870,0,0,0}(
    LIMB_CUBE_mk{3580,710,1357,16,3593,1941,219,2816,449,4032,585,1465,3228,2793,3617,4095,4095,148}(LIMB_SQUARE_mk{3580,710,1357,16,3593,1941,219,2816,449,3129,1241,2495,471}(), LIMB_MULTIPLY_mk{16,3593,1941,219,2816,449,3580,710,1357,4032,585,1465,3228,2793,3617,4095,4095,148,13,3143,2325,1718,3142,953,1010}()),
    LIMB_ADD_mk{4032,585,1465,3228,2793,3617,4095,4095,148,64,3510,2630,867,1302,478,0,0,0,0,0,0,0,0,0,0,0,149,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3580,710,1357,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3581,710,1357,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3581,710,1357,3081,918,560,220,2816,449,2533,1209,3170,3887,3049,870,0,0,149}(LIMB_SQUARE_mk{3581,710,1357,3081,918,560,220,2816,449,3130,1242,2496,471}(), LIMB_MULTIPLY_mk{3081,918,560,220,2816,449,3581,710,1357,2533,1209,3170,3887,3049,870,0,0,149,2693,1337,1669,593,2685,954,1011}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,149,2532,1209,3170,3887,3049,870,0,0,0,2533,1209,3170,3887,3049,870,0,0,149,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_151 (): CUBE_ROOT_FRAC32(151, 0x5338, 0x0d13) =
  CUBE_ROOT_FRAC32_mk{151,21304,3347,0,56,83,5,3347,896,1363,3348,896,1363,2507,3073,2552,71,610,3258,4095,4095,150,1589,1022,1543,4024,3485,837,0,0,0,3904,1424,1043,2992,1051,523,0,0,151,3903,1424,1043,2992,1051,523,0,0,0}(
    LIMB_CUBE_mk{3347,896,1363,3945,4014,3594,3703,2877,453,2507,3073,2552,71,610,3258,4095,4095,150}(LIMB_SQUARE_mk{3347,896,1363,3945,4014,3594,3703,2877,453,2734,1464,2423,596}(), LIMB_MULTIPLY_mk{3945,4014,3594,3703,2877,453,3347,896,1363,2507,3073,2552,71,610,3258,4095,4095,150,3223,4143,5128,5149,4358,2232,1056}()),
    LIMB_ADD_mk{2507,3073,2552,71,610,3258,4095,4095,150,1589,1022,1543,4024,3485,837,0,0,0,0,0,0,0,0,0,0,0,151,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3347,896,1363,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3348,896,1363,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3348,896,1363,2448,1712,2225,3704,2877,453,3904,1424,1043,2992,1051,523,0,0,151}(LIMB_SQUARE_mk{3348,896,1363,2448,1712,2225,3704,2877,453,2736,1465,2424,596}(), LIMB_MULTIPLY_mk{2448,1712,2225,3704,2877,453,3348,896,1363,3904,1424,1043,2992,1051,523,0,0,151,2000,1935,3008,4084,3903,2233,1057}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,151,3903,1424,1043,2992,1051,523,0,0,0,3904,1424,1043,2992,1051,523,0,0,151,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_157 (): CUBE_ROOT_FRAC32(157, 0x650a, 0x7354) =
  CUBE_ROOT_FRAC32_mk{157,25866,29524,7,10,101,5,852,167,1381,853,167,1381,2880,1697,2213,3657,3164,3333,4095,4095,156,1216,2398,1882,438,931,762,0,0,0,4077,370,2384,620,2874,634,0,0,157,4076,370,2384,620,2874,634,0,0,0}(
    LIMB_CUBE_mk{852,167,1381,912,2121,1406,3083,2633,465,2880,1697,2213,3657,3164,3333,4095,4095,156}(LIMB_SQUARE_mk{852,167,1381,912,2121,1406,3083,2633,465,177,69,581,112}(), LIMB_MULTIPLY_mk{912,2121,1406,3083,2633,465,852,167,1381,2880,1697,2213,3657,3164,3333,4095,4095,156,189,478,686,1413,1147,1243,906}()),
    LIMB_ADD_mk{2880,1697,2213,3657,3164,3333,4095,4095,156,1216,2398,1882,438,931,762,0,0,0,0,0,0,0,0,0,0,0,157,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{852,167,1381,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,853,167,1381,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{853,167,1381,2617,2455,72,3084,2633,465,4077,370,2384,620,2874,634,0,0,157}(LIMB_SQUARE_mk{853,167,1381,2617,2455,72,3084,2633,465,177,69,582,112}(), LIMB_MULTIPLY_mk{2617,2455,72,3084,2633,465,853,167,1381,4077,370,2384,620,2874,634,0,0,157,544,618,997,1473,698,1244,907}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,157,4076,370,2384,620,2874,634,0,0,0,4077,370,2384,620,2874,634,0,0,157,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_163 (): CUBE_ROOT_FRAC32(163, 0x766a, 0x0abb) =
  CUBE_ROOT_FRAC32_mk{163,30314,2747,0,106,118,5,2747,1696,1398,2748,1696,1398,1475,2427,731,180,2824,3757,4095,4095,162,2621,1668,3364,3915,1271,338,0,0,0,960,3124,276,363,4039,1093,0,0,163,959,3124,276,363,4039,1093,0,0,0}(
    LIMB_CUBE_mk{2747,1696,1398,1177,1266,3911,1425,1770,477,1475,2427,731,180,2824,3757,4095,4095,162}(LIMB_SQUARE_mk{2747,1696,1398,1177,1266,3911,1425,1770,477,1842,2275,2577,1158}(), LIMB_MULTIPLY_mk{1177,1266,3911,1425,1770,477,2747,1696,1398,1475,2427,731,180,2824,3757,4095,4095,162,789,1336,3549,3008,3112,1539,801}()),
    LIMB_ADD_mk{1475,2427,731,180,2824,3757,4095,4095,162,2621,1668,3364,3915,1271,338,0,0,0,0,0,0,0,0,0,0,0,163,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2747,1696,1398,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2748,1696,1398,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2748,1696,1398,2576,563,2612,1426,1770,477,960,3124,276,363,4039,1093,0,0,163}(LIMB_SQUARE_mk{2748,1696,1398,2576,563,2612,1426,1770,477,1843,2276,2578,1158}(), LIMB_MULTIPLY_mk{2576,563,2612,1426,1770,477,2748,1696,1398,960,3124,276,363,4039,1093,0,0,163,1728,1444,2865,2231,2669,1540,802}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,163,959,3124,276,363,4039,1093,0,0,0,960,3124,276,363,4039,1093,0,0,163,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_167 (): CUBE_ROOT_FRAC32(167, 0x81c2, 0xc92e) =
  CUBE_ROOT_FRAC32_mk{167,33218,51502,12,194,129,5,2350,3116,1409,2351,3116,1409,2104,3002,1597,3840,39,3687,4095,4095,166,1992,1093,2498,255,4056,408,0,0,0,143,1917,3182,709,2637,1046,0,0,167,142,1917,3182,709,2637,1046,0,0,0}(
    LIMB_CUBE_mk{2350,3116,1409,1092,3348,483,3052,865,485,2104,3002,1597,3840,39,3687,4095,4095,166}(LIMB_SQUARE_mk{2350,3116,1409,1092,3348,483,3052,865,485,1348,3575,3988,2144}(), LIMB_MULTIPLY_mk{1092,3348,483,3052,865,485,2350,3116,1409,2104,3002,1597,3840,39,3687,4095,4095,166,626,2751,3200,3270,2985,1986,666}()),
    LIMB_ADD_mk{2104,3002,1597,3840,39,3687,4095,4095,166,1992,1093,2498,255,4056,408,0,0,0,0,0,0,0,0,0,0,0,167,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2350,3116,1409,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2351,3116,1409,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2351,3116,1409,1697,1389,3303,3052,865,485,143,1917,3182,709,2637,1046,0,0,167}(LIMB_SQUARE_mk{2351,3116,1409,1697,1389,3303,3052,865,485,1349,3577,3988,2144}(), LIMB_MULTIPLY_mk{1697,1389,3303,3052,865,485,2351,3116,1409,143,1917,3182,709,2637,1046,0,0,167,974,2088,3536,4743,3955,1987,667}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,167,142,1917,3182,709,2637,1046,0,0,0,143,1917,3182,709,2637,1046,0,0,167,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_173 (): CUBE_ROOT_FRAC32(173, 0x9272, 0x2c85) =
  CUBE_ROOT_FRAC32_mk{173,37490,11397,2,114,146,5,3205,1826,1426,3206,1826,1426,2557,2476,1170,3650,2497,3976,4095,4095,172,1539,1619,2925,445,1598,119,0,0,0,1752,2164,1392,1614,3702,1370,0,0,173,1751,2164,1392,1614,3702,1370,0,0,0}(
    LIMB_CUBE_mk{3205,1826,1426,3353,799,1378,686,3132,496,2557,2476,1170,3650,2497,3976,4095,4095,172}(LIMB_SQUARE_mk{3205,1826,1426,3353,799,1378,686,3132,496,2507,2858,3046,1272}(), LIMB_MULTIPLY_mk{3353,799,1378,686,3132,496,3205,1826,1426,2557,2476,1170,3650,2497,3976,4095,4095,172,2623,2120,2602,1429,3236,2023,1311}()),
    LIMB_ADD_mk{2557,2476,1170,3650,2497,3976,4095,4095,172,1539,1619,2925,445,1598,119,0,0,0,0,0,0,0,0,0,0,0,173,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3205,1826,1426,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3206,1826,1426,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3206,1826,1426,1572,357,135,687,3132,496,1752,2164,1392,1614,3702,1370,0,0,173}(LIMB_SQUARE_mk{3206,1826,1426,1572,357,135,687,3132,496,2509,2859,3047,1272}(), LIMB_MULTIPLY_mk{1572,357,135,687,3132,496,3206,1826,1426,1752,2164,1392,1614,3702,1370,0,0,173,1230,980,812,722,2804,2024,1312}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,173,1751,2164,1392,1614,3702,1370,0,0,0,1752,2164,1392,1614,3702,1370,0,0,173,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_179 (): CUBE_ROOT_FRAC32(179, 0xa2bf, 0xe8a1) =
  CUBE_ROOT_FRAC32_mk{179,41663,59553,14,191,162,5,2209,3070,1442,2210,3070,1442,1505,3158,3674,2250,3239,3637,4095,4095,178,2591,937,421,1845,856,458,0,0,0,3976,3771,1897,615,1419,1066,0,0,179,3975,3771,1897,615,1419,1066,0,0,0}(
    LIMB_CUBE_mk{2209,3070,1442,1345,2595,695,2185,758,508,1505,3158,3674,2250,3239,3637,4095,4095,178}(LIMB_SQUARE_mk{2209,3070,1442,1345,2595,695,2185,758,508,1191,3311,3857,2162}(), LIMB_MULTIPLY_mk{1345,2595,695,2185,758,508,2209,3070,1442,1505,3158,3674,2250,3239,3637,4095,4095,178,725,2407,2793,2613,2291,1611,647}()),
    LIMB_ADD_mk{1505,3158,3674,2250,3239,3637,4095,4095,178,2591,937,421,1845,856,458,0,0,0,0,0,0,0,0,0,0,0,179,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2209,3070,1442,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2210,3070,1442,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2210,3070,1442,1668,544,3581,2185,758,508,3976,3771,1897,615,1419,1066,0,0,179}(LIMB_SQUARE_mk{2210,3070,1442,1668,544,3581,2185,758,508,1192,3313,3857,2162}(), LIMB_MULTIPLY_mk{1668,544,3581,2185,758,508,2210,3070,1442,3976,3771,1897,615,1419,1066,0,0,179,899,1543,2927,4055,3308,1612,648}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,179,3975,3771,1897,615,1419,1066,0,0,0,3976,3771,1897,615,1419,1066,0,0,179,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_181 (): CUBE_ROOT_FRAC32(181, 0xa81a, 0x664b) =
  CUBE_ROOT_FRAC32_mk{181,43034,26187,6,26,168,5,1611,422,1448,1612,422,1448,499,1217,1740,1942,2167,2966,4095,4095,180,3597,2878,2355,2153,1928,1129,0,0,0,704,3821,996,1811,1719,406,0,0,181,703,3821,996,1811,1719,406,0,0,0}(
    LIMB_CUBE_mk{1611,422,1448,2553,445,2400,2686,3946,511,499,1217,1740,1942,2167,2966,4095,4095,180}(LIMB_SQUARE_mk{1611,422,1448,2553,445,2400,2686,3946,511,633,332,1182,298}(), LIMB_MULTIPLY_mk{2553,445,2400,2686,3946,511,1611,422,1448,499,1217,1740,1942,2167,2966,4095,4095,180,1004,438,1892,1461,2677,1557,1447}()),
    LIMB_ADD_mk{499,1217,1740,1942,2167,2966,4095,4095,180,3597,2878,2355,2153,1928,1129,0,0,0,0,0,0,0,0,0,0,0,181,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1611,422,1448,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1612,422,1448,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1612,422,1448,1680,1290,1200,2687,3946,511,704,3821,996,1811,1719,406,0,0,181}(LIMB_SQUARE_mk{1612,422,1448,1680,1290,1200,2687,3946,511,634,332,1183,298}(), LIMB_MULTIPLY_mk{1680,1290,1200,2687,3946,511,1612,422,1448,704,3821,996,1811,1719,406,0,0,181,661,680,1199,1637,2254,1558,1448}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,181,703,3821,996,1811,1719,406,0,0,0,704,3821,996,1811,1719,406,0,0,181,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_191 (): CUBE_ROOT_FRAC32(191, 0xc24b, 0x8b70) =
  CUBE_ROOT_FRAC32_mk{191,49739,35696,8,75,194,5,2928,1208,1474,2929,1208,1474,0,2919,3522,1531,2047,2796,4095,4095,190,0,1177,573,2564,2048,1299,0,0,0,1361,1304,328,1917,1853,292,0,0,191,1360,1304,328,1917,1853,292,0,0,0}(
    LIMB_CUBE_mk{2928,1208,1474,256,2349,191,128,2666,530,0,2919,3522,1531,2047,2796,4095,4095,190}(LIMB_SQUARE_mk{2928,1208,1474,256,2349,191,128,2666,530,2093,1727,2464,870}(), LIMB_MULTIPLY_mk{256,2349,191,128,2666,530,2928,1208,1474,0,2919,3522,1531,2047,2796,4095,4095,190,183,1754,921,993,2012,1211,1115}()),
    LIMB_ADD_mk{0,2919,3522,1531,2047,2796,4095,4095,190,0,1177,573,2564,2048,1299,0,0,0,0,0,0,0,0,0,0,0,191,0,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2928,1208,1474,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2929,1208,1474,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2929,1208,1474,2017,670,3140,128,2666,530,1361,1304,328,1917,1853,292,0,0,191}(LIMB_SQUARE_mk{2929,1208,1474,2017,670,3140,128,2666,530,2094,1728,2464,870}(), LIMB_MULTIPLY_mk{2017,670,3140,128,2666,530,2929,1208,1474,1361,1304,328,1917,1853,292,0,0,191,1442,1074,3169,1259,3074,1212,1116}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,191,1360,1304,328,1917,1853,292,0,0,0,1361,1304,328,1917,1853,292,0,0,191,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_193 (): CUBE_ROOT_FRAC32(193, 0xc76c, 0x51a3) =
  CUBE_ROOT_FRAC32_mk{193,51052,20899,5,108,199,5,419,1733,1479,420,1733,1479,4091,2861,3447,457,1457,4056,4095,4095,192,5,1234,648,3638,2638,39,0,0,0,3648,2711,2558,1728,1647,1563,0,0,193,3647,2711,2558,1728,1647,1563,0,0,0}(
    LIMB_CUBE_mk{419,1733,1479,3529,2312,3685,3153,1428,534,4091,2861,3447,457,1457,4056,4095,4095,192}(LIMB_SQUARE_mk{419,1733,1479,3529,2312,3685,3153,1428,534,42,354,1035,1251}(), LIMB_MULTIPLY_mk{3529,2312,3685,3153,1428,534,419,1733,1479,4091,2861,3447,457,1457,4056,4095,4095,192,360,1729,2629,2717,2811,1797,741}()),
    LIMB_ADD_mk{4091,2861,3447,457,1457,4056,4095,4095,192,5,1234,648,3638,2638,39,0,0,0,0,0,0,0,0,0,0,0,193,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{419,1733,1479,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,420,1733,1479,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{420,1733,1479,272,1683,2548,3154,1428,534,3648,2711,2558,1728,1647,1563,0,0,193}(LIMB_SQUARE_mk{420,1733,1479,272,1683,2548,3154,1428,534,43,355,1036,1251}(), LIMB_MULTIPLY_mk{272,1683,2548,3154,1428,534,420,1733,1479,3648,2711,2558,1728,1647,1563,0,0,193,27,287,1071,2009,2401,1798,742}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,193,3647,2711,2558,1728,1647,1563,0,0,0,3648,2711,2558,1728,1647,1563,0,0,193,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_197 (): CUBE_ROOT_FRAC32(197, 0xd192, 0xe819) =
  CUBE_ROOT_FRAC32_mk{197,53650,59417,14,146,209,5,2073,2350,1489,2074,2350,1489,1289,2967,2159,3780,2321,2731,4095,4095,196,2807,1128,1936,315,1774,1364,0,0,0,1192,1122,2823,2961,2812,260,0,0,197,1191,1122,2823,2961,2812,260,0,0,0}(
    LIMB_CUBE_mk{2073,2350,1489,625,3861,96,1092,2894,541,1289,2967,2159,3780,2321,2731,4095,4095,196}(LIMB_SQUARE_mk{2073,2350,1489,625,3861,96,1092,2894,541,1049,2378,2856,1709}(), LIMB_MULTIPLY_mk{625,3861,96,1092,2894,541,2073,2350,1489,1289,2967,2159,3780,2321,2731,4095,4095,196,316,2312,2491,2011,2126,2331,1362}()),
    LIMB_ADD_mk{1289,2967,2159,3780,2321,2731,4095,4095,196,2807,1128,1936,315,1774,1364,0,0,0,0,0,0,0,0,0,0,0,197,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2073,2350,1489,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2074,2350,1489,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2074,2350,1489,676,370,3076,1092,2894,541,1192,1122,2823,2961,2812,260,0,0,197}(LIMB_SQUARE_mk{2074,2350,1489,676,370,3076,1092,2894,541,1050,2380,2856,1709}(), LIMB_MULTIPLY_mk{676,370,3076,1092,2894,541,2074,2350,1489,1192,1122,2823,2961,2812,260,0,0,197,342,575,2015,2452,3210,2332,1363}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,197,1191,1122,2823,2961,2812,260,0,0,0,1192,1122,2823,2961,2812,260,0,0,197,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_199 (): CUBE_ROOT_FRAC32(199, 0xd699, 0x0624) =
  CUBE_ROOT_FRAC32_mk{199,54937,1572,0,153,214,5,1572,2448,1494,1573,2448,1494,1600,957,2731,84,924,3550,4095,4095,198,2496,3138,1364,4011,3171,545,0,0,0,2013,2304,2500,1324,1335,1090,0,0,199,2012,2304,2500,1324,1335,1090,0,0,0}(
    LIMB_CUBE_mk{1572,2448,1494,1296,731,1159,1778,1502,545,1600,957,2731,84,924,3550,4095,4095,198}(LIMB_SQUARE_mk{1572,2448,1494,1296,731,1159,1778,1502,545,603,1879,2610,1786}(), LIMB_MULTIPLY_mk{1296,731,1159,1778,1502,545,1572,2448,1494,1600,957,2731,84,924,3550,4095,4095,198,497,1055,1354,1642,2062,1755,873}()),
    LIMB_ADD_mk{1600,957,2731,84,924,3550,4095,4095,198,2496,3138,1364,4011,3171,545,0,0,0,0,0,0,0,0,0,0,0,199,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1572,2448,1494,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1573,2448,1494,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1573,2448,1494,345,1532,52,1779,1502,545,2013,2304,2500,1324,1335,1090,0,0,199}(LIMB_SQUARE_mk{1573,2448,1494,345,1532,52,1779,1502,545,604,1880,2611,1786}(), LIMB_MULTIPLY_mk{345,1532,52,1779,1502,545,1573,2448,1494,2013,2304,2500,1324,1335,1090,0,0,199,132,794,1061,1273,1659,1756,874}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,199,2012,2304,2500,1324,1335,1090,0,0,0,2013,2304,2500,1324,1335,1090,0,0,199,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_211 (): CUBE_ROOT_FRAC32(211, 0xf40e, 0x3585) =
  CUBE_ROOT_FRAC32_mk{211,62478,13701,3,14,244,5,1413,227,1524,1414,227,1524,3325,1014,920,1684,3732,3514,4095,4095,210,771,3081,3175,2411,363,581,0,0,0,728,2545,2493,3893,575,1120,0,0,211,727,2545,2493,3893,575,1120,0,0,0}(
    LIMB_CUBE_mk{1413,227,1524,1817,3013,365,736,313,567,3325,1014,920,1684,3732,3514,4095,4095,210}(LIMB_SQUARE_mk{1413,227,1524,1817,3013,365,736,313,567,487,156,1064,169}(), LIMB_MULTIPLY_mk{1817,3013,365,736,313,567,1413,227,1524,3325,1014,920,1684,3732,3514,4095,4095,210,626,1140,969,1395,284,486,147}()),
    LIMB_ADD_mk{3325,1014,920,1684,3732,3514,4095,4095,210,771,3081,3175,2411,363,581,0,0,0,0,0,0,0,0,0,0,0,211,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1413,227,1524,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1414,227,1524,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1414,227,1524,548,3468,3413,736,313,567,728,2545,2493,3893,575,1120,0,0,211}(LIMB_SQUARE_mk{1414,227,1524,548,3468,3413,736,313,567,488,156,1064,169}(), LIMB_MULTIPLY_mk{548,3468,3413,736,313,567,1414,227,1524,728,2545,2493,3893,575,1120,0,0,211,189,1227,1574,1733,1419,487,148}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,211,727,2545,2493,3893,575,1120,0,0,0,728,2545,2493,3893,575,1120,0,0,211,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_223 (): CUBE_ROOT_FRAC32(223, 0x106a, 0xa070) =
  CUBE_ROOT_FRAC32_mk{223,4202,41072,10,106,16,6,112,1706,1552,113,1706,1552,0,3927,2169,4025,771,3746,4095,4095,222,0,169,1926,70,3324,349,0,0,0,1105,414,111,205,1323,1415,0,0,223,1104,414,111,205,1323,1415,0,0,0}(
    LIMB_CUBE_mk{112,1706,1552,256,1219,1857,91,1549,588,0,3927,2169,4025,771,3746,4095,4095,222}(LIMB_SQUARE_mk{112,1706,1552,256,1219,1857,91,1549,588,3,93,795,1293}(), LIMB_MULTIPLY_mk{256,1219,1857,91,1549,588,112,1706,1552,0,3927,2169,4025,771,3746,4095,4095,222,7,139,655,1237,784,695,831}()),
    LIMB_ADD_mk{0,3927,2169,4025,771,3746,4095,4095,222,0,169,1926,70,3324,349,0,0,0,0,0,0,0,0,0,0,0,223,0,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{112,1706,1552,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,113,1706,1552,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{113,1706,1552,481,535,866,92,1549,588,1105,414,111,205,1323,1415,0,0,223}(LIMB_SQUARE_mk{113,1706,1552,481,535,866,92,1549,588,3,94,796,1293}(), LIMB_MULTIPLY_mk{481,535,866,92,1549,588,113,1706,1552,1105,414,111,205,1323,1415,0,0,223,13,215,429,566,409,696,832}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,223,1104,414,111,205,1323,1415,0,0,0,1105,414,111,205,1323,1415,0,0,223,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_227 (): CUBE_ROOT_FRAC32(227, 0x19a4, 0xc116) =
  CUBE_ROOT_FRAC32_mk{227,6564,49430,12,164,25,6,278,2636,1561,279,2636,1561,1432,2957,454,1618,1792,2806,4095,4095,226,2664,1138,3641,2477,2303,1289,0,0,0,647,474,1753,1336,2528,496,0,0,227,646,474,1753,1336,2528,496,0,0,0}(
    LIMB_CUBE_mk{278,2636,1561,3556,3362,1601,2636,1610,595,1432,2957,454,1618,1792,2806,4095,4095,226}(LIMB_SQUARE_mk{278,2636,1561,3556,3362,1601,2636,1610,595,18,357,1908,2009}(), LIMB_MULTIPLY_mk{3556,3362,1601,2636,1610,595,278,2636,1561,1432,2957,454,1618,1792,2806,4095,4095,226,241,2516,3628,2491,2416,2081,996}()),
    LIMB_ADD_mk{1432,2957,454,1618,1792,2806,4095,4095,226,2664,1138,3641,2477,2303,1289,0,0,0,0,0,0,0,0,0,0,0,227,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{278,2636,1561,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,279,2636,1561,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{279,2636,1561,17,443,629,2637,1610,595,647,474,1753,1336,2528,496,0,0,227}(LIMB_SQUARE_mk{279,2636,1561,17,443,629,2637,1610,595,19,359,1909,2009}(), LIMB_MULTIPLY_mk{17,443,629,2637,1610,595,279,2636,1561,647,474,1753,1336,2528,496,0,0,227,1,41,334,753,2046,2082,997}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,227,646,474,1753,1336,2528,496,0,0,0,647,474,1753,1336,2528,496,0,0,227,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_229 (): CUBE_ROOT_FRAC32(229, 0x1e37, 0x6c08) =
  CUBE_ROOT_FRAC32_mk{229,7735,27656,6,55,30,6,3080,886,1566,3081,886,1566,512,272,1391,3985,2975,3525,4095,4095,228,3584,3823,2704,110,1120,570,0,0,0,1753,3256,3124,1123,1566,1226,0,0,229,1752,3256,3124,1123,1566,1226,0,0,0}(
    LIMB_CUBE_mk{3080,886,1566,64,108,377,411,3626,598,512,272,1391,3985,2975,3525,4095,4095,228}(LIMB_SQUARE_mk{3080,886,1566,64,108,377,411,3626,598,2316,1333,2547,678}(), LIMB_MULTIPLY_mk{64,108,377,411,3626,598,3080,886,1566,512,272,1391,3985,2975,3525,4095,4095,228,48,95,331,431,2959,1391,1515}()),
    LIMB_ADD_mk{512,272,1391,3985,2975,3525,4095,4095,228,3584,3823,2704,110,1120,570,0,0,0,0,0,0,0,0,0,0,0,229,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3080,886,1566,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3081,886,1566,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3081,886,1566,2129,1881,3509,411,3626,598,1753,3256,3124,1123,1566,1226,0,0,229}(LIMB_SQUARE_mk{3081,886,1566,2129,1881,3509,411,3626,598,2317,1333,2547,678}(), LIMB_MULTIPLY_mk{2129,1881,3509,411,3626,598,3081,886,1566,1753,3256,3124,1123,1566,1226,0,0,229,1601,1875,3860,1788,4158,1392,1516}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,229,1752,3256,3124,1123,1566,1226,0,0,0,1753,3256,3124,1123,1566,1226,0,0,229,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_233 (): CUBE_ROOT_FRAC32(233, 0x2748, 0x774c) =
  CUBE_ROOT_FRAC32_mk{233,10056,30540,7,72,39,6,1868,1159,1575,1869,1159,1575,704,536,2212,3250,3311,2508,4095,4095,232,3392,3559,1883,845,784,1587,0,0,0,1109,34,137,200,1334,230,0,0,233,1108,34,137,200,1334,230,0,0,0}(
    LIMB_CUBE_mk{1868,1159,1575,3728,1403,3194,3078,3436,605,704,536,2212,3250,3311,2508,4095,4095,232}(LIMB_SQUARE_mk{1868,1159,1575,3728,1403,3194,3078,3436,605,851,1057,1764,891}(), LIMB_MULTIPLY_mk{3728,1403,3194,3078,3436,605,1868,1159,1575,704,536,2212,3250,3311,2508,4095,4095,232,1700,1695,3287,2847,3666,2432,1492}()),
    LIMB_ADD_mk{704,536,2212,3250,3311,2508,4095,4095,232,3392,3559,1883,845,784,1587,0,0,0,0,0,0,0,0,0,0,0,233,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1868,1159,1575,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1869,1159,1575,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1869,1159,1575,3369,3722,2248,3079,3436,605,1109,34,137,200,1334,230,0,0,233}(LIMB_SQUARE_mk{1869,1159,1575,3369,3722,2248,3079,3436,605,852,1057,1765,891}(), LIMB_MULTIPLY_mk{3369,3722,2248,3079,3436,605,1869,1159,1575,1109,34,137,200,1334,230,0,0,233,1537,2652,3375,3473,3304,2433,1493}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,233,1108,34,137,200,1334,230,0,0,0,1109,34,137,200,1334,230,0,0,233,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_239 (): CUBE_ROOT_FRAC32(239, 0x34b0, 0xbcb5) =
  CUBE_ROOT_FRAC32_mk{239,13488,48309,11,176,52,6,3253,2827,1588,3254,2827,1588,3853,3248,3295,2831,3626,2466,4095,4095,238,243,847,800,1264,469,1629,0,0,0,3352,3268,3105,232,1934,219,0,0,239,3351,3268,3105,232,1934,219,0,0,0}(
    LIMB_CUBE_mk{3253,2827,1588,2041,4005,2443,498,801,616,3853,3248,3295,2831,3626,2466,4095,4095,238}(LIMB_SQUARE_mk{3253,2827,1588,2041,4005,2443,498,801,616,2583,4490,4474,2193}(), LIMB_MULTIPLY_mk{2041,4005,2443,498,801,616,3253,2827,1588,3853,3248,3295,2831,3626,2466,4095,4095,238,1620,4589,5496,3635,1927,1235,735}()),
    LIMB_ADD_mk{3853,3248,3295,2831,3626,2466,4095,4095,238,243,847,800,1264,469,1629,0,0,0,0,0,0,0,0,0,0,0,239,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3253,2827,1588,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3254,2827,1588,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3254,2827,1588,356,1469,1525,499,801,616,3352,3268,3105,232,1934,219,0,0,239}(LIMB_SQUARE_mk{3254,2827,1588,356,1469,1525,499,801,616,2585,4492,4475,2193}(), LIMB_MULTIPLY_mk{356,1469,1525,499,801,616,3254,2827,1588,3352,3268,3105,232,1934,219,0,0,239,282,1412,2363,2019,1572,1236,736}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,239,3351,3268,3105,232,1934,219,0,0,0,3352,3268,3105,232,1934,219,0,0,239,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_241 (): CUBE_ROOT_FRAC32(241, 0x391c, 0x0cb3) =
  CUBE_ROOT_FRAC32_mk{241,14620,3251,0,28,57,6,3251,448,1593,3252,448,1593,1963,1876,1812,761,3352,2659,4095,4095,240,2133,2219,2283,3334,743,1436,0,0,0,3392,595,1337,1968,2882,422,0,0,241,3391,595,1337,1968,2882,422,0,0,0}(
    LIMB_CUBE_mk{3251,448,1593,1321,3220,3709,401,2574,619,1963,1876,1812,761,3352,2659,4095,4095,240}(LIMB_SQUARE_mk{3251,448,1593,1321,3220,3709,401,2574,619,2580,711,2577,349}(), LIMB_MULTIPLY_mk{1321,3220,3709,401,2574,619,3251,448,1593,1963,1876,1812,761,3352,2659,4095,4095,240,1048,2700,3810,1977,3529,929,1068}()),
    LIMB_ADD_mk{1963,1876,1812,761,3352,2659,4095,4095,240,2133,2219,2283,3334,743,1436,0,0,0,0,0,0,0,0,0,0,0,241,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3251,448,1593,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3252,448,1593,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3252,448,1593,3728,21,2800,402,2574,619,3392,595,1337,1968,2882,422,0,0,241}(LIMB_SQUARE_mk{3252,448,1593,3728,21,2800,402,2574,619,2581,712,2578,349}(), LIMB_MULTIPLY_mk{3728,21,2800,402,2574,619,3252,448,1593,3392,595,1337,1968,2882,422,0,0,241,2959,425,3675,634,3176,930,1069}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,241,3391,595,1337,1968,2882,422,0,0,0,3392,595,1337,1968,2882,422,0,0,241,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_251 (): CUBE_ROOT_FRAC32(251, 0x4ed8, 0xaa4a) =
  CUBE_ROOT_FRAC32_mk{251,20184,43594,10,216,78,6,2634,3466,1614,2635,3466,1614,1768,1974,2885,821,2026,2400,4095,4095,250,2328,2121,1210,3274,2069,1695,0,0,0,3571,1927,1252,1588,1852,214,0,0,251,3570,1927,1252,1588,1852,214,0,0,0}(
    LIMB_CUBE_mk{2634,3466,1614,3428,613,3302,2985,2672,636,1768,1974,2885,821,2026,2400,4095,4095,250}(LIMB_SQUARE_mk{2634,3466,1614,3428,613,3302,2985,2672,636,1693,4458,5009,2732}(), LIMB_MULTIPLY_mk{3428,613,3302,2985,2672,636,2634,3466,1614,1768,1974,2885,821,2026,2400,4095,4095,250,2204,3295,3993,4956,5546,3847,1591}()),
    LIMB_ADD_mk{1768,1974,2885,821,2026,2400,4095,4095,250,2328,2121,1210,3274,2069,1695,0,0,0,0,0,0,0,0,0,0,0,251,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2634,3466,1614,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2635,3466,1614,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2635,3466,1614,505,3451,2435,2986,2672,636,3571,1927,1252,1588,1852,214,0,0,251}(LIMB_SQUARE_mk{2635,3466,1614,505,3451,2435,2986,2672,636,1695,4459,5010,2732}(), LIMB_MULTIPLY_mk{505,3451,2435,2986,2672,636,2635,3466,1614,3571,1927,1252,1588,1852,214,0,0,251,324,2647,4686,5342,5206,3848,1592}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,251,3570,1927,1252,1588,1852,214,0,0,0,3571,1927,1252,1588,1852,214,0,0,251,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_257 (): CUBE_ROOT_FRAC32(257, 0x5b9c, 0xca4f) =
  CUBE_ROOT_FRAC32_mk{257,23452,51791,12,156,91,6,2639,2508,1627,2640,2508,1627,1007,2642,3363,3828,482,3191,4095,4095,256,3089,1453,732,267,3613,904,0,0,0,0,3933,3652,3744,1609,1035,0,0,257,4095,3932,3652,3744,1609,1035,0,0,0}(
    LIMB_CUBE_mk{2639,2508,1627,1121,652,3930,1336,3106,646,1007,2642,3363,3828,482,3191,4095,4095,256}(LIMB_SQUARE_mk{2639,2508,1627,1121,652,3930,1336,3106,646,1700,3232,3632,1993}(), LIMB_MULTIPLY_mk{1121,652,3930,1336,3106,646,2639,2508,1627,1007,2642,3363,3828,482,3191,4095,4095,256,722,1106,3376,3526,4381,2849,1629}()),
    LIMB_ADD_mk{1007,2642,3363,3828,482,3191,4095,4095,256,3089,1453,732,267,3613,904,0,0,0,0,0,0,0,0,0,0,0,257,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2639,2508,1627,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2640,2508,1627,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2640,2508,1627,2304,1573,3089,1337,3106,646,0,3933,3652,3744,1609,1035,0,0,257}(LIMB_SQUARE_mk{2640,2508,1627,2304,1573,3089,1337,3106,646,1701,3233,3633,1993}(), LIMB_MULTIPLY_mk{2304,1573,3089,1337,3106,646,2640,2508,1627,0,3933,3652,3744,1609,1035,0,0,257,1485,2424,3869,3378,4048,2850,1630}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,257,4095,3932,3652,3744,1609,1035,0,0,0,0,3933,3652,3744,1609,1035,0,0,257,1,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_263 (): CUBE_ROOT_FRAC32(263, 0x682e, 0x6ff3) =
  CUBE_ROOT_FRAC32_mk{263,26670,28659,6,46,104,6,4083,742,1640,4084,742,1640,1899,3964,2844,1129,2174,2443,4095,4095,262,2197,131,1251,2966,1921,1652,0,0,0,2368,1487,4074,1263,3639,317,0,0,263,2367,1487,4074,1263,3639,317,0,0,0}(
    LIMB_CUBE_mk{4083,742,1640,169,1162,1500,44,3219,656,1899,3964,2844,1129,2174,2443,4095,4095,262}(LIMB_SQUARE_mk{4083,742,1640,169,1162,1500,44,3219,656,4070,1480,3404,595}(), LIMB_MULTIPLY_mk{169,1162,1500,44,3219,656,4083,742,1640,1899,3964,2844,1129,2174,2443,4095,4095,262,168,1188,1773,781,3817,1255,1407}()),
    LIMB_ADD_mk{1899,3964,2844,1129,2174,2443,4095,4095,262,2197,131,1251,2966,1921,1652,0,0,0,0,0,0,0,0,0,0,0,263,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{4083,742,1640,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4084,742,1640,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{4084,742,1640,144,2648,684,45,3219,656,2368,1487,4074,1263,3639,317,0,0,263}(LIMB_SQUARE_mk{4084,742,1640,144,2648,684,45,3219,656,4072,1480,3405,595}(), LIMB_MULTIPLY_mk{144,2648,684,45,3219,656,4084,742,1640,2368,1487,4074,1263,3639,317,0,0,263,143,2666,1219,1229,3491,1256,1408}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,263,2367,1487,4074,1263,3639,317,0,0,0,2368,1487,4074,1263,3639,317,0,0,263,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_269 (): CUBE_ROOT_FRAC32(269, 0x748f, 0x82ee) =
  CUBE_ROOT_FRAC32_mk{269,29839,33518,8,143,116,6,750,2296,1652,751,2296,1652,3384,4084,523,2219,182,3362,4095,4095,268,712,11,3572,1876,3913,733,0,0,0,1487,985,3860,280,1052,1266,0,0,269,1486,985,3860,280,1052,1266,0,0,0}(
    LIMB_CUBE_mk{750,2296,1652,1348,3497,824,2084,3020,666,3384,4084,523,2219,182,3362,4095,4095,268}(LIMB_SQUARE_mk{750,2296,1652,1348,3497,824,2084,3020,666,137,840,1892,1852}(), LIMB_MULTIPLY_mk{1348,3497,824,2084,3020,666,750,2296,1652,3384,4084,523,2219,182,3362,4095,4095,268,246,1395,2655,2254,2054,2655,1591}()),
    LIMB_ADD_mk{3384,4084,523,2219,182,3362,4095,4095,268,712,11,3572,1876,3913,733,0,0,0,0,0,0,0,0,0,0,0,269,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{750,2296,1652,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,751,2296,1652,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{751,2296,1652,2849,3993,33,2085,3020,666,1487,985,3860,280,1052,1266,0,0,269}(LIMB_SQUARE_mk{751,2296,1652,2849,3993,33,2085,3020,666,137,841,1893,1852}(), LIMB_MULTIPLY_mk{2849,3993,33,2085,3020,666,751,2296,1652,1487,985,3860,280,1052,1266,0,0,269,522,2329,3393,2012,1736,2656,1592}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,269,1486,985,3860,280,1052,1266,0,0,0,1487,985,3860,280,1052,1266,0,0,269,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_271 (): CUBE_ROOT_FRAC32(271, 0x78a5, 0x636f) =
  CUBE_ROOT_FRAC32_mk{271,30885,25455,6,165,120,6,879,2646,1656,880,2646,1656,1871,2802,2621,2557,836,3569,4095,4095,270,2225,1293,1474,1538,3259,526,0,0,0,0,3047,3538,59,1305,1483,0,0,271,4095,3046,3538,59,1305,1483,0,0,0}(
    LIMB_CUBE_mk{879,2646,1656,2593,2896,1379,532,156,670,1871,2802,2621,2557,836,3569,4095,4095,270}(LIMB_SQUARE_mk{879,2646,1656,2593,2896,1379,532,156,670,188,1135,2420,2140}(), LIMB_MULTIPLY_mk{2593,2896,1379,532,156,670,879,2646,1656,1871,2802,2621,2557,836,3569,4095,4095,270,556,2296,3215,2176,935,459,495}()),
    LIMB_ADD_mk{1871,2802,2621,2557,836,3569,4095,4095,270,2225,1293,1474,1538,3259,526,0,0,0,0,0,0,0,0,0,0,0,271,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{879,2646,1656,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,880,2646,1656,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{880,2646,1656,256,4093,596,533,156,670,0,3047,3538,59,1305,1483,0,0,271}(LIMB_SQUARE_mk{880,2646,1656,256,4093,596,533,156,670,189,1136,2421,2140}(), LIMB_MULTIPLY_mk{256,4093,596,533,156,670,880,2646,1656,0,3047,3538,59,1305,1483,0,0,271,55,1044,2875,2155,619,460,496}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,271,4095,3046,3538,59,1305,1483,0,0,0,0,3047,3538,59,1305,1483,0,0,271,1,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_277 (): CUBE_ROOT_FRAC32(277, 0x84c8, 0x7814) =
  CUBE_ROOT_FRAC32_mk{277,33992,30740,7,200,132,6,2068,3207,1668,2069,3207,1668,3904,2857,2970,1454,3051,2805,4095,4095,276,192,1238,1125,2641,1044,1290,0,0,0,3117,3140,143,1156,1722,749,0,0,277,3116,3140,143,1156,1722,749,0,0,0}(
    LIMB_CUBE_mk{2068,3207,1668,400,2348,119,3996,3652,679,3904,2857,2970,1454,3051,2805,4095,4095,276}(LIMB_SQUARE_mk{2068,3207,1668,400,2348,119,3996,3652,679,1044,3238,4196,2612}(), LIMB_MULTIPLY_mk{400,2348,119,3996,3652,679,2068,3207,1668,3904,2857,2970,1454,3051,2805,4095,4095,276,201,1498,2061,3067,5021,4830,2019}()),
    LIMB_ADD_mk{3904,2857,2970,1454,3051,2805,4095,4095,276,192,1238,1125,2641,1044,1290,0,0,0,0,0,0,0,0,0,0,0,277,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2068,3207,1668,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2069,3207,1668,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2069,3207,1668,441,571,3457,3996,3652,679,3117,3140,143,1156,1722,749,0,0,277}(LIMB_SQUARE_mk{2069,3207,1668,441,571,3457,3996,3652,679,1045,3240,4196,2612}(), LIMB_MULTIPLY_mk{441,571,3457,3996,3652,679,2069,3207,1668,3117,3140,143,1156,1722,749,0,0,277,222,633,2373,4958,6382,4831,2020}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,277,3116,3140,143,1156,1722,749,0,0,0,3117,3140,143,1156,1722,749,0,0,277,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_281 (): CUBE_ROOT_FRAC32(281, 0x8cc7, 0x0208) =
  CUBE_ROOT_FRAC32_mk{281,36039,520,0,199,140,6,520,3184,1676,521,3184,1676,512,2584,61,1946,2894,3883,4095,4095,280,3584,1511,4034,2149,1201,212,0,0,0,2265,1326,2717,2329,3977,1846,0,0,281,2264,1326,2717,2329,3977,1846,0,0,0}(
    LIMB_CUBE_mk{520,3184,1676,64,1858,3304,1492,1726,686,512,2584,61,1946,2894,3883,4095,4095,280}(LIMB_SQUARE_mk{520,3184,1676,64,1858,3304,1492,1726,686,66,808,2900,2606}(), LIMB_MULTIPLY_mk{64,1858,3304,1492,1726,686,520,3184,1676,512,2584,61,1946,2894,3883,4095,4095,280,8,285,1890,3518,2731,2039,1239}()),
    LIMB_ADD_mk{512,2584,61,1946,2894,3883,4095,4095,280,3584,1511,4034,2149,1201,212,0,0,0,0,0,0,0,0,0,0,0,281,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{520,3184,1676,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,521,3184,1676,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{521,3184,1676,1105,34,2562,1493,1726,686,2265,1326,2717,2329,3977,1846,0,0,281}(LIMB_SQUARE_mk{521,3184,1676,1105,34,2562,1493,1726,686,66,810,2901,2606}(), LIMB_MULTIPLY_mk{1105,34,2562,1493,1726,686,521,3184,1676,2265,1326,2717,2329,3977,1846,0,0,281,140,863,804,2195,2428,2040,1240}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,281,2264,1326,2717,2329,3977,1846,0,0,0,2265,1326,2717,2329,3977,1846,0,0,281,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_283 (): CUBE_ROOT_FRAC32(283, 0x90be, 0xfffa) =
  CUBE_ROOT_FRAC32_mk{283,37054,65530,15,190,144,6,4090,3055,1680,4091,3055,1680,3880,2367,784,987,4081,3809,4095,4095,282,216,1728,3311,3108,14,286,0,0,0,3971,3919,3431,2181,83,1783,0,0,283,3970,3919,3431,2181,83,1783,0,0,0}(
    LIMB_CUBE_mk{4090,3055,1680,36,192,567,1763,2763,689,3880,2367,784,987,4081,3809,4095,4095,282}(LIMB_SQUARE_mk{4090,3055,1680,36,192,567,1763,2763,689,4084,6102,5635,2507}(), LIMB_MULTIPLY_mk{36,192,567,1763,2763,689,4090,3055,1680,3880,2367,784,987,4081,3809,4095,4095,282,35,218,724,2262,4306,3472,1647}()),
    LIMB_ADD_mk{3880,2367,784,987,4081,3809,4095,4095,282,216,1728,3311,3108,14,286,0,0,0,0,0,0,0,0,0,0,0,283,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{4090,3055,1680,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4091,3055,1680,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{4091,3055,1680,25,2208,3928,1763,2763,689,3971,3919,3431,2181,83,1783,0,0,283}(LIMB_SQUARE_mk{4091,3055,1680,25,2208,3928,1763,2763,689,4086,6103,5635,2507}(), LIMB_MULTIPLY_mk{25,2208,3928,1763,2763,689,4091,3055,1680,3971,3919,3431,2181,83,1783,0,0,283,24,2223,5580,5597,5687,3473,1648}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,283,3970,3919,3431,2181,83,1783,0,0,0,3971,3919,3431,2181,83,1783,0,0,283,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_293 (): CUBE_ROOT_FRAC32(293, 0xa450, 0x6ceb) =
  CUBE_ROOT_FRAC32_mk{293,42064,27883,6,80,164,6,3307,1286,1700,3308,1286,1700,2771,3266,3732,2213,2138,2255,4095,4095,292,1325,829,363,1882,1957,1840,0,0,0,192,1581,653,1183,15,277,0,0,293,191,1581,653,1183,15,277,0,0,0}(
    LIMB_CUBE_mk{3307,1286,1700,4025,881,1369,1021,3388,705,2771,3266,3732,2213,2138,2255,4095,4095,292}(LIMB_SQUARE_mk{3307,1286,1700,4025,881,1369,1021,3388,705,2669,2077,3149,1068}(), LIMB_MULTIPLY_mk{4025,881,1369,1021,3388,705,3307,1286,1700,2771,3266,3732,2213,2138,2255,4095,4095,292,3249,1975,3052,1620,3624,2057,1627}()),
    LIMB_ADD_mk{2771,3266,3732,2213,2138,2255,4095,4095,292,1325,829,363,1882,1957,1840,0,0,0,0,0,0,0,0,0,0,0,293,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{3307,1286,1700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3308,1286,1700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{3308,1286,1700,2448,3455,673,1022,3388,705,192,1581,653,1183,15,277,0,0,293}(LIMB_SQUARE_mk{3308,1286,1700,2448,3455,673,1022,3388,705,2671,2077,3150,1068}(), LIMB_MULTIPLY_mk{2448,3455,673,1022,3388,705,3308,1286,1700,192,1581,653,1183,15,277,0,0,293,1977,3559,2645,2471,3337,2058,1628}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,293,191,1581,653,1183,15,277,0,0,0,192,1581,653,1183,15,277,0,0,293,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_307 (): CUBE_ROOT_FRAC32(307, 0xbef9, 0xa3f7) =
  CUBE_ROOT_FRAC32_mk{307,48889,41975,10,249,190,6,1015,3994,1726,1016,3994,1726,2343,1130,2458,1179,2209,2570,4095,4095,306,1753,2965,1637,2916,1886,1525,0,0,0,3584,2991,737,3600,3874,658,0,0,307,3583,2991,737,3600,3874,658,0,0,0}(
    LIMB_CUBE_mk{1015,3994,1726,2129,2087,1795,806,555,728,2343,1130,2458,1179,2209,2570,4095,4095,306}(LIMB_SQUARE_mk{1015,3994,1726,2129,2087,1795,806,555,728,251,1979,4750,3367}(), LIMB_MULTIPLY_mk{2129,2087,1795,806,555,728,1015,3994,1726,2343,1130,2458,1179,2209,2570,4095,4095,306,527,2593,3377,2830,1680,1061,943}()),
    LIMB_ADD_mk{2343,1130,2458,1179,2209,2570,4095,4095,306,1753,2965,1637,2916,1886,1525,0,0,0,0,0,0,0,0,0,0,0,307,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{1015,3994,1726,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1016,3994,1726,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{1016,3994,1726,64,1884,1153,807,555,728,3584,2991,737,3600,3874,658,0,0,307}(LIMB_SQUARE_mk{1016,3994,1726,64,1884,1153,807,555,728,252,1981,4751,3367}(), LIMB_MULTIPLY_mk{64,1884,1153,807,555,728,1016,3994,1726,3584,2991,737,3600,3874,658,0,0,307,15,529,2150,2118,1410,1062,944}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,307,3583,2991,737,3600,3874,658,0,0,0,3584,2991,737,3600,3874,658,0,0,307,0,0,0,0,0,0,0,0,0,1}())

prfn cube_root_of_311 (): CUBE_ROOT_FRAC32(311, 0xc671, 0x78f2) =
  CUBE_ROOT_FRAC32_mk{311,50801,30962,7,113,198,6,2290,1815,1734,2291,1815,1734,328,2430,2335,4060,1693,2138,4095,4095,310,3768,1665,1760,35,2402,1957,0,0,0,2667,1081,3191,704,3086,245,0,0,311,2666,1081,3191,704,3086,245,0,0,0}(
    LIMB_CUBE_mk{2290,1815,1734,1220,3196,2646,1611,1829,734,328,2430,2335,4060,1693,2138,4095,4095,310}(LIMB_SQUARE_mk{2290,1815,1734,1220,3196,2646,1611,1829,734,1280,2029,2743,1537}(), LIMB_MULTIPLY_mk{1220,3196,2646,1611,1829,734,2290,1815,1734,328,2430,2335,4060,1693,2138,4095,4095,310,682,2327,3412,3426,2857,1903,1099}()),
    LIMB_ADD_mk{328,2430,2335,4060,1693,2138,4095,4095,310,3768,1665,1760,35,2402,1957,0,0,0,0,0,0,0,0,0,0,0,311,1,1,1,1,1,1,1,1,0,0}(),
    LIMB_ADD_mk{2290,1815,1734,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2291,1815,1734,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_CUBE_mk{2291,1815,1734,1705,2731,2019,1612,1829,734,2667,1081,3191,704,3086,245,0,0,311}(LIMB_SQUARE_mk{2291,1815,1734,1705,2731,2019,1612,1829,734,1281,2030,2744,1537}(), LIMB_MULTIPLY_mk{1705,2731,2019,1612,1829,734,2291,1815,1734,2667,1081,3191,704,3086,245,0,0,311,953,2283,3061,2953,2592,1904,1100}()),
    LIMB_ADD_mk{0,0,0,0,0,0,0,0,311,2666,1081,3191,704,3086,245,0,0,0,2667,1081,3191,704,3086,245,0,0,311,0,0,0,0,0,0,0,0,0,1}())

prfn square_root_of_2 (): SQUARE_ROOT_FRAC30(2, 0x5a82, 0x7999) =
  SQUARE_ROOT_FRAC30_mk{2,23170,31129,7,130,2457,2087,90,2458,2087,90,3441,607,3917,4095,4095,1,655,3488,178,0,0,0,164,687,2,0,0,2,163,687,2,0,0,0}(
    LIMB_SQUARE_mk{2457,2087,90,3441,607,3917,4095,4095,1,1473,2504,1171,91}(),
    LIMB_ADD_mk{3441,607,3917,4095,4095,1,0,0,0,655,3488,178,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,1,1,1,1,0,0,0,0,0}(),
    LIMB_ADD_mk{2457,2087,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2458,2087,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_SQUARE_mk{2458,2087,90,164,687,2,0,0,2,1475,2505,1172,92}(),
    LIMB_ADD_mk{0,0,0,0,0,2,0,0,0,163,687,2,0,0,0,0,0,0,164,687,2,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,1}())

prfn square_root_of_3 (): SQUARE_ROOT_FRAC30(3, 0x6ed9, 0xeba1) =
  SQUARE_ROOT_FRAC30_mk{3,28377,60321,14,217,2977,3486,110,2978,3486,110,2881,3375,4011,4095,4095,2,1215,720,84,0,0,0,644,2157,137,0,0,3,643,2157,137,0,0,0}(
    LIMB_SQUARE_mk{2977,3486,110,2881,3375,4011,4095,4095,2,2163,5067,3127,187}(),
    LIMB_ADD_mk{2881,3375,4011,4095,4095,2,0,0,0,1215,720,84,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,1,1,1,1,1,0,0,0,0,0}(),
    LIMB_ADD_mk{2977,3486,110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2978,3486,110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_SQUARE_mk{2978,3486,110,644,2157,137,0,0,3,2165,5069,3128,188}(),
    LIMB_ADD_mk{0,0,0,0,0,3,0,0,0,643,2157,137,0,0,0,0,0,0,644,2157,137,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,1}())

prfn square_root_of_5 (): SQUARE_ROOT_FRAC30(5, 0x8f1b, 0xbcdc) =
  SQUARE_ROOT_FRAC30_mk{5,36635,48348,11,27,3292,443,143,3293,443,143,3344,3005,3881,4095,4095,4,752,1090,214,0,0,0,1737,3893,71,0,0,5,1736,3893,71,0,0,0}(
    LIMB_SQUARE_mk{3292,443,143,3344,3005,3881,4095,4095,4,2645,712,277,30}(),
    LIMB_ADD_mk{3344,3005,3881,4095,4095,4,0,0,0,752,1090,214,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,1,1,1,1,1,0,0,0,0,0}(),
    LIMB_ADD_mk{3292,443,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3293,443,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_SQUARE_mk{3293,443,143,1737,3893,71,0,0,5,2647,712,278,31}(),
    LIMB_ADD_mk{0,0,0,0,0,5,0,0,0,1736,3893,71,0,0,0,0,0,0,1737,3893,71,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,1}())

prfn square_root_of_10 (): SQUARE_ROOT_FRAC30(10, 0xca62, 0xc1d6) =
  SQUARE_ROOT_FRAC30_mk{10,51810,49622,12,98,470,1580,202,471,1580,202,3812,2501,3762,4095,4095,9,284,1594,333,0,0,0,657,1566,71,0,0,10,656,1566,71,0,0,0}(
    LIMB_SQUARE_mk{470,1580,202,3812,2501,3762,4095,4095,9,53,362,655,155}(),
    LIMB_ADD_mk{3812,2501,3762,4095,4095,9,0,0,0,284,1594,333,0,0,0,0,0,0,0,0,0,0,0,10,0,0,0,1,1,1,1,1,0,0,0,0,0}(),
    LIMB_ADD_mk{470,1580,202,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,471,1580,202,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1}(),
    LIMB_SQUARE_mk{471,1580,202,657,1566,71,0,0,10,54,363,656,156}(),
    LIMB_ADD_mk{0,0,0,0,0,10,0,0,0,656,1566,71,0,0,0,0,0,0,657,1566,71,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,1}())

(* END generated by scripts/gen-roots.py *)

(* SHA256_K(t, high, low): the constant K_t of SHA-256 (section 4.2.2) is
   the word high:low. The standard defines the 64 constants as the first 32
   bits of the fractional parts of the cube roots of the first 64 primes; the
   table states them as the standard prints them, and the compiler checks
   that the rounds use the table's word for round t and no other. That each is
   what the definition says is NOT proved: the proof needs integers of 2 to
   the 100, which the 32-bit solver cannot hold. It is tested only through
   the digests that depend on every word of it (tests/dynamic/vectors,
   digest and proved, against the standard's vectors and hashlib), not
   against the integer cube roots word by word, and owed (sha256 issue 31). *)
#pub dataprop SHA256_K(int, int, int) =
  | SHA256_K_0(0, 0x428a, 0x2f98) of CUBE_ROOT_FRAC32(2, 0x428a, 0x2f98)
  | SHA256_K_1(1, 0x7137, 0x4491) of CUBE_ROOT_FRAC32(3, 0x7137, 0x4491)
  | SHA256_K_2(2, 0xb5c0, 0xfbcf) of CUBE_ROOT_FRAC32(5, 0xb5c0, 0xfbcf)
  | SHA256_K_3(3, 0xe9b5, 0xdba5) of CUBE_ROOT_FRAC32(7, 0xe9b5, 0xdba5)
  | SHA256_K_4(4, 0x3956, 0xc25b) of CUBE_ROOT_FRAC32(11, 0x3956, 0xc25b)
  | SHA256_K_5(5, 0x59f1, 0x11f1) of CUBE_ROOT_FRAC32(13, 0x59f1, 0x11f1)
  | SHA256_K_6(6, 0x923f, 0x82a4) of CUBE_ROOT_FRAC32(17, 0x923f, 0x82a4)
  | SHA256_K_7(7, 0xab1c, 0x5ed5) of CUBE_ROOT_FRAC32(19, 0xab1c, 0x5ed5)
  | SHA256_K_8(8, 0xd807, 0xaa98) of CUBE_ROOT_FRAC32(23, 0xd807, 0xaa98)
  | SHA256_K_9(9, 0x1283, 0x5b01) of CUBE_ROOT_FRAC32(29, 0x1283, 0x5b01)
  | SHA256_K_10(10, 0x2431, 0x85be) of CUBE_ROOT_FRAC32(31, 0x2431, 0x85be)
  | SHA256_K_11(11, 0x550c, 0x7dc3) of CUBE_ROOT_FRAC32(37, 0x550c, 0x7dc3)
  | SHA256_K_12(12, 0x72be, 0x5d74) of CUBE_ROOT_FRAC32(41, 0x72be, 0x5d74)
  | SHA256_K_13(13, 0x80de, 0xb1fe) of CUBE_ROOT_FRAC32(43, 0x80de, 0xb1fe)
  | SHA256_K_14(14, 0x9bdc, 0x06a7) of CUBE_ROOT_FRAC32(47, 0x9bdc, 0x06a7)
  | SHA256_K_15(15, 0xc19b, 0xf174) of CUBE_ROOT_FRAC32(53, 0xc19b, 0xf174)
  | SHA256_K_16(16, 0xe49b, 0x69c1) of CUBE_ROOT_FRAC32(59, 0xe49b, 0x69c1)
  | SHA256_K_17(17, 0xefbe, 0x4786) of CUBE_ROOT_FRAC32(61, 0xefbe, 0x4786)
  | SHA256_K_18(18, 0x0fc1, 0x9dc6) of CUBE_ROOT_FRAC32(67, 0x0fc1, 0x9dc6)
  | SHA256_K_19(19, 0x240c, 0xa1cc) of CUBE_ROOT_FRAC32(71, 0x240c, 0xa1cc)
  | SHA256_K_20(20, 0x2de9, 0x2c6f) of CUBE_ROOT_FRAC32(73, 0x2de9, 0x2c6f)
  | SHA256_K_21(21, 0x4a74, 0x84aa) of CUBE_ROOT_FRAC32(79, 0x4a74, 0x84aa)
  | SHA256_K_22(22, 0x5cb0, 0xa9dc) of CUBE_ROOT_FRAC32(83, 0x5cb0, 0xa9dc)
  | SHA256_K_23(23, 0x76f9, 0x88da) of CUBE_ROOT_FRAC32(89, 0x76f9, 0x88da)
  | SHA256_K_24(24, 0x983e, 0x5152) of CUBE_ROOT_FRAC32(97, 0x983e, 0x5152)
  | SHA256_K_25(25, 0xa831, 0xc66d) of CUBE_ROOT_FRAC32(101, 0xa831, 0xc66d)
  | SHA256_K_26(26, 0xb003, 0x27c8) of CUBE_ROOT_FRAC32(103, 0xb003, 0x27c8)
  | SHA256_K_27(27, 0xbf59, 0x7fc7) of CUBE_ROOT_FRAC32(107, 0xbf59, 0x7fc7)
  | SHA256_K_28(28, 0xc6e0, 0x0bf3) of CUBE_ROOT_FRAC32(109, 0xc6e0, 0x0bf3)
  | SHA256_K_29(29, 0xd5a7, 0x9147) of CUBE_ROOT_FRAC32(113, 0xd5a7, 0x9147)
  | SHA256_K_30(30, 0x06ca, 0x6351) of CUBE_ROOT_FRAC32(127, 0x06ca, 0x6351)
  | SHA256_K_31(31, 0x1429, 0x2967) of CUBE_ROOT_FRAC32(131, 0x1429, 0x2967)
  | SHA256_K_32(32, 0x27b7, 0x0a85) of CUBE_ROOT_FRAC32(137, 0x27b7, 0x0a85)
  | SHA256_K_33(33, 0x2e1b, 0x2138) of CUBE_ROOT_FRAC32(139, 0x2e1b, 0x2138)
  | SHA256_K_34(34, 0x4d2c, 0x6dfc) of CUBE_ROOT_FRAC32(149, 0x4d2c, 0x6dfc)
  | SHA256_K_35(35, 0x5338, 0x0d13) of CUBE_ROOT_FRAC32(151, 0x5338, 0x0d13)
  | SHA256_K_36(36, 0x650a, 0x7354) of CUBE_ROOT_FRAC32(157, 0x650a, 0x7354)
  | SHA256_K_37(37, 0x766a, 0x0abb) of CUBE_ROOT_FRAC32(163, 0x766a, 0x0abb)
  | SHA256_K_38(38, 0x81c2, 0xc92e) of CUBE_ROOT_FRAC32(167, 0x81c2, 0xc92e)
  | SHA256_K_39(39, 0x9272, 0x2c85) of CUBE_ROOT_FRAC32(173, 0x9272, 0x2c85)
  | SHA256_K_40(40, 0xa2bf, 0xe8a1) of CUBE_ROOT_FRAC32(179, 0xa2bf, 0xe8a1)
  | SHA256_K_41(41, 0xa81a, 0x664b) of CUBE_ROOT_FRAC32(181, 0xa81a, 0x664b)
  | SHA256_K_42(42, 0xc24b, 0x8b70) of CUBE_ROOT_FRAC32(191, 0xc24b, 0x8b70)
  | SHA256_K_43(43, 0xc76c, 0x51a3) of CUBE_ROOT_FRAC32(193, 0xc76c, 0x51a3)
  | SHA256_K_44(44, 0xd192, 0xe819) of CUBE_ROOT_FRAC32(197, 0xd192, 0xe819)
  | SHA256_K_45(45, 0xd699, 0x0624) of CUBE_ROOT_FRAC32(199, 0xd699, 0x0624)
  | SHA256_K_46(46, 0xf40e, 0x3585) of CUBE_ROOT_FRAC32(211, 0xf40e, 0x3585)
  | SHA256_K_47(47, 0x106a, 0xa070) of CUBE_ROOT_FRAC32(223, 0x106a, 0xa070)
  | SHA256_K_48(48, 0x19a4, 0xc116) of CUBE_ROOT_FRAC32(227, 0x19a4, 0xc116)
  | SHA256_K_49(49, 0x1e37, 0x6c08) of CUBE_ROOT_FRAC32(229, 0x1e37, 0x6c08)
  | SHA256_K_50(50, 0x2748, 0x774c) of CUBE_ROOT_FRAC32(233, 0x2748, 0x774c)
  | SHA256_K_51(51, 0x34b0, 0xbcb5) of CUBE_ROOT_FRAC32(239, 0x34b0, 0xbcb5)
  | SHA256_K_52(52, 0x391c, 0x0cb3) of CUBE_ROOT_FRAC32(241, 0x391c, 0x0cb3)
  | SHA256_K_53(53, 0x4ed8, 0xaa4a) of CUBE_ROOT_FRAC32(251, 0x4ed8, 0xaa4a)
  | SHA256_K_54(54, 0x5b9c, 0xca4f) of CUBE_ROOT_FRAC32(257, 0x5b9c, 0xca4f)
  | SHA256_K_55(55, 0x682e, 0x6ff3) of CUBE_ROOT_FRAC32(263, 0x682e, 0x6ff3)
  | SHA256_K_56(56, 0x748f, 0x82ee) of CUBE_ROOT_FRAC32(269, 0x748f, 0x82ee)
  | SHA256_K_57(57, 0x78a5, 0x636f) of CUBE_ROOT_FRAC32(271, 0x78a5, 0x636f)
  | SHA256_K_58(58, 0x84c8, 0x7814) of CUBE_ROOT_FRAC32(277, 0x84c8, 0x7814)
  | SHA256_K_59(59, 0x8cc7, 0x0208) of CUBE_ROOT_FRAC32(281, 0x8cc7, 0x0208)
  | SHA256_K_60(60, 0x90be, 0xfffa) of CUBE_ROOT_FRAC32(283, 0x90be, 0xfffa)
  | SHA256_K_61(61, 0xa450, 0x6ceb) of CUBE_ROOT_FRAC32(293, 0xa450, 0x6ceb)
  | SHA256_K_62(62, 0xbef9, 0xa3f7) of CUBE_ROOT_FRAC32(307, 0xbef9, 0xa3f7)
  | SHA256_K_63(63, 0xc671, 0x78f2) of CUBE_ROOT_FRAC32(311, 0xc671, 0x78f2)

(* The constant of round t, with the proof that it is the table's *)
#pub fun sha256_k {t:nat | t < 64} (t: int t)
  : [high,low:nat | high < 65536; low < 65536] (SHA256_K(t, high, low) | @(int high, int low))

implement sha256_k {t} (t) =
  if $AR.lt_g1(t, 32) then
    if $AR.lt_g1(t, 16) then
      if $AR.lt_g1(t, 8) then
        if $AR.lt_g1(t, 4) then
          if $AR.lt_g1(t, 2) then
            if $AR.lt_g1(t, 1) then
              (SHA256_K_0(cube_root_of_2()) | @(0x428a, 0x2f98))
            else
              (SHA256_K_1(cube_root_of_3()) | @(0x7137, 0x4491))
          else
            if $AR.lt_g1(t, 3) then
              (SHA256_K_2(cube_root_of_5()) | @(0xb5c0, 0xfbcf))
            else
              (SHA256_K_3(cube_root_of_7()) | @(0xe9b5, 0xdba5))
        else
          if $AR.lt_g1(t, 6) then
            if $AR.lt_g1(t, 5) then
              (SHA256_K_4(cube_root_of_11()) | @(0x3956, 0xc25b))
            else
              (SHA256_K_5(cube_root_of_13()) | @(0x59f1, 0x11f1))
          else
            if $AR.lt_g1(t, 7) then
              (SHA256_K_6(cube_root_of_17()) | @(0x923f, 0x82a4))
            else
              (SHA256_K_7(cube_root_of_19()) | @(0xab1c, 0x5ed5))
      else
        if $AR.lt_g1(t, 12) then
          if $AR.lt_g1(t, 10) then
            if $AR.lt_g1(t, 9) then
              (SHA256_K_8(cube_root_of_23()) | @(0xd807, 0xaa98))
            else
              (SHA256_K_9(cube_root_of_29()) | @(0x1283, 0x5b01))
          else
            if $AR.lt_g1(t, 11) then
              (SHA256_K_10(cube_root_of_31()) | @(0x2431, 0x85be))
            else
              (SHA256_K_11(cube_root_of_37()) | @(0x550c, 0x7dc3))
        else
          if $AR.lt_g1(t, 14) then
            if $AR.lt_g1(t, 13) then
              (SHA256_K_12(cube_root_of_41()) | @(0x72be, 0x5d74))
            else
              (SHA256_K_13(cube_root_of_43()) | @(0x80de, 0xb1fe))
          else
            if $AR.lt_g1(t, 15) then
              (SHA256_K_14(cube_root_of_47()) | @(0x9bdc, 0x06a7))
            else
              (SHA256_K_15(cube_root_of_53()) | @(0xc19b, 0xf174))
    else
      if $AR.lt_g1(t, 24) then
        if $AR.lt_g1(t, 20) then
          if $AR.lt_g1(t, 18) then
            if $AR.lt_g1(t, 17) then
              (SHA256_K_16(cube_root_of_59()) | @(0xe49b, 0x69c1))
            else
              (SHA256_K_17(cube_root_of_61()) | @(0xefbe, 0x4786))
          else
            if $AR.lt_g1(t, 19) then
              (SHA256_K_18(cube_root_of_67()) | @(0x0fc1, 0x9dc6))
            else
              (SHA256_K_19(cube_root_of_71()) | @(0x240c, 0xa1cc))
        else
          if $AR.lt_g1(t, 22) then
            if $AR.lt_g1(t, 21) then
              (SHA256_K_20(cube_root_of_73()) | @(0x2de9, 0x2c6f))
            else
              (SHA256_K_21(cube_root_of_79()) | @(0x4a74, 0x84aa))
          else
            if $AR.lt_g1(t, 23) then
              (SHA256_K_22(cube_root_of_83()) | @(0x5cb0, 0xa9dc))
            else
              (SHA256_K_23(cube_root_of_89()) | @(0x76f9, 0x88da))
      else
        if $AR.lt_g1(t, 28) then
          if $AR.lt_g1(t, 26) then
            if $AR.lt_g1(t, 25) then
              (SHA256_K_24(cube_root_of_97()) | @(0x983e, 0x5152))
            else
              (SHA256_K_25(cube_root_of_101()) | @(0xa831, 0xc66d))
          else
            if $AR.lt_g1(t, 27) then
              (SHA256_K_26(cube_root_of_103()) | @(0xb003, 0x27c8))
            else
              (SHA256_K_27(cube_root_of_107()) | @(0xbf59, 0x7fc7))
        else
          if $AR.lt_g1(t, 30) then
            if $AR.lt_g1(t, 29) then
              (SHA256_K_28(cube_root_of_109()) | @(0xc6e0, 0x0bf3))
            else
              (SHA256_K_29(cube_root_of_113()) | @(0xd5a7, 0x9147))
          else
            if $AR.lt_g1(t, 31) then
              (SHA256_K_30(cube_root_of_127()) | @(0x06ca, 0x6351))
            else
              (SHA256_K_31(cube_root_of_131()) | @(0x1429, 0x2967))
  else
    if $AR.lt_g1(t, 48) then
      if $AR.lt_g1(t, 40) then
        if $AR.lt_g1(t, 36) then
          if $AR.lt_g1(t, 34) then
            if $AR.lt_g1(t, 33) then
              (SHA256_K_32(cube_root_of_137()) | @(0x27b7, 0x0a85))
            else
              (SHA256_K_33(cube_root_of_139()) | @(0x2e1b, 0x2138))
          else
            if $AR.lt_g1(t, 35) then
              (SHA256_K_34(cube_root_of_149()) | @(0x4d2c, 0x6dfc))
            else
              (SHA256_K_35(cube_root_of_151()) | @(0x5338, 0x0d13))
        else
          if $AR.lt_g1(t, 38) then
            if $AR.lt_g1(t, 37) then
              (SHA256_K_36(cube_root_of_157()) | @(0x650a, 0x7354))
            else
              (SHA256_K_37(cube_root_of_163()) | @(0x766a, 0x0abb))
          else
            if $AR.lt_g1(t, 39) then
              (SHA256_K_38(cube_root_of_167()) | @(0x81c2, 0xc92e))
            else
              (SHA256_K_39(cube_root_of_173()) | @(0x9272, 0x2c85))
      else
        if $AR.lt_g1(t, 44) then
          if $AR.lt_g1(t, 42) then
            if $AR.lt_g1(t, 41) then
              (SHA256_K_40(cube_root_of_179()) | @(0xa2bf, 0xe8a1))
            else
              (SHA256_K_41(cube_root_of_181()) | @(0xa81a, 0x664b))
          else
            if $AR.lt_g1(t, 43) then
              (SHA256_K_42(cube_root_of_191()) | @(0xc24b, 0x8b70))
            else
              (SHA256_K_43(cube_root_of_193()) | @(0xc76c, 0x51a3))
        else
          if $AR.lt_g1(t, 46) then
            if $AR.lt_g1(t, 45) then
              (SHA256_K_44(cube_root_of_197()) | @(0xd192, 0xe819))
            else
              (SHA256_K_45(cube_root_of_199()) | @(0xd699, 0x0624))
          else
            if $AR.lt_g1(t, 47) then
              (SHA256_K_46(cube_root_of_211()) | @(0xf40e, 0x3585))
            else
              (SHA256_K_47(cube_root_of_223()) | @(0x106a, 0xa070))
    else
      if $AR.lt_g1(t, 56) then
        if $AR.lt_g1(t, 52) then
          if $AR.lt_g1(t, 50) then
            if $AR.lt_g1(t, 49) then
              (SHA256_K_48(cube_root_of_227()) | @(0x19a4, 0xc116))
            else
              (SHA256_K_49(cube_root_of_229()) | @(0x1e37, 0x6c08))
          else
            if $AR.lt_g1(t, 51) then
              (SHA256_K_50(cube_root_of_233()) | @(0x2748, 0x774c))
            else
              (SHA256_K_51(cube_root_of_239()) | @(0x34b0, 0xbcb5))
        else
          if $AR.lt_g1(t, 54) then
            if $AR.lt_g1(t, 53) then
              (SHA256_K_52(cube_root_of_241()) | @(0x391c, 0x0cb3))
            else
              (SHA256_K_53(cube_root_of_251()) | @(0x4ed8, 0xaa4a))
          else
            if $AR.lt_g1(t, 55) then
              (SHA256_K_54(cube_root_of_257()) | @(0x5b9c, 0xca4f))
            else
              (SHA256_K_55(cube_root_of_263()) | @(0x682e, 0x6ff3))
      else
        if $AR.lt_g1(t, 60) then
          if $AR.lt_g1(t, 58) then
            if $AR.lt_g1(t, 57) then
              (SHA256_K_56(cube_root_of_269()) | @(0x748f, 0x82ee))
            else
              (SHA256_K_57(cube_root_of_271()) | @(0x78a5, 0x636f))
          else
            if $AR.lt_g1(t, 59) then
              (SHA256_K_58(cube_root_of_277()) | @(0x84c8, 0x7814))
            else
              (SHA256_K_59(cube_root_of_281()) | @(0x8cc7, 0x0208))
        else
          if $AR.lt_g1(t, 62) then
            if $AR.lt_g1(t, 61) then
              (SHA256_K_60(cube_root_of_283()) | @(0x90be, 0xfffa))
            else
              (SHA256_K_61(cube_root_of_293()) | @(0xa450, 0x6ceb))
          else
            if $AR.lt_g1(t, 63) then
              (SHA256_K_62(cube_root_of_307()) | @(0xbef9, 0xa3f7))
            else
              (SHA256_K_63(cube_root_of_311()) | @(0xc671, 0x78f2))

(* SHA256_ROUND(a, b, c, d, e, f, g, h, k, w, new_a, new_e): one round of
   SHA-256 (section 6.2.2 step 3) from the working variables a to h, the
   constant k and the schedule word w:
     T1 = h + BIG_SIGMA_1(e) + Ch(e, f, g) + k + w
     T2 = BIG_SIGMA_0(a) + Maj(a, b, c)
   each sum modulo 2 to the 32, in that order; the new a is T1 + T2 and the
   new e is d + T1. The other variables shift (h = g, g = f, f = e, d = c,
   c = b, b = a), which SHA256_ROUNDS puts in its indices. *)
#pub dataprop SHA256_ROUND(word, word, word, word, word, word, word, word, word, word, word, word) =
  | {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low,k_high,k_low,w_high,w_low,big1_high,big1_low,ch_high,ch_low,sum1_high,sum1_low,sum2_high,sum2_low,sum3_high,sum3_low,t1_high,t1_low,big0_high,big0_low,maj_high,maj_low,t2_high,t2_low,new_a_high,new_a_low,new_e_high,new_e_low:nat}
    SHA256_ROUND_mk(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(f_high, f_low), w32(g_high, g_low), w32(h_high, h_low), w32(k_high, k_low), w32(w_high, w_low), w32(new_a_high, new_a_low), w32(new_e_high, new_e_low)) of (
      BIG_SIGMA_1(e_high, e_low, big1_high, big1_low),
      CH(e_high, e_low, f_high, f_low, g_high, g_low, ch_high, ch_low),
      $AR.ADD32(h_high, h_low, big1_high, big1_low, sum1_high, sum1_low),
      $AR.ADD32(sum1_high, sum1_low, ch_high, ch_low, sum2_high, sum2_low),
      $AR.ADD32(sum2_high, sum2_low, k_high, k_low, sum3_high, sum3_low),
      $AR.ADD32(sum3_high, sum3_low, w_high, w_low, t1_high, t1_low),
      BIG_SIGMA_0(a_high, a_low, big0_high, big0_low),
      MAJ(a_high, a_low, b_high, b_low, c_high, c_low, maj_high, maj_low),
      $AR.ADD32(big0_high, big0_low, maj_high, maj_low, t2_high, t2_low),
      $AR.ADD32(t1_high, t1_low, t2_high, t2_low, new_a_high, new_a_low),
      $AR.ADD32(d_high, d_low, t1_high, t1_low, new_e_high, new_e_low))

(* One round, with the proof that its results are the standard's *)
#pub fun sha256_round {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low,k_high,k_low,w_high,w_low:nat | a_high < 65536; a_low < 65536; b_high < 65536; b_low < 65536; c_high < 65536; c_low < 65536; d_high < 65536; d_low < 65536; e_high < 65536; e_low < 65536; f_high < 65536; f_low < 65536; g_high < 65536; g_low < 65536; h_high < 65536; h_low < 65536; k_high < 65536; k_low < 65536; w_high < 65536; w_low < 65536}
  (a_high: int a_high, a_low: int a_low, b_high: int b_high, b_low: int b_low, c_high: int c_high, c_low: int c_low, d_high: int d_high, d_low: int d_low, e_high: int e_high, e_low: int e_low, f_high: int f_high, f_low: int f_low, g_high: int g_high, g_low: int g_low, h_high: int h_high, h_low: int h_low, k_high: int k_high, k_low: int k_low, w_high: int w_high, w_low: int w_low)
  : [new_a_high,new_a_low,new_e_high,new_e_low:nat | new_a_high < 65536; new_a_low < 65536; new_e_high < 65536; new_e_low < 65536]
    (SHA256_ROUND(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(f_high, f_low), w32(g_high, g_low), w32(h_high, h_low), w32(k_high, k_low), w32(w_high, w_low), w32(new_a_high, new_a_low), w32(new_e_high, new_e_low)) | @(int new_a_high, int new_a_low, int new_e_high, int new_e_low))

implement sha256_round (a_high, a_low, b_high, b_low, c_high, c_low, d_high, d_low, e_high, e_low, f_high, f_low, g_high, g_low, h_high, h_low, k_high, k_low, w_high, w_low) = let
  val (big1 | @(big1_high, big1_low)) = big_sigma_1(e_high, e_low)
  val (choice | @(ch_high, ch_low)) = word_ch(e_high, e_low, f_high, f_low, g_high, g_low)
  val (add1 | @(sum1_high, sum1_low)) = $AR.add32(h_high, h_low, big1_high, big1_low)
  val (add2 | @(sum2_high, sum2_low)) = $AR.add32(sum1_high, sum1_low, ch_high, ch_low)
  val (add3 | @(sum3_high, sum3_low)) = $AR.add32(sum2_high, sum2_low, k_high, k_low)
  val (add4 | @(t1_high, t1_low)) = $AR.add32(sum3_high, sum3_low, w_high, w_low)
  val (big0 | @(big0_high, big0_low)) = big_sigma_0(a_high, a_low)
  val (majority | @(maj_high, maj_low)) = word_maj(a_high, a_low, b_high, b_low, c_high, c_low)
  val (add5 | @(t2_high, t2_low)) = $AR.add32(big0_high, big0_low, maj_high, maj_low)
  val (add6 | @(new_a_high, new_a_low)) = $AR.add32(t1_high, t1_low, t2_high, t2_low)
  val (add7 | @(new_e_high, new_e_low)) = $AR.add32(d_high, d_low, t1_high, t1_low)
in (SHA256_ROUND_mk(big1, choice, add1, add2, add3, add4, big0, majority, add5, add6, add7)
    | @(new_a_high, new_a_low, new_e_high, new_e_low)) end

(* SHA256_ROUNDS(msg, at, t, init, state): after t rounds of the block of 64
   bytes from `at` of the cells msg, begun with the working variables init,
   the working variables are state. Round t uses K_t and the schedule word
   W_t of that block (SCHEDULE), and ends in the state of SHA256_ROUND with
   its registers shifted. *)
#pub dataprop SHA256_ROUNDS($A.cells, int, int, eight_words, eight_words) =
  | {msg:$A.cells}{at:nat}{init:eight_words}
    SHA256_ROUNDS_zero(msg, at, 0, init, init)
  | {msg:$A.cells}{at,t:nat | t < 64}{init:eight_words}
    {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low,k_high,k_low,w_high,w_low,new_a_high,new_a_low,new_e_high,new_e_low:nat}
    SHA256_ROUNDS_next(msg, at, t+1, init,
      eight(w32(new_a_high, new_a_low), w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low),
            w32(new_e_high, new_e_low), w32(e_high, e_low), w32(f_high, f_low), w32(g_high, g_low))) of (
      SHA256_ROUNDS(msg, at, t, init, eight(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(f_high, f_low), w32(g_high, g_low), w32(h_high, h_low))),
      SHA256_K(t, k_high, k_low),
      SCHEDULE(sha256_kind(), msg, at, t, w_high, w_low),
      SHA256_ROUND(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(f_high, f_low), w32(g_high, g_low), w32(h_high, h_low), w32(k_high, k_low), w32(w_high, w_low), w32(new_a_high, new_a_low), w32(new_e_high, new_e_low)))

(* SHA256_BLOCK(msg, at, before, after): the block of 64 bytes from `at` of
   msg, hashed onto the chaining value `before` (section 6.2.2), makes the
   chaining value `after`: the 64 rounds begun with the working variables
   a to h set to `before`, and the new chaining value is each working
   variable at the end added (modulo 2 to the 32) to the same word of
   `before` (step 4) *)
#pub dataprop SHA256_BLOCK($A.cells, int, eight_words, eight_words) =
  | {msg:$A.cells}{at:nat}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low,end_a_high,end_a_low,end_b_high,end_b_low,end_c_high,end_c_low,end_d_high,end_d_low,end_e_high,end_e_low,end_f_high,end_f_low,end_g_high,end_g_low,end_h_high,end_h_low,next_h0_high,next_h0_low,next_h1_high,next_h1_low,next_h2_high,next_h2_low,next_h3_high,next_h3_low,next_h4_high,next_h4_low,next_h5_high,next_h5_low,next_h6_high,next_h6_low,next_h7_high,next_h7_low:nat}
    SHA256_BLOCK_mk(msg, at, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low)), eight(w32(next_h0_high, next_h0_low), w32(next_h1_high, next_h1_low), w32(next_h2_high, next_h2_low), w32(next_h3_high, next_h3_low), w32(next_h4_high, next_h4_low), w32(next_h5_high, next_h5_low), w32(next_h6_high, next_h6_low), w32(next_h7_high, next_h7_low))) of (
      SHA256_ROUNDS(msg, at, 64, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low)), eight(w32(end_a_high, end_a_low), w32(end_b_high, end_b_low), w32(end_c_high, end_c_low), w32(end_d_high, end_d_low), w32(end_e_high, end_e_low), w32(end_f_high, end_f_low), w32(end_g_high, end_g_low), w32(end_h_high, end_h_low))),
      $AR.ADD32(h0_high, h0_low, end_a_high, end_a_low, next_h0_high, next_h0_low),
      $AR.ADD32(h1_high, h1_low, end_b_high, end_b_low, next_h1_high, next_h1_low),
      $AR.ADD32(h2_high, h2_low, end_c_high, end_c_low, next_h2_high, next_h2_low),
      $AR.ADD32(h3_high, h3_low, end_d_high, end_d_low, next_h3_high, next_h3_low),
      $AR.ADD32(h4_high, h4_low, end_e_high, end_e_low, next_h4_high, next_h4_low),
      $AR.ADD32(h5_high, h5_low, end_f_high, end_f_low, next_h5_high, next_h5_low),
      $AR.ADD32(h6_high, h6_low, end_g_high, end_g_low, next_h6_high, next_h6_low),
      $AR.ADD32(h7_high, h7_low, end_h_high, end_h_low, next_h7_high, next_h7_low))

(* The 64 rounds, each with the proof that it is the standard's, from the
   working variables a to h after t rounds *)
fun _rounds256 {lw:agz}{words,msg:$A.cells}{at:nat}{init:eight_words}{t:nat | t <= 64}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low:nat | a_high < 65536; a_low < 65536; b_high < 65536; b_low < 65536; c_high < 65536; c_low < 65536; d_high < 65536; d_low < 65536; e_high < 65536; e_low < 65536; f_high < 65536; f_low < 65536; g_high < 65536; g_low < 65536; h_high < 65536; h_low < 65536} .<64 - t>.
  (schedule: !$A.barr(lw, 256, words), listed: SCHEDULE_ARRAY(sha256_kind(), words, msg, at, 64), t: int t,
   a_high: int a_high, a_low: int a_low, b_high: int b_high, b_low: int b_low, c_high: int c_high, c_low: int c_low, d_high: int d_high, d_low: int d_low, e_high: int e_high, e_low: int e_low, f_high: int f_high, f_low: int f_low, g_high: int g_high, g_low: int g_low, h_high: int h_high, h_low: int h_low,
   done: SHA256_ROUNDS(msg, at, t, init, eight(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(f_high, f_low), w32(g_high, g_low), w32(h_high, h_low))))
  : [end_a_high,end_a_low,end_b_high,end_b_low,end_c_high,end_c_low,end_d_high,end_d_low,end_e_high,end_e_low,end_f_high,end_f_low,end_g_high,end_g_low,end_h_high,end_h_low:nat | end_a_high < 65536; end_a_low < 65536; end_b_high < 65536; end_b_low < 65536; end_c_high < 65536; end_c_low < 65536; end_d_high < 65536; end_d_low < 65536; end_e_high < 65536; end_e_low < 65536; end_f_high < 65536; end_f_low < 65536; end_g_high < 65536; end_g_low < 65536; end_h_high < 65536; end_h_low < 65536]
    (SHA256_ROUNDS(msg, at, 64, init, eight(w32(end_a_high, end_a_low), w32(end_b_high, end_b_low), w32(end_c_high, end_c_low), w32(end_d_high, end_d_low), w32(end_e_high, end_e_low), w32(end_f_high, end_f_low), w32(end_g_high, end_g_low), w32(end_h_high, end_h_low))) | @(int end_a_high, int end_a_low, int end_b_high, int end_b_low, int end_c_high, int end_c_low, int end_d_high, int end_d_low, int end_e_high, int end_e_low, int end_f_high, int end_f_low, int end_g_high, int end_g_low, int end_h_high, int end_h_low)) =
  if t >= 64 then (done | @(a_high, a_low, b_high, b_low, c_high, c_low, d_high, d_low, e_high, e_low, f_high, f_low, g_high, g_low, h_high, h_low))
  else let
    val (constant | @(k_high, k_low)) = sha256_k(t)
    val (word | @(w_high, w_low)) = _scheduled(schedule, listed, t)
    val (step | @(new_a_high, new_a_low, new_e_high, new_e_low)) =
      sha256_round(a_high, a_low, b_high, b_low, c_high, c_low, d_high, d_low, e_high, e_low, f_high, f_low, g_high, g_low, h_high, h_low, k_high, k_low, w_high, w_low)
  in _rounds256(schedule, listed, t + 1,
       new_a_high, new_a_low, a_high, a_low, b_high, b_low, c_high, c_low,
       new_e_high, new_e_low, e_high, e_low, f_high, f_low, g_high, g_low,
       SHA256_ROUNDS_next(done, constant, word, step)) end

(* The block of 64 bytes from `at` of the message hashed onto the chaining
   value in the array (32 bytes, eight words, at 0) and the new chaining value
   written there, with the proof that it is the standard's. The array
   `schedule` is scratch space for the 64 words of the message schedule. *)
#pub fun sha256_compress {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}
  {lw:agz}{words:$A.cells}{lc:agz}{chain:$A.cells}
  {h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536; h5_high < 65536; h5_low < 65536; h6_high < 65536; h6_low < 65536; h7_high < 65536; h7_low < 65536}
  (message: !$A.barr(lm, nm, msg), at: int at, schedule: $A.barr(lw, 256, words),
   chaining: $A.barr(lc, 32, chain), have: EIGHT_AT(chain, 0, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low))))
  : [words2:$A.cells][chain2:$A.cells][next_h0_high,next_h0_low,next_h1_high,next_h1_low,next_h2_high,next_h2_low,next_h3_high,next_h3_low,next_h4_high,next_h4_low,next_h5_high,next_h5_low,next_h6_high,next_h6_low,next_h7_high,next_h7_low:nat | next_h0_high < 65536; next_h0_low < 65536; next_h1_high < 65536; next_h1_low < 65536; next_h2_high < 65536; next_h2_low < 65536; next_h3_high < 65536; next_h3_low < 65536; next_h4_high < 65536; next_h4_low < 65536; next_h5_high < 65536; next_h5_low < 65536; next_h6_high < 65536; next_h6_low < 65536; next_h7_high < 65536; next_h7_low < 65536]
    (SHA256_BLOCK(msg, at, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low)), eight(w32(next_h0_high, next_h0_low), w32(next_h1_high, next_h1_low), w32(next_h2_high, next_h2_low), w32(next_h3_high, next_h3_low), w32(next_h4_high, next_h4_low), w32(next_h5_high, next_h5_low), w32(next_h6_high, next_h6_low), w32(next_h7_high, next_h7_low))),
     EIGHT_AT(chain2, 0, eight(w32(next_h0_high, next_h0_low), w32(next_h1_high, next_h1_low), w32(next_h2_high, next_h2_low), w32(next_h3_high, next_h3_low), w32(next_h4_high, next_h4_low), w32(next_h5_high, next_h5_low), w32(next_h6_high, next_h6_low), w32(next_h7_high, next_h7_low)))
     | @($A.barr(lw, 256, words2), $A.barr(lc, 32, chain2)))

implement sha256_compress {lm}{nm}{msg}{at}{lw}{words}{lc}{chain}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low}
  (message, at, schedule, chaining, have) = let
  val (listed | schedule) = schedule_sha256(message, at, schedule)
  val @(h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low, h5_high, h5_low, h6_high, h6_low, h7_high, h7_low) = eight_get(chaining, 0, have)
  val (rounds | @(end_a_high, end_a_low, end_b_high, end_b_low, end_c_high, end_c_low, end_d_high, end_d_low, end_e_high, end_e_low, end_f_high, end_f_low, end_g_high, end_g_low, end_h_high, end_h_low)) = _rounds256(schedule, listed, 0,
    h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low, h5_high, h5_low, h6_high, h6_low, h7_high, h7_low, SHA256_ROUNDS_zero())
  val (add0 | @(next_h0_high, next_h0_low)) = $AR.add32(h0_high, h0_low, end_a_high, end_a_low)
  val (add1 | @(next_h1_high, next_h1_low)) = $AR.add32(h1_high, h1_low, end_b_high, end_b_low)
  val (add2 | @(next_h2_high, next_h2_low)) = $AR.add32(h2_high, h2_low, end_c_high, end_c_low)
  val (add3 | @(next_h3_high, next_h3_low)) = $AR.add32(h3_high, h3_low, end_d_high, end_d_low)
  val (add4 | @(next_h4_high, next_h4_low)) = $AR.add32(h4_high, h4_low, end_e_high, end_e_low)
  val (add5 | @(next_h5_high, next_h5_low)) = $AR.add32(h5_high, h5_low, end_f_high, end_f_low)
  val (add6 | @(next_h6_high, next_h6_low)) = $AR.add32(h6_high, h6_low, end_g_high, end_g_low)
  val (add7 | @(next_h7_high, next_h7_low)) = $AR.add32(h7_high, h7_low, end_h_high, end_h_low)
  val (written | chaining) = eight_set(chaining, 0, next_h0_high, next_h0_low, next_h1_high, next_h1_low, next_h2_high, next_h2_low, next_h3_high, next_h3_low, next_h4_high, next_h4_low, next_h5_high, next_h5_low, next_h6_high, next_h6_low, next_h7_high, next_h7_low)
in (SHA256_BLOCK_mk(rounds, add0, add1, add2, add3, add4, add5, add6, add7), written | @(schedule, chaining)) end

(* ============================================================
   SHA-1's rounds (FIPS 180-4, sections 4.1.1, 4.2.1, 5.3.1, 6.1.2)
   ============================================================ *)

(* PARITY(x, y, z, r): r is Parity(x, y, z) = x xor y xor z (section 4.1.1) *)
#pub dataprop PARITY(int, int, int, int, int, int, int, int) =
  | {xh,xl,yh,yl,zh,zl,ah,al,rh,rl:nat}
    PARITY_mk(xh, xl, yh, yl, zh, zl, rh, rl) of (
      $AR.XOR(xh, yh, ah), $AR.XOR(xl, yl, al),
      $AR.XOR(ah, zh, rh), $AR.XOR(al, zl, rl))

(* SHA1_F(t, b, c, d, f): f is f_t(b, c, d) (section 4.1.1): Ch for t from 0
   to 19, Parity from 20 to 39, Maj from 40 to 59, Parity from 60 to 79 *)
#pub dataprop SHA1_F(int, int, int, int, int, int, int, int, int) =
  | {t:nat | t <= 19}{bh,bl,ch,cl,dh,dl,fh,fl:nat}
    SHA1_F_choose(t, bh, bl, ch, cl, dh, dl, fh, fl) of CH(bh, bl, ch, cl, dh, dl, fh, fl)
  | {t:nat | 20 <= t; t <= 39}{bh,bl,ch,cl,dh,dl,fh,fl:nat}
    SHA1_F_parity_first(t, bh, bl, ch, cl, dh, dl, fh, fl) of PARITY(bh, bl, ch, cl, dh, dl, fh, fl)
  | {t:nat | 40 <= t; t <= 59}{bh,bl,ch,cl,dh,dl,fh,fl:nat}
    SHA1_F_majority(t, bh, bl, ch, cl, dh, dl, fh, fl) of MAJ(bh, bl, ch, cl, dh, dl, fh, fl)
  | {t:nat | 60 <= t; t <= 79}{bh,bl,ch,cl,dh,dl,fh,fl:nat}
    SHA1_F_parity_second(t, bh, bl, ch, cl, dh, dl, fh, fl) of PARITY(bh, bl, ch, cl, dh, dl, fh, fl)

(* Parity of three words, with the proof that it is *)
#pub fun word_parity {xh,xl,yh,yl,zh,zl:nat | xh < 65536; xl < 65536; yh < 65536; yl < 65536; zh < 65536; zl < 65536}
  (xh: int xh, xl: int xl, yh: int yh, yl: int yl, zh: int zh, zl: int zl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (PARITY(xh, xl, yh, yl, zh, zl, rh, rl) | @(int rh, int rl))

implement word_parity (xh, xl, yh, yl, zh, zl) = let
  val (pah, pal | @(ah, al)) = $AR.xor32(xh, xl, yh, yl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(ah, al, zh, zl)
in (PARITY_mk(pah, pal, prh, prl) | @(rh, rl)) end

(* f_t(b, c, d), with the proof that it is *)
#pub fun sha1_f {t:nat | t < 80}{bh,bl,ch,cl,dh,dl:nat | bh < 65536; bl < 65536; ch < 65536; cl < 65536; dh < 65536; dl < 65536}
  (t: int t, bh: int bh, bl: int bl, ch: int ch, cl: int cl, dh: int dh, dl: int dl)
  : [fh,fl:nat | fh < 65536; fl < 65536] (SHA1_F(t, bh, bl, ch, cl, dh, dl, fh, fl) | @(int fh, int fl))

implement sha1_f {t}{bh,bl,ch,cl,dh,dl} (t, bh, bl, ch, cl, dh, dl) =
  if $AR.lt_g1(t, 20) then let
    val (pf | @(fh, fl)) = word_ch(bh, bl, ch, cl, dh, dl)
  in (SHA1_F_choose(pf) | @(fh, fl)) end
  else if $AR.lt_g1(t, 40) then let
    val (pf | @(fh, fl)) = word_parity(bh, bl, ch, cl, dh, dl)
  in (SHA1_F_parity_first(pf) | @(fh, fl)) end
  else if $AR.lt_g1(t, 60) then let
    val (pf | @(fh, fl)) = word_maj(bh, bl, ch, cl, dh, dl)
  in (SHA1_F_majority(pf) | @(fh, fl)) end
  else let
    val (pf | @(fh, fl)) = word_parity(bh, bl, ch, cl, dh, dl)
  in (SHA1_F_parity_second(pf) | @(fh, fl)) end

(* SHA1_K(t, high, low): the constant K_t of SHA-1 (section 4.2.1) is the word
   high:low: 5a827999 for t from 0 to 19, 6ed9eba1 from 20 to 39, 8f1bbcdc from
   40 to 59 and ca62c1d6 from 60 to 79. The standard defines them as the
   first 30 bits of the square roots of 2, 3, 5 and 10 times 2 to the 30 (the
   integer part of 2 to the 30 times the root). Like SHA-256's they are stated
   and tested only through the digests that depend on them
   (tests/dynamic/sha1 and proved), not proved against the definition (the
   proof needs integers of 2 to the 61 and more); owed (sha256 issue 31). *)
#pub dataprop SHA1_K(int, int, int) =
  | {t:nat | 0 <= t; t <= 19} SHA1_K_0_to_19(t, 0x5a82, 0x7999) of SQUARE_ROOT_FRAC30(2, 0x5a82, 0x7999)
  | {t:nat | 20 <= t; t <= 39} SHA1_K_20_to_39(t, 0x6ed9, 0xeba1) of SQUARE_ROOT_FRAC30(3, 0x6ed9, 0xeba1)
  | {t:nat | 40 <= t; t <= 59} SHA1_K_40_to_59(t, 0x8f1b, 0xbcdc) of SQUARE_ROOT_FRAC30(5, 0x8f1b, 0xbcdc)
  | {t:nat | 60 <= t; t <= 79} SHA1_K_60_to_79(t, 0xca62, 0xc1d6) of SQUARE_ROOT_FRAC30(10, 0xca62, 0xc1d6)

(* The constant of round t, with the proof that it is the table's *)
#pub fun sha1_k {t:nat | t < 80} (t: int t)
  : [high,low:nat | high < 65536; low < 65536] (SHA1_K(t, high, low) | @(int high, int low))

implement sha1_k {t} (t) =
  if $AR.lt_g1(t, 20) then (SHA1_K_0_to_19(square_root_of_2()) | @(0x5a82, 0x7999))
  else if $AR.lt_g1(t, 40) then (SHA1_K_20_to_39(square_root_of_3()) | @(0x6ed9, 0xeba1))
  else if $AR.lt_g1(t, 60) then (SHA1_K_40_to_59(square_root_of_5()) | @(0x8f1b, 0xbcdc))
  else (SHA1_K_60_to_79(square_root_of_10()) | @(0xca62, 0xc1d6))

(* SHA1_ROUND(t, a, b, c, d, e, k, w, new_a, new_c): round t of SHA-1
   (section 6.1.2 step 3) from the working variables a to e, the constant k
   and the schedule word w:
     T = ROTL 5 (a) + f_t(b, c, d) + e + k + w
   each sum modulo 2 to the 32, in that order; ROTL 5 is ROTR 27 and ROTL 30
   is ROTR 2 (arith has no left rotation; ROTL n = ROTR (32 - n) by the
   standard's definitions of the two). The new a is T and the new c is ROTL 30
   (b); the others shift (e = d, d = c, b = a), which SHA1_ROUNDS puts in its
   indices. *)
#pub dataprop SHA1_ROUND(int, word, word, word, word, word, word, word, word, word) =
  | {t:nat}{a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,k_high,k_low,w_high,w_low,sum1_high,sum1_low,sum2_high,sum2_low,sum3_high,sum3_low,turn5_high,turn5_low,f_high,f_low,new_a_high,new_a_low,new_c_high,new_c_low:nat}
    SHA1_ROUND_mk(t, w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(k_high, k_low), w32(w_high, w_low), w32(new_a_high, new_a_low), w32(new_c_high, new_c_low)) of (
      $AR.ROTR(27, a_high, a_low, turn5_high, turn5_low),
      SHA1_F(t, b_high, b_low, c_high, c_low, d_high, d_low, f_high, f_low),
      $AR.ADD32(turn5_high, turn5_low, f_high, f_low, sum1_high, sum1_low),
      $AR.ADD32(sum1_high, sum1_low, e_high, e_low, sum2_high, sum2_low),
      $AR.ADD32(sum2_high, sum2_low, k_high, k_low, sum3_high, sum3_low),
      $AR.ADD32(sum3_high, sum3_low, w_high, w_low, new_a_high, new_a_low),
      $AR.ROTR(2, b_high, b_low, new_c_high, new_c_low))

(* Round t, with the proof that its results are the standard's *)
#pub fun sha1_round {t:nat | t < 80}{a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,k_high,k_low,w_high,w_low:nat | a_high < 65536; a_low < 65536; b_high < 65536; b_low < 65536; c_high < 65536; c_low < 65536; d_high < 65536; d_low < 65536; e_high < 65536; e_low < 65536; k_high < 65536; k_low < 65536; w_high < 65536; w_low < 65536}
  (t: int t, a_high: int a_high, a_low: int a_low, b_high: int b_high, b_low: int b_low, c_high: int c_high, c_low: int c_low, d_high: int d_high, d_low: int d_low, e_high: int e_high, e_low: int e_low, k_high: int k_high, k_low: int k_low, w_high: int w_high, w_low: int w_low)
  : [new_a_high,new_a_low,new_c_high,new_c_low:nat | new_a_high < 65536; new_a_low < 65536; new_c_high < 65536; new_c_low < 65536]
    (SHA1_ROUND(t, w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(k_high, k_low), w32(w_high, w_low), w32(new_a_high, new_a_low), w32(new_c_high, new_c_low)) | @(int new_a_high, int new_a_low, int new_c_high, int new_c_low))

implement sha1_round (t, a_high, a_low, b_high, b_low, c_high, c_low, d_high, d_low, e_high, e_low, k_high, k_low, w_high, w_low) = let
  val (turn | @(turn5_high, turn5_low)) = $AR.rotr_fast(27, a_high, a_low)
  val (function | @(f_high, f_low)) = sha1_f(t, b_high, b_low, c_high, c_low, d_high, d_low)
  val (add1 | @(sum1_high, sum1_low)) = $AR.add32(turn5_high, turn5_low, f_high, f_low)
  val (add2 | @(sum2_high, sum2_low)) = $AR.add32(sum1_high, sum1_low, e_high, e_low)
  val (add3 | @(sum3_high, sum3_low)) = $AR.add32(sum2_high, sum2_low, k_high, k_low)
  val (add4 | @(new_a_high, new_a_low)) = $AR.add32(sum3_high, sum3_low, w_high, w_low)
  val (turn30 | @(new_c_high, new_c_low)) = $AR.rotr_fast(2, b_high, b_low)
in (SHA1_ROUND_mk(turn, function, add1, add2, add3, add4, turn30)
    | @(new_a_high, new_a_low, new_c_high, new_c_low)) end

(* SHA1_ROUNDS(msg, at, t, init, state): after t rounds of the block of 64
   bytes from `at` of the cells msg, begun with the working variables init,
   the working variables are state (section 6.1.2 step 3) *)
#pub dataprop SHA1_ROUNDS($A.cells, int, int, five_words, five_words) =
  | {msg:$A.cells}{at:nat}{init:five_words}
    SHA1_ROUNDS_zero(msg, at, 0, init, init)
  | {msg:$A.cells}{at,t:nat | t < 80}{init:five_words}
    {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,k_high,k_low,w_high,w_low,new_a_high,new_a_low,new_c_high,new_c_low:nat}
    SHA1_ROUNDS_next(msg, at, t+1, init,
      five(w32(new_a_high, new_a_low), w32(a_high, a_low), w32(new_c_high, new_c_low),
           w32(c_high, c_low), w32(d_high, d_low))) of (
      SHA1_ROUNDS(msg, at, t, init, five(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low))),
      SHA1_K(t, k_high, k_low),
      SCHEDULE(sha1_kind(), msg, at, t, w_high, w_low),
      SHA1_ROUND(t, w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low), w32(k_high, k_low), w32(w_high, w_low), w32(new_a_high, new_a_low), w32(new_c_high, new_c_low)))

(* SHA1_BLOCK(msg, at, before, after): the block of 64 bytes from `at` of msg,
   hashed onto the chaining value `before` (section 6.1.2), makes `after`: the
   80 rounds begun with the working variables a to e set to `before`, and
   each working variable at the end added (modulo 2 to the 32) to the same
   word of `before` (step 4) *)
#pub dataprop SHA1_BLOCK($A.cells, int, five_words, five_words) =
  | {msg:$A.cells}{at:nat}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,end_a_high,end_a_low,end_b_high,end_b_low,end_c_high,end_c_low,end_d_high,end_d_low,end_e_high,end_e_low,next_h0_high,next_h0_low,next_h1_high,next_h1_low,next_h2_high,next_h2_low,next_h3_high,next_h3_low,next_h4_high,next_h4_low:nat}
    SHA1_BLOCK_mk(msg, at, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low)), five(w32(next_h0_high, next_h0_low), w32(next_h1_high, next_h1_low), w32(next_h2_high, next_h2_low), w32(next_h3_high, next_h3_low), w32(next_h4_high, next_h4_low))) of (
      SHA1_ROUNDS(msg, at, 80, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low)), five(w32(end_a_high, end_a_low), w32(end_b_high, end_b_low), w32(end_c_high, end_c_low), w32(end_d_high, end_d_low), w32(end_e_high, end_e_low))),
      $AR.ADD32(h0_high, h0_low, end_a_high, end_a_low, next_h0_high, next_h0_low),
      $AR.ADD32(h1_high, h1_low, end_b_high, end_b_low, next_h1_high, next_h1_low),
      $AR.ADD32(h2_high, h2_low, end_c_high, end_c_low, next_h2_high, next_h2_low),
      $AR.ADD32(h3_high, h3_low, end_d_high, end_d_low, next_h3_high, next_h3_low),
      $AR.ADD32(h4_high, h4_low, end_e_high, end_e_low, next_h4_high, next_h4_low))

(* The 80 rounds, each with the proof that it is the standard's *)
fun _rounds1 {lw:agz}{words,msg:$A.cells}{at:nat}{init:five_words}{t:nat | t <= 80}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low:nat | a_high < 65536; a_low < 65536; b_high < 65536; b_low < 65536; c_high < 65536; c_low < 65536; d_high < 65536; d_low < 65536; e_high < 65536; e_low < 65536} .<80 - t>.
  (schedule: !$A.barr(lw, 320, words), listed: SCHEDULE_ARRAY(sha1_kind(), words, msg, at, 80), t: int t,
   a_high: int a_high, a_low: int a_low, b_high: int b_high, b_low: int b_low, c_high: int c_high, c_low: int c_low, d_high: int d_high, d_low: int d_low, e_high: int e_high, e_low: int e_low,
   done: SHA1_ROUNDS(msg, at, t, init, five(w32(a_high, a_low), w32(b_high, b_low), w32(c_high, c_low), w32(d_high, d_low), w32(e_high, e_low))))
  : [end_a_high,end_a_low,end_b_high,end_b_low,end_c_high,end_c_low,end_d_high,end_d_low,end_e_high,end_e_low:nat | end_a_high < 65536; end_a_low < 65536; end_b_high < 65536; end_b_low < 65536; end_c_high < 65536; end_c_low < 65536; end_d_high < 65536; end_d_low < 65536; end_e_high < 65536; end_e_low < 65536]
    (SHA1_ROUNDS(msg, at, 80, init, five(w32(end_a_high, end_a_low), w32(end_b_high, end_b_low), w32(end_c_high, end_c_low), w32(end_d_high, end_d_low), w32(end_e_high, end_e_low))) | @(int end_a_high, int end_a_low, int end_b_high, int end_b_low, int end_c_high, int end_c_low, int end_d_high, int end_d_low, int end_e_high, int end_e_low)) =
  if t >= 80 then (done | @(a_high, a_low, b_high, b_low, c_high, c_low, d_high, d_low, e_high, e_low))
  else let
    val (constant | @(k_high, k_low)) = sha1_k(t)
    val (word | @(w_high, w_low)) = _scheduled(schedule, listed, t)
    val (step | @(new_a_high, new_a_low, new_c_high, new_c_low)) =
      sha1_round(t, a_high, a_low, b_high, b_low, c_high, c_low, d_high, d_low, e_high, e_low, k_high, k_low, w_high, w_low)
  in _rounds1(schedule, listed, t + 1,
       new_a_high, new_a_low, a_high, a_low, new_c_high, new_c_low, c_high, c_low, d_high, d_low,
       SHA1_ROUNDS_next(done, constant, word, step)) end

(* The block of 64 bytes from `at` of the message hashed onto the chaining
   value in the array (20 bytes, five words, at 0), the new chaining value
   written there, with the proof that it is the standard's *)
#pub fun sha1_compress {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}
  {lw:agz}{words:$A.cells}{lc:agz}{chain:$A.cells}
  {h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536}
  (message: !$A.barr(lm, nm, msg), at: int at, schedule: $A.barr(lw, 320, words),
   chaining: $A.barr(lc, 20, chain), have: FIVE_AT(chain, 0, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low))))
  : [words2:$A.cells][chain2:$A.cells][next_h0_high,next_h0_low,next_h1_high,next_h1_low,next_h2_high,next_h2_low,next_h3_high,next_h3_low,next_h4_high,next_h4_low:nat | next_h0_high < 65536; next_h0_low < 65536; next_h1_high < 65536; next_h1_low < 65536; next_h2_high < 65536; next_h2_low < 65536; next_h3_high < 65536; next_h3_low < 65536; next_h4_high < 65536; next_h4_low < 65536]
    (SHA1_BLOCK(msg, at, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low)), five(w32(next_h0_high, next_h0_low), w32(next_h1_high, next_h1_low), w32(next_h2_high, next_h2_low), w32(next_h3_high, next_h3_low), w32(next_h4_high, next_h4_low))),
     FIVE_AT(chain2, 0, five(w32(next_h0_high, next_h0_low), w32(next_h1_high, next_h1_low), w32(next_h2_high, next_h2_low), w32(next_h3_high, next_h3_low), w32(next_h4_high, next_h4_low)))
     | @($A.barr(lw, 320, words2), $A.barr(lc, 20, chain2)))

implement sha1_compress {lm}{nm}{msg}{at}{lw}{words}{lc}{chain}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low}
  (message, at, schedule, chaining, have) = let
  val (listed | schedule) = schedule_sha1(message, at, schedule)
  val @(h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low) = five_get(chaining, 0, have)
  val (rounds | @(end_a_high, end_a_low, end_b_high, end_b_low, end_c_high, end_c_low, end_d_high, end_d_low, end_e_high, end_e_low)) = _rounds1(schedule, listed, 0,
    h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low, SHA1_ROUNDS_zero())
  val (add0 | @(next_h0_high, next_h0_low)) = $AR.add32(h0_high, h0_low, end_a_high, end_a_low)
  val (add1 | @(next_h1_high, next_h1_low)) = $AR.add32(h1_high, h1_low, end_b_high, end_b_low)
  val (add2 | @(next_h2_high, next_h2_low)) = $AR.add32(h2_high, h2_low, end_c_high, end_c_low)
  val (add3 | @(next_h3_high, next_h3_low)) = $AR.add32(h3_high, h3_low, end_d_high, end_d_low)
  val (add4 | @(next_h4_high, next_h4_low)) = $AR.add32(h4_high, h4_low, end_e_high, end_e_low)
  val (written | chaining) = five_set(chaining, 0, next_h0_high, next_h0_low, next_h1_high, next_h1_low, next_h2_high, next_h2_low, next_h3_high, next_h3_low, next_h4_high, next_h4_low)
in (SHA1_BLOCK_mk(rounds, add0, add1, add2, add3, add4), written | @(schedule, chaining)) end

(* ============================================================
   Messages as sequences of bytes, and the padding (FIPS 180-4,
   sections 5.1.1 and 5.1.2), proved (bats-lang/sha256#29, stage D)

   A message is a sequence of cells (array's `cells`, whose cell values
   are the bytes). `SNOC(message, value, message_after)` says message_after is
   message with the byte `value` after it. `HELD(base, cells, n, message)`
   says message is `base` followed, one byte at a time, by the first n cells
   of `cells`: it is how bytes reach a message from an array (a piece given
   to update, the block being filled), and it names no array but the cells it
   reads. `LIST(message)` says message is a finite sequence, which is what
   lets a byte be put after it.
   ============================================================ *)

#pub dataprop SNOC($A.cells, int, $A.cells) =
  | {value:int} SNOC_nil($A.cnil(), value, $A.ccons(value, $A.cnil()))
  | {head,value:int}{cells,cells_after:$A.cells} SNOC_cons($A.ccons(head, cells), value, $A.ccons(head, cells_after)) of SNOC(cells, value, cells_after)

#pub dataprop LISTN($A.cells, int) =
  | LISTN_nil($A.cnil(), 0)
  | {head:int}{cells:$A.cells}{size:nat} LISTN_cons($A.ccons(head, cells), size + 1) of LISTN(cells, size)

#pub dataprop LIST($A.cells) =
  | {message:$A.cells}{size:nat} LIST_mk(message) of LISTN(message, size)

(* the empty message is a sequence *)
#pub prfun empty_is_a_list (): LIST($A.cnil())

primplement empty_is_a_list () = LIST_mk(LISTN_nil())

#pub dataprop HELD($A.cells, $A.cells, int, $A.cells) =
  | {base,cells:$A.cells} HELD_zero(base, cells, 0, base)
  | {base,cells,message,message_after:$A.cells}{n:nat}{value:int}
    HELD_next(base, cells, n + 1, message_after) of (HELD(base, cells, n, message), $A.NTH(cells, n, value), SNOC(message, value, message_after))

(* A byte can be put after any message *)
#pub prfun snoc_list {message:$A.cells}{value:int} (LIST(message)): [message_after:$A.cells] (SNOC(message, value, message_after), LIST(message_after))

prfun _snoc_list {message:$A.cells}{value:int}{size:nat} .<size>.
  (listed: LISTN(message, size)): [message_after:$A.cells] (SNOC(message, value, message_after), LISTN(message_after, size + 1)) =
  case+ listed of
  | LISTN_nil() => (SNOC_nil(), LISTN_cons(LISTN_nil()))
  | LISTN_cons(rest) => let
      prval (snoc, longer) = _snoc_list{..}{value}(rest)
    in (SNOC_cons(snoc), LISTN_cons(longer)) end

primplement snoc_list {message}{value} (list) = let
  prval LIST_mk(listed) = list
  prval (snoc, longer) = _snoc_list{message}{value}(listed)
in (snoc, LIST_mk(longer)) end

(* Setting a cell the held bytes do not reach leaves them as they were *)
#pub prfun held_frame {base,cells,cells_after,message:$A.cells}{n,i:nat | n <= i}{value:int}
  (HELD(base, cells, n, message), $A.SETC(cells, i, value, cells_after)): HELD(base, cells_after, n, message)

prfun _held_frame {base,cells,cells_after,message:$A.cells}{n,i:nat | n <= i}{value:int} .<n>.
  (held: HELD(base, cells, n, message), set: $A.SETC(cells, i, value, cells_after)): HELD(base, cells_after, n, message) =
  case+ held of
  | HELD_zero() => HELD_zero()
  | HELD_next(before, cell, snoc) =>
      HELD_next(_held_frame(before, set), $A.setc_nth_other(set, cell), snoc)

primplement held_frame {base,cells,cells_after,message}{n,i}{value} (held, set) = _held_frame(held, set)

(* ============================================================
   The length of a message, in digits, and the padding

   The solver is 32-bit, so a message's length is not one integer: it is
   (count_top, count_high, count_blocks, fill) for n = 2 to the 32 *
   count_top + 2 to the 16 * count_high + 64 * count_blocks + fill, with
   fill the bytes in the block being filled (fill = 64 while that block is
   full and not yet hashed, then it is counted anew by NORM), count_blocks
   under 1024 (so 64 * count_blocks + fill is the low 16 bits), count_high
   under 65536 and count_top under 8192: a message of under 2 to the 45
   bytes, whose length in bits is under 2 to the 48, so the 64-bit length of
   the padding has its top two bytes zero.
   ============================================================ *)

(* NORM: a full block (fill = 64) is hashed, and the count carries into the
   next digit: the blocks, then count_high, then count_top *)
#pub dataprop NORM(int, int, int, int, int, int, int, int) =
  | {count_top,count_high:nat}{count_blocks:nat | count_blocks + 1 < 1024} NORM_block(count_top, count_high, count_blocks, 64, count_top, count_high, count_blocks + 1, 0)
  | {count_top,count_high:nat | count_high + 1 < 65536} NORM_carry(count_top, count_high, 1023, 64, count_top, count_high + 1, 0, 0)
  | {count_top:nat | count_top + 1 < 8192} NORM_carry2(count_top, 65535, 1023, 64, count_top + 1, 0, 0, 0)

(* COUNTED(message, count_top, count_high, count_blocks, fill): message has
   2^32 * count_top + 2^16 * count_high + 64 * count_blocks + fill bytes, by
   its bytes one at a time (COUNTED_byte), and a full block hashed (COUNTED_norm) *)
#pub dataprop COUNTED($A.cells, int, int, int, int) =
  | COUNTED_nil($A.cnil(), 0, 0, 0, 0)
  | {message,message_after:$A.cells}{count_top,count_high,count_blocks,fill:nat | fill < 64}{value:int}
    COUNTED_byte(message_after, count_top, count_high, count_blocks, fill + 1) of (COUNTED(message, count_top, count_high, count_blocks, fill), SNOC(message, value, message_after))
  | {message:$A.cells}{count_top,count_high,count_blocks,fill,count_top_after,count_high_after,count_blocks_after,fill_after:nat}
    COUNTED_norm(message, count_top_after, count_high_after, count_blocks_after, fill_after) of (COUNTED(message, count_top, count_high, count_blocks, fill), NORM(count_top, count_high, count_blocks, fill, count_top_after, count_high_after, count_blocks_after, fill_after))

(* The length in bits is 8 * n, and n = 2^32 * count_top + 2^16 * count_high +
   64 * count_blocks + fill, so 8 * n is three 16-bit limbs: each limb is two
   bytes and hands a carry (under 8) to the next. The three relations are
   small because the solver is 32-bit: each limb is its own, with its own few
   variables, and the carries are what they share.

   BITLEN_LOW(count_blocks, fill, carry_low, byte6, byte7): 8 * (64 *
   count_blocks + fill) = 65536 * carry_low + 256 * byte6 + byte7, the low limb
   and the carry out of it, with count_blocks = 128 * carry_low + blocks_rest
   BITLEN_MID(count_high, carry_low, carry_mid, byte4, byte5): 8 * count_high +
   carry_low = 65536 * carry_mid + 256 * byte4 + byte5, with count_high = 8192 *
   carry_mid + high_rest
   BITLEN_HIGH(count_top, carry_mid, byte2, byte3): 8 * count_top + carry_mid =
   256 * byte2 + byte3 (under 65536 since count_top is under 8192) *)
#pub dataprop BITLEN_LOW(int, int, int, int, int) =
  | {count_blocks,fill,carry_low,blocks_rest,byte6,byte7:nat | count_blocks == 128*carry_low + blocks_rest; blocks_rest < 128; carry_low < 8; fill < 64; byte6 < 256; byte7 < 256; 256*byte6 + byte7 == 512*blocks_rest + 8*fill}
    BITLEN_LOW_mk(count_blocks, fill, carry_low, byte6, byte7)

#pub dataprop BITLEN_MID(int, int, int, int, int) =
  | {count_high,carry_low,carry_mid,high_rest,byte4,byte5:nat | count_high == 8192*carry_mid + high_rest; high_rest < 8192; carry_mid < 8; carry_low < 8; byte4 < 256; byte5 < 256; 256*byte4 + byte5 == 8*high_rest + carry_low}
    BITLEN_MID_mk(count_high, carry_low, carry_mid, byte4, byte5)

#pub dataprop BITLEN_HIGH(int, int, int, int) =
  | {count_top,carry_mid,byte2,byte3:nat | count_top < 8192; carry_mid < 8; byte2 < 256; byte3 < 256; 256*byte2 + byte3 == 8*count_top + carry_mid}
    BITLEN_HIGH_mk(count_top, carry_mid, byte2, byte3)

(* BITLEN(count_top, count_high, count_blocks, fill, byte0, ..., byte7): the
   8 bytes, most significant first, of 8 * n, the length in bits (the top two
   are 0: the length is under 2^48) *)
#pub dataprop BITLEN(int, int, int, int, int, int, int, int, int, int, int, int) =
  | {count_top,count_high,count_blocks,fill,carry_low,carry_mid,byte2,byte3,byte4,byte5,byte6,byte7:nat}
    BITLEN_mk(count_top, count_high, count_blocks, fill, 0, 0, byte2, byte3, byte4, byte5, byte6, byte7) of (
      BITLEN_LOW(count_blocks, fill, carry_low, byte6, byte7), BITLEN_MID(count_high, carry_low, carry_mid, byte4, byte5), BITLEN_HIGH(count_top, carry_mid, byte2, byte3))

(* ZCOUNT(fill, zeros): `zeros` is the number of zero bytes after the 0x80 of
   a message whose length is `fill` modulo 64: the smallest number with fill +
   1 + zeros + 8 a multiple of 64 (5.1.1: the smallest k with l + 1 + k = 448
   modulo 512, here in bytes) *)
#pub dataprop ZCOUNT(int, int) =
  | {fill,zeros:nat | fill <= 55; zeros == 55 - fill} ZCOUNT_short(fill, zeros)
  | {fill,zeros:nat | 56 <= fill; fill < 64; zeros == 119 - fill} ZCOUNT_long(fill, zeros)

(* ZSNOC(start, zeros, longer): longer is start with `zeros` zero bytes after it *)
#pub dataprop ZSNOC($A.cells, int, $A.cells) =
  | {start:$A.cells} ZSNOC_zero(start, 0, start)
  | {start,so_far,longer:$A.cells}{zeros:nat} ZSNOC_next(start, zeros + 1, longer) of (ZSNOC(start, zeros, so_far), SNOC(so_far, 0, longer))

(* LENSNOC(start, byte0, ..., byte7, grown8): grown8 is start with the bytes
   byte0 to byte7 after it, one at a time *)
#pub dataprop LENSNOC($A.cells, int, int, int, int, int, int, int, int, $A.cells) =
  | {start,grown1,grown2,grown3,grown4,grown5,grown6,grown7,grown8:$A.cells}{byte0,byte1,byte2,byte3,byte4,byte5,byte6,byte7:int}
    LENSNOC_mk(start, byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7, grown8) of (
      SNOC(start, byte0, grown1), SNOC(grown1, byte1, grown2), SNOC(grown2, byte2, grown3), SNOC(grown3, byte3, grown4),
      SNOC(grown4, byte4, grown5), SNOC(grown5, byte5, grown6), SNOC(grown6, byte6, grown7), SNOC(grown7, byte7, grown8))

(* PAD(message, count_top, count_high, count_blocks, fill, padded): padded is
   the message, of that length, padded (FIPS 180-4, section 5.1.1 of SHA-256
   and of SHA-1): the byte 128 (the bit 1 and seven zeros), `zeros` zero bytes
   (ZCOUNT) and the 64-bit big-endian length in bits (BITLEN). padded is a
   multiple of 64 bytes long. *)
#pub dataprop PAD($A.cells, int, int, int, int, $A.cells) =
  | {message,marked,zeroed,padded:$A.cells}{count_top,count_high,count_blocks,fill,zeros:nat}{byte0,byte1,byte2,byte3,byte4,byte5,byte6,byte7:int}
    PAD_mk(message, count_top, count_high, count_blocks, fill, padded) of (
      COUNTED(message, count_top, count_high, count_blocks, fill), ZCOUNT(fill, zeros),
      BITLEN(count_top, count_high, count_blocks, fill, byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7),
      SNOC(message, 128, marked), ZSNOC(marked, zeros, zeroed), LENSNOC(zeroed, byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7, padded))

(* The 8 bytes of the length in bits (the top two are 0), with the proof that
   they are *)
#pub fun bitlen_bytes {count_top,count_high,count_blocks,fill:nat | count_top < 8192; count_high < 65536; count_blocks < 1024; fill < 64}
  (count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill)
  : [byte2,byte3,byte4,byte5,byte6,byte7:nat | byte2 < 256; byte3 < 256; byte4 < 256; byte5 < 256; byte6 < 256; byte7 < 256]
    (BITLEN(count_top, count_high, count_blocks, fill, 0, 0, byte2, byte3, byte4, byte5, byte6, byte7) | @(int byte2, int byte3, int byte4, int byte5, int byte6, int byte7))

fn _split128 {number:nat} (number: int number): [quotient,remainder:nat | number == 128*quotient + remainder; remainder < 128] @(int quotient, int remainder) = let
  val quotient = number / 128
in @(quotient, number - 128 * quotient) end

fn _split256 {number:nat} (number: int number): [quotient,remainder:nat | number == 256*quotient + remainder; remainder < 256] @(int quotient, int remainder) = let
  val quotient = number / 256
in @(quotient, number - 256 * quotient) end

fn _split8192 {number:nat} (number: int number): [quotient,remainder:nat | number == 8192*quotient + remainder; remainder < 8192] @(int quotient, int remainder) = let
  val quotient = number / 8192
in @(quotient, number - 8192 * quotient) end

(* The low limb of 8 * n, and the carry out of it *)
#pub fun bitlen_low {count_blocks,fill:nat | count_blocks < 1024; fill < 64} (count_blocks: int count_blocks, fill: int fill)
  : [carry_low,byte6,byte7:nat | carry_low < 8; byte6 < 256; byte7 < 256] (BITLEN_LOW(count_blocks, fill, carry_low, byte6, byte7) | @(int carry_low, int byte6, int byte7))

implement bitlen_low {count_blocks,fill} (count_blocks, fill) = let
  val [carry_low:int, blocks_rest:int] @(carry_low, blocks_rest) = _split128(count_blocks)
  val [byte6:int, byte7:int] @(byte6, byte7) = _split256(512 * blocks_rest + 8 * fill)
in (BITLEN_LOW_mk{count_blocks,fill,carry_low,blocks_rest,byte6,byte7}() | @(carry_low, byte6, byte7)) end

(* The middle limb, with the carry from below, and the carry out of it *)
#pub fun bitlen_mid {count_high,carry_low:nat | count_high < 65536; carry_low < 8} (count_high: int count_high, carry_low: int carry_low)
  : [carry_mid,byte4,byte5:nat | carry_mid < 8; byte4 < 256; byte5 < 256] (BITLEN_MID(count_high, carry_low, carry_mid, byte4, byte5) | @(int carry_mid, int byte4, int byte5))

implement bitlen_mid {count_high,carry_low} (count_high, carry_low) = let
  val [carry_mid:int, high_rest:int] @(carry_mid, high_rest) = _split8192(count_high)
  val [byte4:int, byte5:int] @(byte4, byte5) = _split256(8 * high_rest + carry_low)
in (BITLEN_MID_mk{count_high,carry_low,carry_mid,high_rest,byte4,byte5}() | @(carry_mid, byte4, byte5)) end

(* The high limb, with the carry from below *)
#pub fun bitlen_high {count_top,carry_mid:nat | count_top < 8192; carry_mid < 8} (count_top: int count_top, carry_mid: int carry_mid)
  : [byte2,byte3:nat | byte2 < 256; byte3 < 256] (BITLEN_HIGH(count_top, carry_mid, byte2, byte3) | @(int byte2, int byte3))

implement bitlen_high {count_top,carry_mid} (count_top, carry_mid) = let
  val [byte2:int, byte3:int] @(byte2, byte3) = _split256(8 * count_top + carry_mid)
in (BITLEN_HIGH_mk{count_top,carry_mid,byte2,byte3}() | @(byte2, byte3)) end

implement bitlen_bytes {count_top,count_high,count_blocks,fill} (count_top, count_high, count_blocks, fill) = let
  val (low | @(carry_low, byte6, byte7)) = bitlen_low(count_blocks, fill)
  val (mid | @(carry_mid, byte4, byte5)) = bitlen_mid(count_high, carry_low)
  val (high | @(byte2, byte3)) = bitlen_high(count_top, carry_mid)
in (BITLEN_mk(low, mid, high) | @(byte2, byte3, byte4, byte5, byte6, byte7)) end

(* ============================================================
   Writing the padding in place in the block being filled
   ============================================================ *)

(* The byte `value` put at cell i of the block, after the i bytes held *)
fn _emit {block_loc:agz}{block_cells,base,message:$A.cells}{i:nat | i < 64}{value:nat | value < 256}
  (block_array: $A.barr(block_loc, 64, block_cells), i: int i, value: int value, held: HELD(base, block_cells, i, message), list: LIST(message))
  : [block_cells_after,message_after:$A.cells] (HELD(base, block_cells_after, i + 1, message_after), LIST(message_after), SNOC(message, value, message_after) | $A.barr(block_loc, 64, block_cells_after)) = let
  val (set | block_array) = $A.barr_set(block_array, i, value)
  prval kept = held_frame(held, set)
  prval (snoc, listed) = snoc_list{message}{value}(list)
in (HELD_next(kept, $A.setc_nth_same(set), snoc), listed, snoc | block_array) end

(* `remaining` zero bytes put from cell i, after `zeros_so_far` zeros *)
fun _emit_zeros {block_loc:agz}{block_cells,base,marked,message:$A.cells}{zeros_so_far:nat}{i,remaining:nat | i + remaining <= 64} .<remaining>.
  (block_array: $A.barr(block_loc, 64, block_cells), i: int i, remaining: int remaining,
   held: HELD(base, block_cells, i, message), list: LIST(message), zeros: ZSNOC(marked, zeros_so_far, message))
  : [block_cells_after,message_after:$A.cells] (HELD(base, block_cells_after, i + remaining, message_after), LIST(message_after), ZSNOC(marked, zeros_so_far + remaining, message_after) | $A.barr(block_loc, 64, block_cells_after)) =
  if remaining = 0 then (held, list, zeros | block_array)
  else let
    val (held_next, list_next, snoc | block_array) = _emit(block_array, i, 0, held, list)
  in _emit_zeros(block_array, i + 1, remaining - 1, held_next, list_next, ZSNOC_next(zeros, snoc)) end

(* The 8 bytes of the length at cells 56 to 63 *)
fn _emit_length {block_loc:agz}{block_cells,base,zeroed:$A.cells}{byte2,byte3,byte4,byte5,byte6,byte7:nat | byte2 < 256; byte3 < 256; byte4 < 256; byte5 < 256; byte6 < 256; byte7 < 256}
  (block_array: $A.barr(block_loc, 64, block_cells), held: HELD(base, block_cells, 56, zeroed), list: LIST(zeroed),
   byte2: int byte2, byte3: int byte3, byte4: int byte4, byte5: int byte5, byte6: int byte6, byte7: int byte7)
  : [block_cells_after,padded:$A.cells] (HELD(base, block_cells_after, 64, padded), LENSNOC(zeroed, 0, 0, byte2, byte3, byte4, byte5, byte6, byte7, padded) | $A.barr(block_loc, 64, block_cells_after)) = let
  val (held0, listed0, snoc0 | block_array) = _emit(block_array, 56, 0, held, list)
  val (held1, listed1, snoc1 | block_array) = _emit(block_array, 57, 0, held0, listed0)
  val (held2, listed2, snoc2 | block_array) = _emit(block_array, 58, byte2, held1, listed1)
  val (held3, listed3, snoc3 | block_array) = _emit(block_array, 59, byte3, held2, listed2)
  val (held4, listed4, snoc4 | block_array) = _emit(block_array, 60, byte4, held3, listed3)
  val (held5, listed5, snoc5 | block_array) = _emit(block_array, 61, byte5, held4, listed4)
  val (held6, listed6, snoc6 | block_array) = _emit(block_array, 62, byte6, held5, listed5)
  val (held7, listed7, snoc7 | block_array) = _emit(block_array, 63, byte7, held6, listed6)
in (held7, LENSNOC_mk(snoc0, snoc1, snoc2, snoc3, snoc4, snoc5, snoc6, snoc7) | block_array) end

(* A message of fill <= 55 bytes in the block being filled: the padding makes
   the block whole (128, zeros, the length) *)
#pub fun pad_short {block_loc:agz}{block_cells,hashed_bytes,message:$A.cells}{count_top,count_high,count_blocks,fill:nat | count_top < 8192; count_high < 65536; count_blocks < 1024; fill <= 55}
  (block_array: $A.barr(block_loc, 64, block_cells), count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill,
   held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message), counted: COUNTED(message, count_top, count_high, count_blocks, fill))
  : [block_cells_after,padded:$A.cells] (HELD(hashed_bytes, block_cells_after, 64, padded), PAD(message, count_top, count_high, count_blocks, fill, padded) | $A.barr(block_loc, 64, block_cells_after))

implement pad_short {block_loc}{block_cells,hashed_bytes,message}{count_top,count_high,count_blocks,fill} (block_array, count_top, count_high, count_blocks, fill, held, list, counted) = let
  val (held1, list1, snoc128 | block_array) = _emit(block_array, fill, 128, held, list)
  val (held2, list2, zeros | block_array) = _emit_zeros(block_array, fill + 1, 55 - fill, held1, list1, ZSNOC_zero())
  val (lengths | @(byte2, byte3, byte4, byte5, byte6, byte7)) = bitlen_bytes(count_top, count_high, count_blocks, fill)
  val (held3, written | block_array) = _emit_length(block_array, held2, list2, byte2, byte3, byte4, byte5, byte6, byte7)
in (held3, PAD_mk(counted, ZCOUNT_short(), lengths, snoc128, zeros, written) | block_array) end

(* A message of 56 to 63 bytes in the block being filled: the first padding
   block is whole with the 128 and zeros; the second (pad_long_second, once
   the first is hashed) is the rest *)
#pub fun pad_long_first {block_loc:agz}{block_cells,hashed_bytes,message:$A.cells}{fill:nat | 56 <= fill; fill < 64}
  (block_array: $A.barr(block_loc, 64, block_cells), fill: int fill, held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message))
  : [block_cells_after,marked,first_padded:$A.cells]
    (HELD(hashed_bytes, block_cells_after, 64, first_padded), LIST(first_padded), SNOC(message, 128, marked), ZSNOC(marked, 63 - fill, first_padded) | $A.barr(block_loc, 64, block_cells_after))

implement pad_long_first {block_loc}{block_cells,hashed_bytes,message}{fill} (block_array, fill, held, list) = let
  val (held1, list1, snoc128 | block_array) = _emit(block_array, fill, 128, held, list)
  val (held2, list2, zeros | block_array) = _emit_zeros(block_array, fill + 1, 63 - fill, held1, list1, ZSNOC_zero())
in (held2, list2, snoc128, zeros | block_array) end

#pub fun pad_long_second {block_loc:agz}{block_cells,message,marked,first_padded:$A.cells}{count_top,count_high,count_blocks,fill:nat | count_top < 8192; count_high < 65536; count_blocks < 1024; 56 <= fill; fill < 64}
  (block_array: $A.barr(block_loc, 64, block_cells), count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill,
   list: LIST(first_padded), counted: COUNTED(message, count_top, count_high, count_blocks, fill), snoc128: SNOC(message, 128, marked), zeros: ZSNOC(marked, 63 - fill, first_padded))
  : [block_cells_after,padded:$A.cells] (HELD(first_padded, block_cells_after, 64, padded), PAD(message, count_top, count_high, count_blocks, fill, padded) | $A.barr(block_loc, 64, block_cells_after))

implement pad_long_second {block_loc}{block_cells,message,marked,first_padded}{count_top,count_high,count_blocks,fill} (block_array, count_top, count_high, count_blocks, fill, list, counted, snoc128, zeros) = let
  val (held1, list1, more | block_array) = _emit_zeros(block_array, 0, 56, HELD_zero(), list, zeros)
  val (lengths | @(byte2, byte3, byte4, byte5, byte6, byte7)) = bitlen_bytes(count_top, count_high, count_blocks, fill)
  val (held2, written | block_array) = _emit_length(block_array, held1, list1, byte2, byte3, byte4, byte5, byte6, byte7)
in (held2, PAD_mk(counted, ZCOUNT_long(), lengths, snoc128, more, written) | block_array) end

(* ============================================================
   The hash of a sequence of whole blocks, and the digest
   ============================================================ *)

(* SHA256_IV(chaining): the initial hash value H(0) of SHA-256 (FIPS 180-4, section
   5.3.3): the first 32 bits of the fractional parts of the square roots of
   the first eight primes. Stated, and tested against the definition, not
   proved (needs integers of 2 to the 64: sha256 issue 31) *)
#pub dataprop SHA256_IV(eight_words) =
  | SHA256_IV_mk(eight(w32(0x6a09, 0xe667), w32(0xbb67, 0xae85), w32(0x3c6e, 0xf372), w32(0xa54f, 0xf53a),
                       w32(0x510e, 0x527f), w32(0x9b05, 0x688c), w32(0x1f83, 0xd9ab), w32(0x5be0, 0xcd19)))

(* SHA1_IV(chaining): the initial hash value H(0) of SHA-1 (section 5.3.1), five
   constants the standard gives as they are *)
#pub dataprop SHA1_IV(five_words) =
  | SHA1_IV_mk(five(w32(0x6745, 0x2301), w32(0xefcd, 0xab89), w32(0x98ba, 0xdcfe), w32(0x1032, 0x5476), w32(0xc3d2, 0xe1f0)))

(* The initial value, with the proof that it is the table's. The words are in
   the type, so the values returned are the ones the proof states. *)
#pub fun sha256_iv ()
  : (SHA256_IV(eight(w32(0x6a09, 0xe667), w32(0xbb67, 0xae85), w32(0x3c6e, 0xf372), w32(0xa54f, 0xf53a),
                     w32(0x510e, 0x527f), w32(0x9b05, 0x688c), w32(0x1f83, 0xd9ab), w32(0x5be0, 0xcd19))) |
     @(int(0x6a09), int(0xe667), int(0xbb67), int(0xae85), int(0x3c6e), int(0xf372), int(0xa54f), int(0xf53a),
       int(0x510e), int(0x527f), int(0x9b05), int(0x688c), int(0x1f83), int(0xd9ab), int(0x5be0), int(0xcd19)))

implement sha256_iv () = (SHA256_IV_mk() | @(0x6a09, 0xe667, 0xbb67, 0xae85, 0x3c6e, 0xf372, 0xa54f, 0xf53a,
                                              0x510e, 0x527f, 0x9b05, 0x688c, 0x1f83, 0xd9ab, 0x5be0, 0xcd19))

#pub fun sha1_iv ()
  : (SHA1_IV(five(w32(0x6745, 0x2301), w32(0xefcd, 0xab89), w32(0x98ba, 0xdcfe), w32(0x1032, 0x5476), w32(0xc3d2, 0xe1f0))) |
     @(int(0x6745), int(0x2301), int(0xefcd), int(0xab89), int(0x98ba), int(0xdcfe), int(0x1032), int(0x5476), int(0xc3d2), int(0xe1f0)))

implement sha1_iv () = (SHA1_IV_mk() | @(0x6745, 0x2301, 0xefcd, 0xab89, 0x98ba, 0xdcfe, 0x1032, 0x5476, 0xc3d2, 0xe1f0))

(* HASHED256(hashed_bytes, chaining): the SHA-256 chaining value after the
   sequence hashed_bytes, a whole number of 64-byte blocks, is `chaining`: the
   initial value, and then each block, which is 64 bytes put after the ones
   before (HELD) and is compressed (SHA256_BLOCK) onto the value the ones
   before made. The block's bytes are the first 64 cells of an array's cells,
   at 0. HASHED1 is the same for SHA-1. *)
#pub dataprop HASHED256($A.cells, eight_words) =
  | {chaining:eight_words} HASHED256_start($A.cnil(), chaining) of SHA256_IV(chaining)
  | {hashed_bytes,hashed_after,cells:$A.cells}{chaining,chaining_after:eight_words}
    HASHED256_block(hashed_after, chaining_after) of (HASHED256(hashed_bytes, chaining), SHA256_BLOCK(cells, 0, chaining, chaining_after), HELD(hashed_bytes, cells, 64, hashed_after))

#pub dataprop HASHED1($A.cells, five_words) =
  | {chaining:five_words} HASHED1_start($A.cnil(), chaining) of SHA1_IV(chaining)
  | {hashed_bytes,hashed_after,cells:$A.cells}{chaining,chaining_after:five_words}
    HASHED1_block(hashed_after, chaining_after) of (HASHED1(hashed_bytes, chaining), SHA1_BLOCK(cells, 0, chaining, chaining_after), HELD(hashed_bytes, cells, 64, hashed_after))

(* DIGEST256(message, chaining): the SHA-256 of the message is `chaining`:
   the message padded (PAD), and the padded message hashed block by block from
   the initial value (HASHED256). DIGEST1 is the same for SHA-1. *)
#pub dataprop DIGEST256($A.cells, eight_words) =
  | {message,padded:$A.cells}{count_top,count_high,count_blocks,fill:nat}{chaining:eight_words}
    DIGEST256_mk(message, chaining) of (PAD(message, count_top, count_high, count_blocks, fill, padded), HASHED256(padded, chaining))

#pub dataprop DIGEST1($A.cells, five_words) =
  | {message,padded:$A.cells}{count_top,count_high,count_blocks,fill:nat}{chaining:five_words}
    DIGEST1_mk(message, chaining) of (PAD(message, count_top, count_high, count_blocks, fill, padded), HASHED1(padded, chaining))


(* The halves of a word of an array are under 2 to the 16 (bound lemmas: what
   the compression's preconditions need of the words an array holds) *)
#pub prfun word_at_bound {cells:$A.cells}{at,high,low:nat} (WORD_AT(cells, at, high, low)): [high < 65536; low < 65536] void

primplement word_at_bound {cells}{at,high,low} (word) = let
  prval WORD_AT_mk(case0, case1, case2, case3) = word
in end

#pub prfun eight_at_bound {cells:$A.cells}{at,h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat}
  (EIGHT_AT(cells, at, eight(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low), w32(h5_high, h5_low), w32(h6_high, h6_low), w32(h7_high, h7_low))))
  : [h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536; h5_high < 65536; h5_low < 65536; h6_high < 65536; h6_low < 65536; h7_high < 65536; h7_low < 65536] void

primplement eight_at_bound {cells}{at,h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low} (have) = let
  prval EIGHT_AT_mk(word0, word1, word2, word3, word4, word5, word6, word7) = have
  prval () = word_at_bound(word0)
  prval () = word_at_bound(word1)
  prval () = word_at_bound(word2)
  prval () = word_at_bound(word3)
  prval () = word_at_bound(word4)
  prval () = word_at_bound(word5)
  prval () = word_at_bound(word6)
  prval () = word_at_bound(word7)
in end

(* One block hashed onto the chaining value: the block is the 64 bytes held
   in the block array, put after the bytes already hashed *)
fn _compress256 {chain_loc,schedule_loc,block_loc:agz}{chain_cells,schedule_cells,block_cells,hashed_bytes,message:$A.cells}{chaining:eight_words}
  (block_array: !$A.barr(block_loc, 64, block_cells), schedule_array: $A.barr(schedule_loc, 256, schedule_cells), chain_array: $A.barr(chain_loc, 32, chain_cells),
   have: EIGHT_AT(chain_cells, 0, chaining), hashed: HASHED256(hashed_bytes, chaining), held: HELD(hashed_bytes, block_cells, 64, message))
  : [schedule_cells_after,chain_cells_after:$A.cells][chaining_after:eight_words]
    (HASHED256(message, chaining_after), EIGHT_AT(chain_cells_after, 0, chaining_after) | @($A.barr(schedule_loc, 256, schedule_cells_after), $A.barr(chain_loc, 32, chain_cells_after))) = let
  prval EIGHT_AT_mk(word0, word1, word2, word3, word4, word5, word6, word7) = have
  prval opened = EIGHT_AT_mk(word0, word1, word2, word3, word4, word5, word6, word7)
  prval () = eight_at_bound(opened)
  val (block, written | @(schedule_array, chain_array)) = sha256_compress(block_array, 0, schedule_array, chain_array, opened)
in (HASHED256_block(hashed, block, held), written | @(schedule_array, chain_array)) end

#pub datavtype ctx256($A.cells) =
  | {message:$A.cells}{chain_loc,schedule_loc,block_loc:agz}{chain_cells,schedule_cells,block_cells,hashed_bytes:$A.cells}{chaining:eight_words}{count_top,count_high,count_blocks,fill:nat | count_top < 8191; count_high < 65536; count_blocks < 1024; fill < 64}
    ctx256_mk(message) of (
      HASHED256(hashed_bytes, chaining), EIGHT_AT(chain_cells, 0, chaining), HELD(hashed_bytes, block_cells, fill, message), LIST(message), COUNTED(message, count_top, count_high, count_blocks, fill) |
      $A.barr(chain_loc, 32, chain_cells), $A.barr(schedule_loc, 256, schedule_cells), $A.barr(block_loc, 64, block_cells), int count_top, int count_high, int count_blocks, int fill)

(* The parts of a hash of the empty message: the proofs and the three arrays *)
fn _init256 ()
  : [chain_cells,schedule_cells,block_cells:$A.cells][chain_loc,schedule_loc,block_loc:agz][chaining:eight_words]
    (HASHED256($A.cnil(), chaining), EIGHT_AT(chain_cells, 0, chaining), HELD($A.cnil(), block_cells, 0, $A.cnil()), LIST($A.cnil()),
     COUNTED($A.cnil(), 0, 0, 0, 0) | @($A.barr(chain_loc, 32, chain_cells), $A.barr(schedule_loc, 256, schedule_cells), $A.barr(block_loc, 64, block_cells))) = let
  val (_ | chain_array) = $A.barr_alloc(32)
  val (_ | schedule_array) = $A.barr_alloc(256)
  val (_ | block_array) = $A.barr_alloc(64)
  val (initial | @(h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low, h5_high, h5_low, h6_high, h6_low, h7_high, h7_low)) = sha256_iv()
  val (have | chain_array) = eight_set(chain_array, 0, h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low,
                                       h4_high, h4_low, h5_high, h5_low, h6_high, h6_low, h7_high, h7_low)
in (HASHED256_start(initial), have, HELD_zero(), empty_is_a_list(), COUNTED_nil() | @(chain_array, schedule_array, block_array)) end

(* A hash of the empty message: the context of everything fed to it so far,
   indexed by that message. Its chaining value (HASHED256), the bytes of the
   block being filled (HELD), their count (COUNTED) and the arrays are held
   in it, and none of them is given out. *)
#pub fn init256_proved (): ctx256($A.cnil())

implement init256_proved () = let
  val (hashed, have, block_held, list, counted | @(chain_array, schedule_array, block_array)) = _init256()
in ctx256_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, 0, 0, 0, 0) end

(* Bytes of data from i put in the block until the data ends or the block is
   full: each is read from the data, put at the next cell and counted *)
fun _feed {block_loc,data_loc:agz}{n:nat}{data_cells,message_before,block_cells,hashed_bytes,message:$A.cells}{length:nat | length <= n}{i:nat | i <= length}{count_top,count_high,count_blocks,fill:nat | fill <= 64} .<length - i>.
  (block_array: $A.barr(block_loc, 64, block_cells), data: !$A.barr(data_loc, n, data_cells), length: int length, i: int i, fill: int fill,
   data_held: HELD(message_before, data_cells, i, message), block_held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message), counted: COUNTED(message, count_top, count_high, count_blocks, fill))
  : [block_cells_after,message_after:$A.cells][index_after,fill_after:nat | i <= index_after; index_after <= length; fill <= fill_after; fill_after <= 64; fill_after - fill == index_after - i; index_after == length || fill_after == 64]
    (HELD(message_before, data_cells, index_after, message_after), HELD(hashed_bytes, block_cells_after, fill_after, message_after), LIST(message_after), COUNTED(message_after, count_top, count_high, count_blocks, fill_after)
     | @($A.barr(block_loc, 64, block_cells_after), int index_after, int fill_after)) =
  if i >= length then (data_held, block_held, list, counted | @(block_array, i, fill))
  else if fill >= 64 then (data_held, block_held, list, counted | @(block_array, i, fill))
  else let
    val [value:int] (cell | value) = $A.barr_get(data, i)
    val (set | block_array) = $A.barr_set(block_array, fill, value)
    prval kept = held_frame(block_held, set)
    prval (snoc, list_after) = snoc_list{message}{value}(list)
  in _feed(block_array, data, length, i + 1, fill + 1,
       HELD_next(data_held, cell, snoc), HELD_next(kept, $A.setc_nth_same(set), snoc), list_after, COUNTED_byte(counted, snoc)) end

(* The count once a full block is hashed: carried into the next digit (the
   top digit is under 8190, so it cannot pass its end) *)
fn _normalize {count_top,count_high,count_blocks:nat | count_top < 8190; count_high < 65536; count_blocks < 1024} (count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks)
  : [count_top_after,count_high_after,count_blocks_after:nat | count_top_after < 8191; count_high_after < 65536; count_blocks_after < 1024]
    (NORM(count_top, count_high, count_blocks, 64, count_top_after, count_high_after, count_blocks_after, 0) | @(int count_top_after, int count_high_after, int count_blocks_after)) =
  if count_blocks < 1023 then (NORM_block() | @(count_top, count_high, count_blocks + 1))
  else if count_high < 65535 then (NORM_carry() | @(count_top, count_high + 1, 0))
  else (NORM_carry2() | @(count_top + 1, 0, 0))

(* What update256_proved did: all `length` bytes were put after the message
   (Updated256: message_after is the message and the first `length` cells of
   the data, one after the other), or the message reached its largest length
   (about 2 to the 45 bytes) first and the bytes from the i-th on were not put
   (Stopped256: only the first i were). The comparable streaming API of HACL*
   answers a length over its maximum with an error code, as this does. *)
#pub datavtype update256_result($A.cells, $A.cells, int) =
  | {message_before,data_cells:$A.cells}{length:nat}{message_after:$A.cells}
    Updated256(message_before, data_cells, length) of (HELD(message_before, data_cells, length, message_after) | ctx256(message_after))
  | {message_before,data_cells:$A.cells}{length:nat}{message_after:$A.cells}{i:nat | i < length}
    Stopped256(message_before, data_cells, length) of (HELD(message_before, data_cells, i, message_after) | ctx256(message_after))

fun _update256 {chain_loc,schedule_loc,block_loc,data_loc:agz}{n:nat}{data_cells,message_before:$A.cells}{length:nat | length <= n}{i:nat | i <= length}
  {chain_cells,schedule_cells,block_cells,hashed_bytes,message:$A.cells}{chaining:eight_words}{count_top,count_high,count_blocks,fill:nat | count_top < 8191; count_high < 65536; count_blocks < 1024; fill < 64} .<length - i>.
  (chain_array: $A.barr(chain_loc, 32, chain_cells), schedule_array: $A.barr(schedule_loc, 256, schedule_cells), block_array: $A.barr(block_loc, 64, block_cells),
   data: !$A.barr(data_loc, n, data_cells), length: int length, i: int i, count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill,
   hashed: HASHED256(hashed_bytes, chaining), have: EIGHT_AT(chain_cells, 0, chaining), block_held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message),
   counted: COUNTED(message, count_top, count_high, count_blocks, fill), data_held: HELD(message_before, data_cells, i, message))
  : update256_result(message_before, data_cells, length) =
  if i >= length then Updated256(data_held | ctx256_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill))
  else if count_top >= 8190 then Stopped256(data_held | ctx256_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill))
  else let
    val (data_held_after, block_held_after, list_after, counted_after | @(block_array, index_after, fill_after)) = _feed(block_array, data, length, i, fill, data_held, block_held, list, counted)
  in
    if fill_after >= 64 then let
      val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress256(block_array, schedule_array, chain_array, have, hashed, block_held_after)
      val (norm | @(count_top_after, count_high_after, count_blocks_after)) = _normalize(count_top, count_high, count_blocks)
    in _update256(chain_array, schedule_array, block_array, data, length, index_after, count_top_after, count_high_after, count_blocks_after, 0,
         hashed_after, have_after, HELD_zero(), list_after, COUNTED_norm(counted_after, norm), data_held_after) end
    else Updated256(data_held_after | ctx256_mk(hashed, have, block_held_after, list_after, counted_after | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill_after))
  end

(* The bytes data[0, len) put after the message so far, one by one: the
   result's HELD proof is that message_after is the message followed by those
   cells. A block that fills is hashed (and the proof that it was, with the
   chaining value it made, is in the context). *)
#pub fn update256_proved {message,data_cells:$A.cells}{l:agz}{n:nat}{length:nat | length <= n}
  (c: ctx256(message), data: !$A.barr(l, n, data_cells), len: int length): update256_result(message, data_cells, length)

implement update256_proved {message,data_cells}{l}{n}{length} (c, data, len) = let
  val+ ~ctx256_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill) = c
in _update256(chain_array, schedule_array, block_array, data, len, 0, count_top, count_high, count_blocks, fill, hashed, have, block_held, list, counted, HELD_zero()) end

(* ============================================================
   The digest as 64 lowercase hex digits
   ============================================================ *)

(* HEX_DIGIT(digit, character): `character` is the ASCII character of the hex
   digit (a to f lower case) *)
#pub dataprop HEX_DIGIT(int, int) =
  | {digit:nat | digit < 10} HEX_DIGIT_decimal(digit, 48 + digit)
  | {digit:nat | 10 <= digit; digit < 16} HEX_DIGIT_letter(digit, 87 + digit)

(* HEXOF(out_cells, chain_cells, n): the first n bytes of chain_cells are
   written in out_cells as two hex digits each, the high digit first, from
   cell 0 *)
#pub dataprop HEXOF($A.cells, $A.cells, int) =
  | {out_cells,chain_cells:$A.cells} HEXOF_zero(out_cells, chain_cells, 0)
  | {out_cells,chain_cells:$A.cells}{n:nat}{value,high_nibble,low_nibble,first_char,second_char:nat | value < 256; high_nibble < 16; low_nibble < 16; value == 16*high_nibble + low_nibble}
    HEXOF_next(out_cells, chain_cells, n + 1) of (
      HEXOF(out_cells, chain_cells, n), $A.NTH(chain_cells, n, value), HEX_DIGIT(high_nibble, first_char), HEX_DIGIT(low_nibble, second_char),
      $A.NTH(out_cells, 2*n, first_char), $A.NTH(out_cells, 2*n + 1, second_char))

(* EIGHT_HEX(out_cells, chaining): out_cells holds the 64 hex digits of the 32
   bytes that are the eight words of `chaining`, big endian (the bytes are
   those of an array that held them: EIGHT_AT) *)
#pub dataprop EIGHT_HEX($A.cells, eight_words) =
  | {out_cells,chain_cells:$A.cells}{chaining:eight_words} EIGHT_HEX_mk(out_cells, chaining) of (EIGHT_AT(chain_cells, 0, chaining), HEXOF(out_cells, chain_cells, 32))

(* Setting a cell beyond the digits written leaves them as they were *)
prfun hexof_frame {out_cells,out_cells_after,chain_cells:$A.cells}{n,j:nat | 2*n <= j}{character:int} .<n>.
  (done: HEXOF(out_cells, chain_cells, n), set: $A.SETC(out_cells, j, character, out_cells_after)): HEXOF(out_cells_after, chain_cells, n) =
  case+ done of
  | HEXOF_zero() => HEXOF_zero()
  | HEXOF_next(before, nth, first, second, at_even, at_odd) =>
      HEXOF_next(hexof_frame(before, set), nth, first, second,
                 $A.setc_nth_other(set, at_even), $A.setc_nth_other(set, at_odd))

fn _split16 {number:nat | number < 256} (number: int number)
  : [quotient,remainder:nat | number == 16*quotient + remainder; quotient < 16; remainder < 16] @(int quotient, int remainder) = let
  val quotient = number / 16
in @(quotient, number - 16 * quotient) end

fn _hex_char {digit:nat | digit < 16} (digit: int digit): [character:nat | character < 256] (HEX_DIGIT(digit, character) | int character) =
  if digit < 10 then (HEX_DIGIT_decimal() | digit + 48) else (HEX_DIGIT_letter() | digit + 87)

fun _hex_bytes {chain_loc,out_loc:agz}{chain_cells,out_cells:$A.cells}{n:nat | n <= 32} .<32 - n>.
  (chain_array: !$A.barr(chain_loc, 32, chain_cells), out: $A.barr(out_loc, 64, out_cells), n: int n, done: HEXOF(out_cells, chain_cells, n))
  : [out_cells_after:$A.cells] (HEXOF(out_cells_after, chain_cells, 32) | $A.barr(out_loc, 64, out_cells_after)) =
  if n >= 32 then (done | out)
  else let
    val [value:int] (nth | value) = $A.barr_get(chain_array, n)
    val [high_nibble:int, low_nibble:int] @(high_nibble, low_nibble) = _split16(value)
    val [first_char:int] (first | first_char) = _hex_char(high_nibble)
    val [second_char:int] (second | second_char) = _hex_char(low_nibble)
    val (set_even | out) = $A.barr_set(out, 2 * n, first_char)
    val (set_odd | out) = $A.barr_set(out, 2 * n + 1, second_char)
    prval kept = hexof_frame(hexof_frame(done, set_even), set_odd)
    prval at_even = $A.setc_nth_other(set_odd, $A.setc_nth_same(set_even))
    prval at_odd = $A.setc_nth_same(set_odd)
  in _hex_bytes(chain_array, out, n + 1, HEXOF_next(kept, nth, first, second, at_even, at_odd)) end

(* The hex digits of the chaining value, the array of it freed *)
fn _hex_out256 {chain_loc,out_loc:agz}{chain_cells,out_cells:$A.cells}{chaining:eight_words}
  (chain_array: $A.barr(chain_loc, 32, chain_cells), have: EIGHT_AT(chain_cells, 0, chaining), out: $A.barr(out_loc, 64, out_cells))
  : [out_cells_after:$A.cells] (EIGHT_HEX(out_cells_after, chaining) | $A.barr(out_loc, 64, out_cells_after)) = let
  val (written | out) = _hex_bytes(chain_array, out, 0, HEXOF_zero())
  val () = $A.barr_free(chain_array)
in (EIGHT_HEX_mk(have, written) | out) end

(* The padding of the message so far, the last block or two hashed, and the
   SHA-256 of the message as 64 lowercase hex digits in out, with the proof
   that it is (DIGEST256, EIGHT_HEX). The context is used up. *)
#pub fn finish256_proved {message:$A.cells}{out_loc:agz}{out_cells:$A.cells} (c: ctx256(message), out: $A.barr(out_loc, 64, out_cells))
  : [out_cells_after:$A.cells][chaining:eight_words] (DIGEST256(message, chaining), EIGHT_HEX(out_cells_after, chaining) | $A.barr(out_loc, 64, out_cells_after))

implement finish256_proved {message}{out_loc}{out_cells} (c, out) = let
  val+ ~ctx256_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill) = c
in
  if fill <= 55 then let
    val (held, pad | block_array) = pad_short(block_array, count_top, count_high, count_blocks, fill, block_held, list, counted)
    val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress256(block_array, schedule_array, chain_array, have, hashed, held)
    val () = $A.barr_free(block_array)
    val () = $A.barr_free(schedule_array)
    val (hex | out) = _hex_out256(chain_array, have_after, out)
  in (DIGEST256_mk(pad, hashed_after), hex | out) end
  else let
    val (held1, list_first, snoc, zeros | block_array) = pad_long_first(block_array, fill, block_held, list)
    val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress256(block_array, schedule_array, chain_array, have, hashed, held1)
    val (held2, pad | block_array) = pad_long_second(block_array, count_top, count_high, count_blocks, fill, list_first, counted, snoc, zeros)
    val (hashed_last, have_last | @(schedule_array, chain_array)) = _compress256(block_array, schedule_array, chain_array, have_after, hashed_after, held2)
    val () = $A.barr_free(block_array)
    val () = $A.barr_free(schedule_array)
    val (hex | out) = _hex_out256(chain_array, have_last, out)
  in (DIGEST256_mk(pad, hashed_last), hex | out) end
end

(* ============================================================
   The digest of a whole array in one call
   ============================================================ *)

(* The same loop as _update256, for a message that starts empty and is under
   2 to the 16 bytes: 64 * count_blocks + fill = i bytes are in (so
   count_blocks is under 1024), the digits above stay 0, and the message never
   reaches its largest length. The count is not tied to anything bigger on
   purpose: the 32-bit solver accepted a false claim in a context that held
   1024 * count_high + count_blocks = j and 64 * j + fill = i together (65536 *
   count_high once j is gone) *)
fun _small256 {chain_loc,schedule_loc,block_loc,data_loc:agz}{n:nat}{data_cells,message_before:$A.cells}{length:nat | length <= n; length <= 65535}{i:nat | i <= length}
  {chain_cells,schedule_cells,block_cells,hashed_bytes,message:$A.cells}{chaining:eight_words}{count_blocks,fill:nat | count_blocks < 1024; fill < 64; 64*count_blocks + fill == i} .<length - i>.
  (chain_array: $A.barr(chain_loc, 32, chain_cells), schedule_array: $A.barr(schedule_loc, 256, schedule_cells), block_array: $A.barr(block_loc, 64, block_cells),
   data: !$A.barr(data_loc, n, data_cells), length: int length, i: int i, count_blocks: int count_blocks, fill: int fill,
   hashed: HASHED256(hashed_bytes, chaining), have: EIGHT_AT(chain_cells, 0, chaining), block_held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message),
   counted: COUNTED(message, 0, 0, count_blocks, fill), data_held: HELD(message_before, data_cells, i, message))
  : [message_after:$A.cells] (HELD(message_before, data_cells, length, message_after) | ctx256(message_after)) =
  if i >= length then (data_held | ctx256_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, 0, 0, count_blocks, fill))
  else let
    val (data_held_after, block_held_after, list_after, counted_after | @(block_array, index_after, fill_after)) = _feed(block_array, data, length, i, fill, data_held, block_held, list, counted)
  in
    if fill_after >= 64 then let
      val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress256(block_array, schedule_array, chain_array, have, hashed, block_held_after)
    in _small256(chain_array, schedule_array, block_array, data, length, index_after, count_blocks + 1, 0,
         hashed_after, have_after, HELD_zero(), list_after, COUNTED_norm(counted_after, NORM_block()), data_held_after) end
    else (data_held_after | ctx256_mk(hashed, have, block_held_after, list_after, counted_after | chain_array, schedule_array, block_array, 0, 0, count_blocks, fill_after))
  end

(* The SHA-256 of data[0, len), under 2 to the 16 bytes, as 64 lowercase hex
   digits in out: the message is the first len cells of the data, one after the
   other (HELD), its digest is the chaining value the padded message makes
   (DIGEST256), and the digits are that value's (EIGHT_HEX). For more bytes
   than that, the incremental API, in pieces. *)
#pub fn sha256_digest_proved {l:agz}{n:nat}{data_cells:$A.cells}{length:nat | length <= n; length <= 65535}{out_loc:agz}{out_cells:$A.cells}
  (data: !$A.barr(l, n, data_cells), len: int length, out: $A.barr(out_loc, 64, out_cells))
  : [message,out_cells_after:$A.cells][chaining:eight_words]
    (HELD($A.cnil(), data_cells, length, message), DIGEST256(message, chaining), EIGHT_HEX(out_cells_after, chaining) | $A.barr(out_loc, 64, out_cells_after))

implement sha256_digest_proved {l}{n}{data_cells}{length}{out_loc}{out_cells} (data, len, out) = let
  val (hashed, have, block_held, list, counted | @(chain_array, schedule_array, block_array)) = _init256()
  val (data_held | c) = _small256(chain_array, schedule_array, block_array, data, len, 0, 0, 0, hashed, have, block_held, list, counted, HELD_zero())
  val (digest, hex | out) = finish256_proved(c, out)
in (data_held, digest, hex | out) end

(* ============================================================
   SHA-1's digest (FIPS 180-4, section 6.1), the same padding and blocks
   ============================================================ *)

#pub prfun five_at_bound {cells:$A.cells}{at,h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat}
  (FIVE_AT(cells, at, five(w32(h0_high, h0_low), w32(h1_high, h1_low), w32(h2_high, h2_low), w32(h3_high, h3_low), w32(h4_high, h4_low))))
  : [h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536] void

primplement five_at_bound {cells}{at,h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low} (have) = let
  prval FIVE_AT_mk(word0, word1, word2, word3, word4) = have
  prval () = word_at_bound(word0)
  prval () = word_at_bound(word1)
  prval () = word_at_bound(word2)
  prval () = word_at_bound(word3)
  prval () = word_at_bound(word4)
in end

fn _compress1 {chain_loc,schedule_loc,block_loc:agz}{chain_cells,schedule_cells,block_cells,hashed_bytes,message:$A.cells}{chaining:five_words}
  (block_array: !$A.barr(block_loc, 64, block_cells), schedule_array: $A.barr(schedule_loc, 320, schedule_cells), chain_array: $A.barr(chain_loc, 20, chain_cells),
   have: FIVE_AT(chain_cells, 0, chaining), hashed: HASHED1(hashed_bytes, chaining), held: HELD(hashed_bytes, block_cells, 64, message))
  : [schedule_cells_after,chain_cells_after:$A.cells][chaining_after:five_words]
    (HASHED1(message, chaining_after), FIVE_AT(chain_cells_after, 0, chaining_after) | @($A.barr(schedule_loc, 320, schedule_cells_after), $A.barr(chain_loc, 20, chain_cells_after))) = let
  prval FIVE_AT_mk(word0, word1, word2, word3, word4) = have
  prval opened = FIVE_AT_mk(word0, word1, word2, word3, word4)
  prval () = five_at_bound(opened)
  val (block, written | @(schedule_array, chain_array)) = sha1_compress(block_array, 0, schedule_array, chain_array, opened)
in (HASHED1_block(hashed, block, held), written | @(schedule_array, chain_array)) end

(* The padding and the last blocks of a SHA-1 message, and its 20 bytes
   written to out (the five words of the chaining value, big endian) *)
fn _finish1 {chain_loc,schedule_loc,block_loc,out_loc:agz}{chain_cells,schedule_cells,block_cells,hashed_bytes,message,out_cells:$A.cells}{chaining:five_words}{count_top,count_high,count_blocks,fill:nat | count_top < 8191; count_high < 65536; count_blocks < 1024; fill < 64}
  (chain_array: $A.barr(chain_loc, 20, chain_cells), schedule_array: $A.barr(schedule_loc, 320, schedule_cells), block_array: $A.barr(block_loc, 64, block_cells),
   count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill,
   hashed: HASHED1(hashed_bytes, chaining), have: FIVE_AT(chain_cells, 0, chaining), block_held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message),
   counted: COUNTED(message, count_top, count_high, count_blocks, fill), out: $A.barr(out_loc, 20, out_cells))
  : [out_cells_after:$A.cells][chaining_after:five_words] (DIGEST1(message, chaining_after), FIVE_AT(out_cells_after, 0, chaining_after) | $A.barr(out_loc, 20, out_cells_after)) = let
  fn written {chain_loc,out_loc:agz}{chain_cells,out_cells:$A.cells}{chaining:five_words}
    (chain_array: $A.barr(chain_loc, 20, chain_cells), have: FIVE_AT(chain_cells, 0, chaining), out: $A.barr(out_loc, 20, out_cells))
    : [out_cells_after:$A.cells] (FIVE_AT(out_cells_after, 0, chaining) | $A.barr(out_loc, 20, out_cells_after)) = let
    prval FIVE_AT_mk(word0, word1, word2, word3, word4) = have
    prval opened = FIVE_AT_mk(word0, word1, word2, word3, word4)
    prval () = five_at_bound(opened)
    val @(h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low) = five_get(chain_array, 0, opened)
    val () = $A.barr_free(chain_array)
  in five_set(out, 0, h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low) end
in
  if fill <= 55 then let
    val (held, pad | block_array) = pad_short(block_array, count_top, count_high, count_blocks, fill, block_held, list, counted)
    val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress1(block_array, schedule_array, chain_array, have, hashed, held)
    val () = $A.barr_free(block_array)
    val () = $A.barr_free(schedule_array)
    val (placed | out) = written(chain_array, have_after, out)
  in (DIGEST1_mk(pad, hashed_after), placed | out) end
  else let
    val (held1, list_first, snoc, zeros | block_array) = pad_long_first(block_array, fill, block_held, list)
    val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress1(block_array, schedule_array, chain_array, have, hashed, held1)
    val (held2, pad | block_array) = pad_long_second(block_array, count_top, count_high, count_blocks, fill, list_first, counted, snoc, zeros)
    val (hashed_last, have_last | @(schedule_array, chain_array)) = _compress1(block_array, schedule_array, chain_array, have_after, hashed_after, held2)
    val () = $A.barr_free(block_array)
    val () = $A.barr_free(schedule_array)
    val (placed | out) = written(chain_array, have_last, out)
  in (DIGEST1_mk(pad, hashed_last), placed | out) end
end

fn _init1 ()
  : [chain_cells,schedule_cells,block_cells:$A.cells][chain_loc,schedule_loc,block_loc:agz][chaining:five_words]
    (HASHED1($A.cnil(), chaining), FIVE_AT(chain_cells, 0, chaining), HELD($A.cnil(), block_cells, 0, $A.cnil()), LIST($A.cnil()),
     COUNTED($A.cnil(), 0, 0, 0, 0) | @($A.barr(chain_loc, 20, chain_cells), $A.barr(schedule_loc, 320, schedule_cells), $A.barr(block_loc, 64, block_cells))) = let
  val (_ | chain_array) = $A.barr_alloc(20)
  val (_ | schedule_array) = $A.barr_alloc(320)
  val (_ | block_array) = $A.barr_alloc(64)
  val (initial | @(h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low)) = sha1_iv()
  val (have | chain_array) = five_set(chain_array, 0, h0_high, h0_low, h1_high, h1_low, h2_high, h2_low, h3_high, h3_low, h4_high, h4_low)
in (HASHED1_start(initial), have, HELD_zero(), empty_is_a_list(), COUNTED_nil() | @(chain_array, schedule_array, block_array)) end

fun _small1 {chain_loc,schedule_loc,block_loc,data_loc,out_loc:agz}{n:nat}{data_cells,message_before,out_cells:$A.cells}{length:nat | length <= n; length <= 65535}{i:nat | i <= length}
  {chain_cells,schedule_cells,block_cells,hashed_bytes,message:$A.cells}{chaining:five_words}{count_blocks,fill:nat | count_blocks < 1024; fill < 64; 64*count_blocks + fill == i} .<length - i>.
  (chain_array: $A.barr(chain_loc, 20, chain_cells), schedule_array: $A.barr(schedule_loc, 320, schedule_cells), block_array: $A.barr(block_loc, 64, block_cells),
   data: !$A.barr(data_loc, n, data_cells), length: int length, i: int i, count_blocks: int count_blocks, fill: int fill,
   hashed: HASHED1(hashed_bytes, chaining), have: FIVE_AT(chain_cells, 0, chaining), block_held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message),
   counted: COUNTED(message, 0, 0, count_blocks, fill), data_held: HELD(message_before, data_cells, i, message), out: $A.barr(out_loc, 20, out_cells))
  : [message_after,out_cells_after:$A.cells][chaining_after:five_words]
    (HELD(message_before, data_cells, length, message_after), DIGEST1(message_after, chaining_after), FIVE_AT(out_cells_after, 0, chaining_after) | $A.barr(out_loc, 20, out_cells_after)) =
  if i >= length then let
    val (digest, placed | out) = _finish1(chain_array, schedule_array, block_array, 0, 0, count_blocks, fill, hashed, have, block_held, list, counted, out)
  in (data_held, digest, placed | out) end
  else let
    val (data_held_after, block_held_after, list_after, counted_after | @(block_array, index_after, fill_after)) = _feed(block_array, data, length, i, fill, data_held, block_held, list, counted)
  in
    if fill_after >= 64 then let
      val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress1(block_array, schedule_array, chain_array, have, hashed, block_held_after)
    in _small1(chain_array, schedule_array, block_array, data, length, index_after, count_blocks + 1, 0,
         hashed_after, have_after, HELD_zero(), list_after, COUNTED_norm(counted_after, NORM_block()), data_held_after, out) end
    else let
      val (digest, placed | out) = _finish1(chain_array, schedule_array, block_array, 0, 0, count_blocks, fill_after, hashed, have, block_held_after, list_after, counted_after, out)
    in (data_held_after, digest, placed | out) end
  end

(* The SHA-1 of data[0, len), under 2 to the 16 bytes, as its 20 bytes in out,
   with the proof that the message is the data and the bytes are its digest
   (DIGEST1, FIVE_AT) *)
#pub fn sha1_digest_proved {l:agz}{n:nat}{data_cells:$A.cells}{length:nat | length <= n; length <= 65535}{out_loc:agz}{out_cells:$A.cells}
  (data: !$A.barr(l, n, data_cells), len: int length, out: $A.barr(out_loc, 20, out_cells))
  : [message,out_cells_after:$A.cells][chaining:five_words]
    (HELD($A.cnil(), data_cells, length, message), DIGEST1(message, chaining), FIVE_AT(out_cells_after, 0, chaining) | $A.barr(out_loc, 20, out_cells_after))

implement sha1_digest_proved {l}{n}{data_cells}{length}{out_loc}{out_cells} (data, len, out) = let
  val (hashed, have, block_held, list, counted | @(chain_array, schedule_array, block_array)) = _init1()
in _small1(chain_array, schedule_array, block_array, data, len, 0, 0, 0, hashed, have, block_held, list, counted, HELD_zero(), out) end

(* ============================================================
   SHA-1 incrementally (FIPS 180-4, section 6.1), the same way as SHA-256
   ============================================================ *)

#pub datavtype ctx1($A.cells) =
  | {message:$A.cells}{chain_loc,schedule_loc,block_loc:agz}{chain_cells,schedule_cells,block_cells,hashed_bytes:$A.cells}{chaining:five_words}{count_top,count_high,count_blocks,fill:nat | count_top < 8191; count_high < 65536; count_blocks < 1024; fill < 64}
    ctx1_mk(message) of (
      HASHED1(hashed_bytes, chaining), FIVE_AT(chain_cells, 0, chaining), HELD(hashed_bytes, block_cells, fill, message), LIST(message), COUNTED(message, count_top, count_high, count_blocks, fill) |
      $A.barr(chain_loc, 20, chain_cells), $A.barr(schedule_loc, 320, schedule_cells), $A.barr(block_loc, 64, block_cells), int count_top, int count_high, int count_blocks, int fill)

(* A hash of the empty message *)
#pub fn init1_proved (): ctx1($A.cnil())

implement init1_proved () = let
  val (hashed, have, block_held, list, counted | @(chain_array, schedule_array, block_array)) = _init1()
in ctx1_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, 0, 0, 0, 0) end

(* What update1_proved did: all `length` bytes were put after the message
   (Updated1: message_after is the message and the first `length` cells of
   the data, one after the other), or the message reached its largest length
   (about 2 to the 45 bytes) first and the bytes from the i-th on were not put
   (Stopped1: only the first i were). The comparable streaming API of HACL*
   answers a length over its maximum with an error code, as this does. *)
#pub datavtype update1_result($A.cells, $A.cells, int) =
  | {message_before,data_cells:$A.cells}{length:nat}{message_after:$A.cells}
    Updated1(message_before, data_cells, length) of (HELD(message_before, data_cells, length, message_after) | ctx1(message_after))
  | {message_before,data_cells:$A.cells}{length:nat}{message_after:$A.cells}{i:nat | i < length}
    Stopped1(message_before, data_cells, length) of (HELD(message_before, data_cells, i, message_after) | ctx1(message_after))

fun _update1 {chain_loc,schedule_loc,block_loc,data_loc:agz}{n:nat}{data_cells,message_before:$A.cells}{length:nat | length <= n}{i:nat | i <= length}
  {chain_cells,schedule_cells,block_cells,hashed_bytes,message:$A.cells}{chaining:five_words}{count_top,count_high,count_blocks,fill:nat | count_top < 8191; count_high < 65536; count_blocks < 1024; fill < 64} .<length - i>.
  (chain_array: $A.barr(chain_loc, 20, chain_cells), schedule_array: $A.barr(schedule_loc, 320, schedule_cells), block_array: $A.barr(block_loc, 64, block_cells),
   data: !$A.barr(data_loc, n, data_cells), length: int length, i: int i, count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill,
   hashed: HASHED1(hashed_bytes, chaining), have: FIVE_AT(chain_cells, 0, chaining), block_held: HELD(hashed_bytes, block_cells, fill, message), list: LIST(message),
   counted: COUNTED(message, count_top, count_high, count_blocks, fill), data_held: HELD(message_before, data_cells, i, message))
  : update1_result(message_before, data_cells, length) =
  if i >= length then Updated1(data_held | ctx1_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill))
  else if count_top >= 8190 then Stopped1(data_held | ctx1_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill))
  else let
    val (data_held_after, block_held_after, list_after, counted_after | @(block_array, index_after, fill_after)) = _feed(block_array, data, length, i, fill, data_held, block_held, list, counted)
  in
    if fill_after >= 64 then let
      val (hashed_after, have_after | @(schedule_array, chain_array)) = _compress1(block_array, schedule_array, chain_array, have, hashed, block_held_after)
      val (norm | @(count_top_after, count_high_after, count_blocks_after)) = _normalize(count_top, count_high, count_blocks)
    in _update1(chain_array, schedule_array, block_array, data, length, index_after, count_top_after, count_high_after, count_blocks_after, 0,
         hashed_after, have_after, HELD_zero(), list_after, COUNTED_norm(counted_after, norm), data_held_after) end
    else Updated1(data_held_after | ctx1_mk(hashed, have, block_held_after, list_after, counted_after | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill_after))
  end

(* The bytes data[0, len) put after the message so far, one by one: the
   result's HELD proof is that message_after is the message followed by those
   cells. A block that fills is hashed (and the proof that it was, with the
   chaining value it made, is in the context). *)
#pub fn update1_proved {message,data_cells:$A.cells}{l:agz}{n:nat}{length:nat | length <= n}
  (c: ctx1(message), data: !$A.barr(l, n, data_cells), len: int length): update1_result(message, data_cells, length)

implement update1_proved {message,data_cells}{l}{n}{length} (c, data, len) = let
  val+ ~ctx1_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill) = c
in _update1(chain_array, schedule_array, block_array, data, len, 0, count_top, count_high, count_blocks, fill, hashed, have, block_held, list, counted, HELD_zero()) end

(* The padding of the message so far, the last block or two hashed, and the
   SHA-1 of the message as its 20 bytes in out, with the proof that they are
   (DIGEST1, FIVE_AT). The context is used up. *)
#pub fn finish1_proved {message:$A.cells}{out_loc:agz}{out_cells:$A.cells} (c: ctx1(message), out: $A.barr(out_loc, 20, out_cells))
  : [out_cells_after:$A.cells][chaining:five_words] (DIGEST1(message, chaining), FIVE_AT(out_cells_after, 0, chaining) | $A.barr(out_loc, 20, out_cells_after))

implement finish1_proved {message}{out_loc}{out_cells} (c, out) = let
  val+ ~ctx1_mk(hashed, have, block_held, list, counted | chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill) = c
in _finish1(chain_array, schedule_array, block_array, count_top, count_high, count_blocks, fill, hashed, have, block_held, list, counted, out) end

(* ============================================================
   Round constants (FIPS 180-4, section 4.2.2)
   ============================================================ *)

fn _k {i:nat | i < 64} (i: int i): uint =
  if i < 8 then
    (if i = 0 then 0x428a2f98u else if i = 1 then 0x71374491u
     else if i = 2 then 0xb5c0fbcfu else if i = 3 then 0xe9b5dba5u
     else if i = 4 then 0x3956c25bu else if i = 5 then 0x59f111f1u
     else if i = 6 then 0x923f82a4u else 0xab1c5ed5u)
  else if i < 16 then
    (if i = 8 then 0xd807aa98u else if i = 9 then 0x12835b01u
     else if i = 10 then 0x243185beu else if i = 11 then 0x550c7dc3u
     else if i = 12 then 0x72be5d74u else if i = 13 then 0x80deb1feu
     else if i = 14 then 0x9bdc06a7u else 0xc19bf174u)
  else if i < 24 then
    (if i = 16 then 0xe49b69c1u else if i = 17 then 0xefbe4786u
     else if i = 18 then 0x0fc19dc6u else if i = 19 then 0x240ca1ccu
     else if i = 20 then 0x2de92c6fu else if i = 21 then 0x4a7484aau
     else if i = 22 then 0x5cb0a9dcu else 0x76f988dau)
  else if i < 32 then
    (if i = 24 then 0x983e5152u else if i = 25 then 0xa831c66du
     else if i = 26 then 0xb00327c8u else if i = 27 then 0xbf597fc7u
     else if i = 28 then 0xc6e00bf3u else if i = 29 then 0xd5a79147u
     else if i = 30 then 0x06ca6351u else 0x14292967u)
  else if i < 40 then
    (if i = 32 then 0x27b70a85u else if i = 33 then 0x2e1b2138u
     else if i = 34 then 0x4d2c6dfcu else if i = 35 then 0x53380d13u
     else if i = 36 then 0x650a7354u else if i = 37 then 0x766a0abbu
     else if i = 38 then 0x81c2c92eu else 0x92722c85u)
  else if i < 48 then
    (if i = 40 then 0xa2bfe8a1u else if i = 41 then 0xa81a664bu
     else if i = 42 then 0xc24b8b70u else if i = 43 then 0xc76c51a3u
     else if i = 44 then 0xd192e819u else if i = 45 then 0xd6990624u
     else if i = 46 then 0xf40e3585u else 0x106aa070u)
  else if i < 56 then
    (if i = 48 then 0x19a4c116u else if i = 49 then 0x1e376c08u
     else if i = 50 then 0x2748774cu else if i = 51 then 0x34b0bcb5u
     else if i = 52 then 0x391c0cb3u else if i = 53 then 0x4ed8aa4au
     else if i = 54 then 0x5b9cca4fu else 0x682e6ff3u)
  else
    (if i = 56 then 0x748f82eeu else if i = 57 then 0x78a5636fu
     else if i = 58 then 0x84c87814u else if i = 59 then 0x8cc70208u
     else if i = 60 then 0x90befffau else if i = 61 then 0xa4506cebu
     else if i = 62 then 0xbef9a3f7u else 0xc67178f2u)

(* ============================================================
   Block compression (FIPS 180-4, section 6.2.2)
   ============================================================ *)

(* Processes data[bo, bo + 64) into h, using w as the message schedule. *)
fn _compress {ld:agz}{nd:pos}{bo:nat | bo + 64 <= nd}{lw:agz}{lh:agz}
  (data: !$A.arr(byte, ld, nd), bo: int bo,
   w: !$A.arr(uint, lw, 64), h: !$A.arr(uint, lh, 8)): void = let
  fun load {t:nat | t <= 16} .<16 - t>.
    (data: !$A.arr(byte, ld, nd), w: !$A.arr(uint, lw, 64), t: int t): void =
    if t >= 16 then ()
    else let
      val o = bo + 4 * t
      val b0 = _u(byte2int0($A.get<byte>(data, o)))
      val b1 = _u(byte2int0($A.get<byte>(data, o + 1)))
      val b2 = _u(byte2int0($A.get<byte>(data, o + 2)))
      val b3 = _u(byte2int0($A.get<byte>(data, o + 3)))
      val () = $A.set<uint>(w, t, (b0 << 24) lor (b1 << 16) lor (b2 << 8) lor b3)
    in load(data, w, t + 1) end
  fun expand {t:int | 16 <= t; t <= 64} .<64 - t>.
    (w: !$A.arr(uint, lw, 64), t: int t): void =
    if t >= 64 then ()
    else let
      val v = _ssig1($A.get<uint>(w, t - 2)) + $A.get<uint>(w, t - 7)
            + _ssig0($A.get<uint>(w, t - 15)) + $A.get<uint>(w, t - 16)
      val () = $A.set<uint>(w, t, v)
    in expand(w, t + 1) end
  fun rounds {t:nat | t <= 64} .<64 - t>.
    (w: !$A.arr(uint, lw, 64), t: int t,
     a: uint, b: uint, c: uint, d: uint,
     e: uint, f: uint, g: uint, hh: uint): @(uint, uint, uint, uint, uint, uint, uint, uint) =
    if t >= 64 then @(a, b, c, d, e, f, g, hh)
    else let
      val t1 = hh + _bsig1(e) + _ch(e, f, g) + _k(t) + $A.get<uint>(w, t)
      val t2 = _bsig0(a) + _maj(a, b, c)
    in rounds(w, t + 1, t1 + t2, a, b, c, d + t1, e, f, g) end
  val () = load(data, w, 0)
  val () = expand(w, 16)
  val h0 = $A.get<uint>(h, 0) val h1 = $A.get<uint>(h, 1)
  val h2 = $A.get<uint>(h, 2) val h3 = $A.get<uint>(h, 3)
  val h4 = $A.get<uint>(h, 4) val h5 = $A.get<uint>(h, 5)
  val h6 = $A.get<uint>(h, 6) val h7 = $A.get<uint>(h, 7)
  val @(a, b, c, d, e, f, g, hh) = rounds(w, 0, h0, h1, h2, h3, h4, h5, h6, h7)
  val () = $A.set<uint>(h, 0, h0 + a) val () = $A.set<uint>(h, 1, h1 + b)
  val () = $A.set<uint>(h, 2, h2 + c) val () = $A.set<uint>(h, 3, h3 + d)
  val () = $A.set<uint>(h, 4, h4 + e) val () = $A.set<uint>(h, 5, h5 + f)
  val () = $A.set<uint>(h, 6, h6 + g) val () = $A.set<uint>(h, 7, h7 + hh)
in end

(* The one or two padding blocks in pad[0, last). *)
fn _compress_pad {lp,lw,lh:agz}{e:int | e == 64 || e == 128}
  (pad: !$A.arr(byte, lp, 128), last: int e,
   w: !$A.arr(uint, lw, 64), h: !$A.arr(uint, lh, 8)): void = let
  val () = _compress(pad, 0, w, h)
in if last = 128 then _compress(pad, 64, w, h) else () end

(* ============================================================
   Output
   ============================================================ *)

(* The low byte of x. *)
fn _byte (x: uint): [v:nat | v < 256] int v =
  $AR.low_byte(g0uint2int_uint_int(x land 0xffu))

(* The hex digit of d < 16. *)
fn _hex {d:nat | d < 16} (d: int d): [c:nat | c < 256] int c =
  if d < 10 then d + 48 else d + 87

(* Writes x as 8 hex digits at out[p, p + 8). *)
fn _put_word {lo:agz}{p:nat | p + 8 <= 64}
  (out: !$A.arr(byte, lo, 64), p: int p, x: uint): void = let
  fun loop {i:nat | i <= 8} .<8 - i>.
    (out: !$A.arr(byte, lo, 64), i: int i): void =
    if i >= 8 then ()
    else let
      val v = _byte(x >> (28 - 4 * i))
      val hi = v / 16
      val () = $A.set<byte>(out, p + i, $A.int2byte(_hex(v - 16 * hi)))
    in loop(out, i + 1) end
in loop(out, 0) end

(* ============================================================
   Incremental hash
   ============================================================ *)

implement init () = let
  val h = $A.alloc<uint>(8)
  val () = $A.set<uint>(h, 0, 0x6a09e667u)
  val () = $A.set<uint>(h, 1, 0xbb67ae85u)
  val () = $A.set<uint>(h, 2, 0x3c6ef372u)
  val () = $A.set<uint>(h, 3, 0xa54ff53au)
  val () = $A.set<uint>(h, 4, 0x510e527fu)
  val () = $A.set<uint>(h, 5, 0x9b05688cu)
  val () = $A.set<uint>(h, 6, 0x1f83d9abu)
  val () = $A.set<uint>(h, 7, 0x5be0cd19u)
in ctx_mk(h, $A.alloc<uint>(64), $A.alloc<byte>(64), 0, 0u, 0u) end

(* data[i, k) appended to the block in buf[0, b), compressing each block
   as it fills; the bytes left in the block *)
fun _fill {lh,lw,lb,ld:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}{b:nat | b < 64}
  .<k - i>.
  (h: !$A.arr(uint, lh, 8), w: !$A.arr(uint, lw, 64), buf: !$A.arr(byte, lb, 64),
   data: !$A.arr(byte, ld, n), k: int k, i: int i, b: int b)
  : [b2:nat | b2 < 64] int b2 =
  if i >= k then b
  else let
    val () = $A.set<byte>(buf, b, $A.get<byte>(data, i))
  in
    if b + 1 >= 64 then let
      val () = _compress(buf, 0, w, h)
    in _fill(h, w, buf, data, k, i + 1, 0) end
    else _fill(h, w, buf, data, k, i + 1, b + 1)
  end

implement update {l}{n}{k} (c, data, len) = let
  val+ @ctx_mk(h, w, buf, b, hi, lo) = c
  val () = b := _fill(h, w, buf, data, len, 0, b)
  val nlo = lo + _u(len)
  val () = (if nlo < lo then hi := hi + 1u else ())
  val () = lo := nlo
  prval () = fold@(c)
in end

implement finish {lo} (c, out) = let
  val+ ~ctx_mk(h, w, buf, tail, nhi, nlo) = c
  (* The tail, 0x80, zeros and the 64-bit big-endian bit length, in one
     or two blocks. alloc zeroes the buffer. *)
  val pad = $A.alloc<byte>(128)
  fun copy {lp,lb:agz}{t:nat | t < 64}{i:nat | i <= t} .<t - i>.
    (buf: !$A.arr(byte, lb, 64), pad: !$A.arr(byte, lp, 128), t: int t, i: int i): void =
    if i >= t then ()
    else let
      val () = $A.set<byte>(pad, i, $A.get<byte>(buf, i))
    in copy(buf, pad, t, i + 1) end
  val () = copy(buf, pad, tail, 0)
  val () = $A.set<byte>(pad, tail, $A.int2byte(128))
  val last = (if tail + 9 > 64 then 128 else 64): [e:int | e == 64 || e == 128] int e
  val bhi = (nhi << 3) lor (nlo >> 29)
  val blo = nlo << 3
  val () = $A.set<byte>(pad, last - 8, $A.int2byte(_byte(bhi >> 24)))
  val () = $A.set<byte>(pad, last - 7, $A.int2byte(_byte(bhi >> 16)))
  val () = $A.set<byte>(pad, last - 6, $A.int2byte(_byte(bhi >> 8)))
  val () = $A.set<byte>(pad, last - 5, $A.int2byte(_byte(bhi)))
  val () = $A.set<byte>(pad, last - 4, $A.int2byte(_byte(blo >> 24)))
  val () = $A.set<byte>(pad, last - 3, $A.int2byte(_byte(blo >> 16)))
  val () = $A.set<byte>(pad, last - 2, $A.int2byte(_byte(blo >> 8)))
  val () = $A.set<byte>(pad, last - 1, $A.int2byte(_byte(blo)))
  val () = _compress_pad(pad, last, w, h)
  fun put {lh:agz}{j:nat | j <= 8} .<8 - j>.
    (out: !$A.arr(byte, lo, 64), h: !$A.arr(uint, lh, 8), j: int j): void =
    if j >= 8 then ()
    else let val () = _put_word(out, 8 * j, $A.get<uint>(h, j)) in put(out, h, j + 1) end
  val () = put(out, h, 0)
  val () = $A.free<byte>(pad)
  val () = $A.free<byte>(buf)
  val () = $A.free<uint>(w)
  val () = $A.free<uint>(h)
in end

(* ============================================================
   Main hash
   ============================================================ *)

implement hash {l}{n}{lo} (data, data_len, out) = let
  val c = init()
  val () = update(c, data, data_len)
in finish(c, out) end

(* ============================================================
   The proved code through arrays: proved_hash, proved_init,
   proved_update, proved_finish and sha1_digest (sha256#29, stage E)

   The callers' arrays are array's `arr` (and `borrow`), whose cells the
   types know nothing of, and the proved functions read a `barr`, whose
   cells they do. So the bytes of a call are copied, a piece at a time, into
   a `barr` of the package's own (_copy_arr, _copy_borrow) and fed to the
   proved update (update256_proved, update1_proved); the digits and bytes
   the proved finish writes into a `barr` are copied to the caller's array
   (_copy_out). The copies are glue the types do not check, tested by
   tests/dynamic; everything between them (the padding, the blocks, the
   message schedule, the rounds, the chaining value, the digits) is the
   proved code, so the digest a caller gets is the one DIGEST256 and
   DIGEST1 are about. An input of any length is fed in pieces to the
   incremental proved API, so no input is limited to the 2 to the 16 bytes
   the one-shot sha256_digest_proved and sha1_digest_proved take (those are
   proved too and stay beside).

   hash, init, update and finish keep the fast code above: they are not
   changed, and the proved functions are new names beside them.
   ============================================================ *)

(* A byte as the integer it is, 0 to 255 *)
fn _octet (b: byte): [v:int | 0 <= v; v < 256] int v = let
  val x = g1ofg0(byte2int0(b))
in
  if x >= 0 then (if x < 256 then x else 0)
  else if x >= ~256 then x + 256 else 0
end

(* data[from, from + count) put in the cells of the piece from its j-th on *)
fun _copy_arr {ld,lb:agz}{nd:pos}{from,count:nat | from + count <= nd; count <= 4096}{j:nat | j <= count}{cs:$A.cells} .<count - j>.
  (piece: $A.barr(lb, 4096, cs), data: !$A.arr(byte, ld, nd), from: int from, count: int count, j: int j)
  : [cs2:$A.cells] $A.barr(lb, 4096, cs2) =
  if j >= count then piece
  else let
    val (_ | piece) = $A.barr_set(piece, j, _octet($A.get<byte>(data, from + j)))
  in _copy_arr(piece, data, from, count, j + 1) end

fun _copy_borrow {ld,lb:agz}{nd:pos}{from,count:nat | from + count <= nd; count <= 4096}{j:nat | j <= count}{cs:$A.cells} .<count - j>.
  (piece: $A.barr(lb, 4096, cs), data: !$A.borrow(byte, ld, nd), from: int from, count: int count, j: int j)
  : [cs2:$A.cells] $A.barr(lb, 4096, cs2) =
  if j >= count then piece
  else let
    val (_ | piece) = $A.barr_set(piece, j, _octet($A.read<byte>(data, from + j)))
  in _copy_borrow(piece, data, from, count, j + 1) end

(* The first count cells of a barr put in an array of the caller's *)
fun _copy_out {lt,lo:agz}{n:pos}{count:nat | count <= n}{j:nat | j <= count}{cs:$A.cells} .<count - j>.
  (source: !$A.barr(lt, n, cs), out: !$A.arr(byte, lo, n), count: int count, j: int j): void =
  if j >= count then ()
  else let
    val (_ | v) = $A.barr_get(source, j)
    val () = $A.set<byte>(out, j, $A.int2byte(v))
  in _copy_out(source, out, count, j + 1) end

(* data[i, length) fed to the context in pieces of at most 4096 bytes; it stops
   (Stopped256) only when the message has reached its largest length, about
   2 to the 45 bytes *)
fun _pour256 {ld,lb:agz}{nd:pos}{message,cs:$A.cells}{length:nat | length <= nd}{i:nat | i <= length} .<length - i>.
  (c: ctx256(message), piece: $A.barr(lb, 4096, cs), data: !$A.arr(byte, ld, nd), length: int length, i: int i)
  : [message_after,cs2:$A.cells] @(ctx256(message_after), $A.barr(lb, 4096, cs2)) =
  if i >= length then @(c, piece)
  else let
    val rest = length - i
    val count = (if rest < 4096 then rest else 4096): [q:pos | q <= 4096; q <= length - i] int q
    val piece = _copy_arr(piece, data, i, count, 0)
  in
    case+ update256_proved(c, piece, count) of
    | ~Updated256(_ | c2) => _pour256(c2, piece, data, length, i + count)
    | ~Stopped256(_ | c2) => @(c2, piece)
  end

fun _pour1 {ld,lb:agz}{nd:pos}{message,cs:$A.cells}{length:nat | length <= nd}{i:nat | i <= length} .<length - i>.
  (c: ctx1(message), piece: $A.barr(lb, 4096, cs), data: !$A.borrow(byte, ld, nd), length: int length, i: int i)
  : [message_after,cs2:$A.cells] @(ctx1(message_after), $A.barr(lb, 4096, cs2)) =
  if i >= length then @(c, piece)
  else let
    val rest = length - i
    val count = (if rest < 4096 then rest else 4096): [q:pos | q <= 4096; q <= length - i] int q
    val piece = _copy_borrow(piece, data, i, count, 0)
  in
    case+ update1_proved(c, piece, count) of
    | ~Updated1(_ | c2) => _pour1(c2, piece, data, length, i + count)
    | ~Stopped1(_ | c2) => @(c2, piece)
  end

(* The proved incremental SHA-256: proved_init, proved_update with each piece
   of the input in order, then proved_finish; the same as init, update and
   finish but the proved code, and about 30 times slower. It holds a ctx256
   of some message. *)
#pub datavtype proved_ctx =
  | {message:$A.cells} proved_ctx_mk of (ctx256(message))

#pub fn proved_init (): proved_ctx

implement proved_init () = proved_ctx_mk(init256_proved())

(* Hashes data[0, len) after everything given so far (the proved code). A message that has
   reached its largest length (about 2 to the 45 bytes) takes no more. *)
#pub fn proved_update
  {l:agz}{n:pos}{k:nat | k <= n}
  (c: !proved_ctx, data: !$A.arr(byte, l, n), len: int k): void

implement proved_update {l}{n}{k} (c, data, len) = let
  val+ @proved_ctx_mk(inner) = c
  val taken = inner
  val (_ | piece) = $A.barr_alloc(4096)
  val @(next, piece) = _pour256(taken, piece, data, len, 0)
  val () = $A.barr_free(piece)
  val () = inner := next
  prval () = fold@(c)
in end

(* The SHA-256 of everything given, as 64 lowercase hex digits in out (the
   proved code). *)
#pub fn proved_finish {lo:agz} (c: proved_ctx, out: !$A.arr(byte, lo, 64)): void

implement proved_finish {lo} (c, out) = let
  val+ ~proved_ctx_mk(inner) = c
  val (_ | digits) = $A.barr_alloc(64)
  val (_, _ | digits) = finish256_proved(inner, digits)
  val () = _copy_out(digits, out, 64, 0)
  val () = $A.barr_free(digits)
in end

(* The SHA-256 of data[0, data_len) as 64 lowercase hex digits in out (the
   proved code; hash is the fast one). *)
#pub fn proved_hash
  {l:agz}{n:pos}{lo:agz}
  (data: !$A.arr(byte, l, n), data_len: int n,
   out: !$A.arr(byte, lo, 64)): void

implement proved_hash {l}{n}{lo} (data, data_len, out) = let
  val c = proved_init()
  val () = proved_update(c, data, data_len)
in proved_finish(c, out) end

(* The SHA-1 of data[0, data_len) as its 20 bytes, in out. SHA-1 is not fit
   to keep anything secret; it is here for the one thing EPUB asks of it, the
   key of the IDPF font obfuscation (quire#562). *)
#pub fn sha1_digest {l:agz}{n:pos}{data_len:pos | data_len <= n}{lo:agz}
  (data: !$A.borrow(byte, l, n), data_len: int data_len, out: !$A.arr(byte, lo, 20)): void

implement sha1_digest {l}{n}{data_len}{lo} (data, data_len, out) = let
  val (_ | piece) = $A.barr_alloc(4096)
  val @(c, piece) = _pour1(init1_proved(), piece, data, data_len, 0)
  val () = $A.barr_free(piece)
  val (_ | digits) = $A.barr_alloc(20)
  val (_, _ | digits) = finish1_proved(c, digits)
  val () = _copy_out(digits, out, 20, 0)
  val () = $A.barr_free(digits)
in end
