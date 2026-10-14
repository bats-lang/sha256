(* sha256 -- pure ATS2 SHA-256 implementation *)
(* No C code, no $UNSAFE. 32-bit words are uint: C unsigned arithmetic
   wraps modulo 2^32 by definition, so no operation overflows (signed
   int arithmetic would). Assumes a 32-bit unsigned int, as on every
   bats target (LP64 and ILP32 native, wasm32). *)

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
  val (pa | @(ah, al)) = $AR.rotr(2, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr(13, xh, xl)
  val (pc | @(ch, cl)) = $AR.rotr(22, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (BIG_SIGMA_0_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun big_sigma_1 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (BIG_SIGMA_1(xh, xl, rh, rl) | @(int rh, int rl))

implement big_sigma_1 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr(6, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr(11, xh, xl)
  val (pc | @(ch, cl)) = $AR.rotr(25, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (BIG_SIGMA_1_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun small_sigma_0 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (SMALL_SIGMA_0(xh, xl, rh, rl) | @(int rh, int rl))

implement small_sigma_0 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr(7, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr(18, xh, xl)
  val (pc | @(ch, cl)) = $AR.shr(3, xh, xl)
  val (psh, psl | @(sh, sl)) = $AR.xor32(ah, al, bh, bl)
  val (prh, prl | @(rh, rl)) = $AR.xor32(sh, sl, ch, cl)
in (SMALL_SIGMA_0_mk(pa, pb, pc, psh, psl, prh, prl) | @(rh, rl)) end

#pub fun small_sigma_1 {xh,xl:nat | xh < 65536; xl < 65536} (xh: int xh, xl: int xl)
  : [rh,rl:nat | rh < 65536; rl < 65536] (SMALL_SIGMA_1(xh, xl, rh, rl) | @(int rh, int rl))

implement small_sigma_1 (xh, xl) = let
  val (pa | @(ah, al)) = $AR.rotr(17, xh, xl)
  val (pb | @(bh, bl)) = $AR.rotr(19, xh, xl)
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
    val (turned | @(high, low)) = $AR.rotr(31, x3_high, x3_low)
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

(* SHA256_K(t, high, low): the constant K_t of SHA-256 (section 4.2.2) is
   the word high:low. The standard defines the 64 constants as the first 32
   bits of the fractional parts of the cube roots of the first 64 primes; the
   table states them as the standard prints them, and the compiler checks
   that the rounds use the table's word for round t and no other. That each is
   what the definition says is NOT proved: the proof needs integers of 2 to
   the 100, which the 32-bit solver cannot hold. It is tested against the
   integer cube roots (tests/dynamic/constants) and owed (a p2 issue). *)
#pub dataprop SHA256_K(int, int, int) =
  | SHA256_K_0(0, 0x428a, 0x2f98)
  | SHA256_K_1(1, 0x7137, 0x4491)
  | SHA256_K_2(2, 0xb5c0, 0xfbcf)
  | SHA256_K_3(3, 0xe9b5, 0xdba5)
  | SHA256_K_4(4, 0x3956, 0xc25b)
  | SHA256_K_5(5, 0x59f1, 0x11f1)
  | SHA256_K_6(6, 0x923f, 0x82a4)
  | SHA256_K_7(7, 0xab1c, 0x5ed5)
  | SHA256_K_8(8, 0xd807, 0xaa98)
  | SHA256_K_9(9, 0x1283, 0x5b01)
  | SHA256_K_10(10, 0x2431, 0x85be)
  | SHA256_K_11(11, 0x550c, 0x7dc3)
  | SHA256_K_12(12, 0x72be, 0x5d74)
  | SHA256_K_13(13, 0x80de, 0xb1fe)
  | SHA256_K_14(14, 0x9bdc, 0x06a7)
  | SHA256_K_15(15, 0xc19b, 0xf174)
  | SHA256_K_16(16, 0xe49b, 0x69c1)
  | SHA256_K_17(17, 0xefbe, 0x4786)
  | SHA256_K_18(18, 0x0fc1, 0x9dc6)
  | SHA256_K_19(19, 0x240c, 0xa1cc)
  | SHA256_K_20(20, 0x2de9, 0x2c6f)
  | SHA256_K_21(21, 0x4a74, 0x84aa)
  | SHA256_K_22(22, 0x5cb0, 0xa9dc)
  | SHA256_K_23(23, 0x76f9, 0x88da)
  | SHA256_K_24(24, 0x983e, 0x5152)
  | SHA256_K_25(25, 0xa831, 0xc66d)
  | SHA256_K_26(26, 0xb003, 0x27c8)
  | SHA256_K_27(27, 0xbf59, 0x7fc7)
  | SHA256_K_28(28, 0xc6e0, 0x0bf3)
  | SHA256_K_29(29, 0xd5a7, 0x9147)
  | SHA256_K_30(30, 0x06ca, 0x6351)
  | SHA256_K_31(31, 0x1429, 0x2967)
  | SHA256_K_32(32, 0x27b7, 0x0a85)
  | SHA256_K_33(33, 0x2e1b, 0x2138)
  | SHA256_K_34(34, 0x4d2c, 0x6dfc)
  | SHA256_K_35(35, 0x5338, 0x0d13)
  | SHA256_K_36(36, 0x650a, 0x7354)
  | SHA256_K_37(37, 0x766a, 0x0abb)
  | SHA256_K_38(38, 0x81c2, 0xc92e)
  | SHA256_K_39(39, 0x9272, 0x2c85)
  | SHA256_K_40(40, 0xa2bf, 0xe8a1)
  | SHA256_K_41(41, 0xa81a, 0x664b)
  | SHA256_K_42(42, 0xc24b, 0x8b70)
  | SHA256_K_43(43, 0xc76c, 0x51a3)
  | SHA256_K_44(44, 0xd192, 0xe819)
  | SHA256_K_45(45, 0xd699, 0x0624)
  | SHA256_K_46(46, 0xf40e, 0x3585)
  | SHA256_K_47(47, 0x106a, 0xa070)
  | SHA256_K_48(48, 0x19a4, 0xc116)
  | SHA256_K_49(49, 0x1e37, 0x6c08)
  | SHA256_K_50(50, 0x2748, 0x774c)
  | SHA256_K_51(51, 0x34b0, 0xbcb5)
  | SHA256_K_52(52, 0x391c, 0x0cb3)
  | SHA256_K_53(53, 0x4ed8, 0xaa4a)
  | SHA256_K_54(54, 0x5b9c, 0xca4f)
  | SHA256_K_55(55, 0x682e, 0x6ff3)
  | SHA256_K_56(56, 0x748f, 0x82ee)
  | SHA256_K_57(57, 0x78a5, 0x636f)
  | SHA256_K_58(58, 0x84c8, 0x7814)
  | SHA256_K_59(59, 0x8cc7, 0x0208)
  | SHA256_K_60(60, 0x90be, 0xfffa)
  | SHA256_K_61(61, 0xa450, 0x6ceb)
  | SHA256_K_62(62, 0xbef9, 0xa3f7)
  | SHA256_K_63(63, 0xc671, 0x78f2)

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
              (SHA256_K_0() | @(0x428a, 0x2f98))
            else
              (SHA256_K_1() | @(0x7137, 0x4491))
          else
            if $AR.lt_g1(t, 3) then
              (SHA256_K_2() | @(0xb5c0, 0xfbcf))
            else
              (SHA256_K_3() | @(0xe9b5, 0xdba5))
        else
          if $AR.lt_g1(t, 6) then
            if $AR.lt_g1(t, 5) then
              (SHA256_K_4() | @(0x3956, 0xc25b))
            else
              (SHA256_K_5() | @(0x59f1, 0x11f1))
          else
            if $AR.lt_g1(t, 7) then
              (SHA256_K_6() | @(0x923f, 0x82a4))
            else
              (SHA256_K_7() | @(0xab1c, 0x5ed5))
      else
        if $AR.lt_g1(t, 12) then
          if $AR.lt_g1(t, 10) then
            if $AR.lt_g1(t, 9) then
              (SHA256_K_8() | @(0xd807, 0xaa98))
            else
              (SHA256_K_9() | @(0x1283, 0x5b01))
          else
            if $AR.lt_g1(t, 11) then
              (SHA256_K_10() | @(0x2431, 0x85be))
            else
              (SHA256_K_11() | @(0x550c, 0x7dc3))
        else
          if $AR.lt_g1(t, 14) then
            if $AR.lt_g1(t, 13) then
              (SHA256_K_12() | @(0x72be, 0x5d74))
            else
              (SHA256_K_13() | @(0x80de, 0xb1fe))
          else
            if $AR.lt_g1(t, 15) then
              (SHA256_K_14() | @(0x9bdc, 0x06a7))
            else
              (SHA256_K_15() | @(0xc19b, 0xf174))
    else
      if $AR.lt_g1(t, 24) then
        if $AR.lt_g1(t, 20) then
          if $AR.lt_g1(t, 18) then
            if $AR.lt_g1(t, 17) then
              (SHA256_K_16() | @(0xe49b, 0x69c1))
            else
              (SHA256_K_17() | @(0xefbe, 0x4786))
          else
            if $AR.lt_g1(t, 19) then
              (SHA256_K_18() | @(0x0fc1, 0x9dc6))
            else
              (SHA256_K_19() | @(0x240c, 0xa1cc))
        else
          if $AR.lt_g1(t, 22) then
            if $AR.lt_g1(t, 21) then
              (SHA256_K_20() | @(0x2de9, 0x2c6f))
            else
              (SHA256_K_21() | @(0x4a74, 0x84aa))
          else
            if $AR.lt_g1(t, 23) then
              (SHA256_K_22() | @(0x5cb0, 0xa9dc))
            else
              (SHA256_K_23() | @(0x76f9, 0x88da))
      else
        if $AR.lt_g1(t, 28) then
          if $AR.lt_g1(t, 26) then
            if $AR.lt_g1(t, 25) then
              (SHA256_K_24() | @(0x983e, 0x5152))
            else
              (SHA256_K_25() | @(0xa831, 0xc66d))
          else
            if $AR.lt_g1(t, 27) then
              (SHA256_K_26() | @(0xb003, 0x27c8))
            else
              (SHA256_K_27() | @(0xbf59, 0x7fc7))
        else
          if $AR.lt_g1(t, 30) then
            if $AR.lt_g1(t, 29) then
              (SHA256_K_28() | @(0xc6e0, 0x0bf3))
            else
              (SHA256_K_29() | @(0xd5a7, 0x9147))
          else
            if $AR.lt_g1(t, 31) then
              (SHA256_K_30() | @(0x06ca, 0x6351))
            else
              (SHA256_K_31() | @(0x1429, 0x2967))
  else
    if $AR.lt_g1(t, 48) then
      if $AR.lt_g1(t, 40) then
        if $AR.lt_g1(t, 36) then
          if $AR.lt_g1(t, 34) then
            if $AR.lt_g1(t, 33) then
              (SHA256_K_32() | @(0x27b7, 0x0a85))
            else
              (SHA256_K_33() | @(0x2e1b, 0x2138))
          else
            if $AR.lt_g1(t, 35) then
              (SHA256_K_34() | @(0x4d2c, 0x6dfc))
            else
              (SHA256_K_35() | @(0x5338, 0x0d13))
        else
          if $AR.lt_g1(t, 38) then
            if $AR.lt_g1(t, 37) then
              (SHA256_K_36() | @(0x650a, 0x7354))
            else
              (SHA256_K_37() | @(0x766a, 0x0abb))
          else
            if $AR.lt_g1(t, 39) then
              (SHA256_K_38() | @(0x81c2, 0xc92e))
            else
              (SHA256_K_39() | @(0x9272, 0x2c85))
      else
        if $AR.lt_g1(t, 44) then
          if $AR.lt_g1(t, 42) then
            if $AR.lt_g1(t, 41) then
              (SHA256_K_40() | @(0xa2bf, 0xe8a1))
            else
              (SHA256_K_41() | @(0xa81a, 0x664b))
          else
            if $AR.lt_g1(t, 43) then
              (SHA256_K_42() | @(0xc24b, 0x8b70))
            else
              (SHA256_K_43() | @(0xc76c, 0x51a3))
        else
          if $AR.lt_g1(t, 46) then
            if $AR.lt_g1(t, 45) then
              (SHA256_K_44() | @(0xd192, 0xe819))
            else
              (SHA256_K_45() | @(0xd699, 0x0624))
          else
            if $AR.lt_g1(t, 47) then
              (SHA256_K_46() | @(0xf40e, 0x3585))
            else
              (SHA256_K_47() | @(0x106a, 0xa070))
    else
      if $AR.lt_g1(t, 56) then
        if $AR.lt_g1(t, 52) then
          if $AR.lt_g1(t, 50) then
            if $AR.lt_g1(t, 49) then
              (SHA256_K_48() | @(0x19a4, 0xc116))
            else
              (SHA256_K_49() | @(0x1e37, 0x6c08))
          else
            if $AR.lt_g1(t, 51) then
              (SHA256_K_50() | @(0x2748, 0x774c))
            else
              (SHA256_K_51() | @(0x34b0, 0xbcb5))
        else
          if $AR.lt_g1(t, 54) then
            if $AR.lt_g1(t, 53) then
              (SHA256_K_52() | @(0x391c, 0x0cb3))
            else
              (SHA256_K_53() | @(0x4ed8, 0xaa4a))
          else
            if $AR.lt_g1(t, 55) then
              (SHA256_K_54() | @(0x5b9c, 0xca4f))
            else
              (SHA256_K_55() | @(0x682e, 0x6ff3))
      else
        if $AR.lt_g1(t, 60) then
          if $AR.lt_g1(t, 58) then
            if $AR.lt_g1(t, 57) then
              (SHA256_K_56() | @(0x748f, 0x82ee))
            else
              (SHA256_K_57() | @(0x78a5, 0x636f))
          else
            if $AR.lt_g1(t, 59) then
              (SHA256_K_58() | @(0x84c8, 0x7814))
            else
              (SHA256_K_59() | @(0x8cc7, 0x0208))
        else
          if $AR.lt_g1(t, 62) then
            if $AR.lt_g1(t, 61) then
              (SHA256_K_60() | @(0x90be, 0xfffa))
            else
              (SHA256_K_61() | @(0xa450, 0x6ceb))
          else
            if $AR.lt_g1(t, 63) then
              (SHA256_K_62() | @(0xbef9, 0xa3f7))
            else
              (SHA256_K_63() | @(0xc671, 0x78f2))

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
   and tested (tests/dynamic/constants), not proved against the definition
   (the proof needs integers of 2 to the 61 and more); owed, a p2 issue. *)
#pub dataprop SHA1_K(int, int, int) =
  | {t:nat | 0 <= t; t <= 19} SHA1_K_0_to_19(t, 0x5a82, 0x7999)
  | {t:nat | 20 <= t; t <= 39} SHA1_K_20_to_39(t, 0x6ed9, 0xeba1)
  | {t:nat | 40 <= t; t <= 59} SHA1_K_40_to_59(t, 0x8f1b, 0xbcdc)
  | {t:nat | 60 <= t; t <= 79} SHA1_K_60_to_79(t, 0xca62, 0xc1d6)

(* The constant of round t, with the proof that it is the table's *)
#pub fun sha1_k {t:nat | t < 80} (t: int t)
  : [high,low:nat | high < 65536; low < 65536] (SHA1_K(t, high, low) | @(int high, int low))

implement sha1_k {t} (t) =
  if $AR.lt_g1(t, 20) then (SHA1_K_0_to_19() | @(0x5a82, 0x7999))
  else if $AR.lt_g1(t, 40) then (SHA1_K_20_to_39() | @(0x6ed9, 0xeba1))
  else if $AR.lt_g1(t, 60) then (SHA1_K_40_to_59() | @(0x8f1b, 0xbcdc))
  else (SHA1_K_60_to_79() | @(0xca62, 0xc1d6))

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
  val (turn | @(turn5_high, turn5_low)) = $AR.rotr(27, a_high, a_low)
  val (function | @(f_high, f_low)) = sha1_f(t, b_high, b_low, c_high, c_low, d_high, d_low)
  val (add1 | @(sum1_high, sum1_low)) = $AR.add32(turn5_high, turn5_low, f_high, f_low)
  val (add2 | @(sum2_high, sum2_low)) = $AR.add32(sum1_high, sum1_low, e_high, e_low)
  val (add3 | @(sum3_high, sum3_low)) = $AR.add32(sum2_high, sum2_low, k_high, k_low)
  val (add4 | @(new_a_high, new_a_low)) = $AR.add32(sum3_high, sum3_low, w_high, w_low)
  val (turn30 | @(new_c_high, new_c_low)) = $AR.rotr(2, b_high, b_low)
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
   SHA-1 (FIPS 180-4, section 6.1), beside SHA-256

   Written, not proved: its tests are known answers (tests/dynamic/sha1),
   and the proof against a specification relation checked by the compiler
   is owed (see the issue filed for it). SHA-1 is not fit to keep
   anything secret; it is here for the one thing EPUB asks of it, the key
   of the IDPF font obfuscation (quire#562).
   ============================================================ *)


(* The SHA-1 of data[0, data_len) as its 20 bytes, in out *)
#pub fn sha1_digest {l:agz}{n:pos}{data_len:pos | data_len <= n}{lo:agz}
  (data: !$A.borrow(byte, l, n), data_len: int data_len, out: !$A.arr(byte, lo, 20)): void

fn _sha1_rotl {k:int | 0 < k; k < 32} (x: uint, k: int k): uint =
  (x << k) lor (x >> (32 - k))

fn _sha1_word (x: int): uint = g0int2uint_int_uint(x)

(* The low byte of x *)
fn _sha1_byte (x: uint): [v:nat | v < 256] int v =
  $AR.low_byte(g0uint2int_uint_int(x land 0xffu))

(* The constant of round t (FIPS 180-4, section 4.2.1) *)
fn _sha1_constant {t:nat | t < 80} (t: int t): uint =
  if t < 20 then 0x5a827999u
  else if t < 40 then 0x6ed9eba1u
  else if t < 60 then 0x8f1bbcdcu
  else 0xca62c1d6u

(* The function of round t (section 4.1.1) *)
fn _sha1_mix {t:nat | t < 80} (t: int t, b: uint, c: uint, d: uint): uint =
  if t < 20 then (b land c) lor ((lnot b) land d)
  else if t < 40 then b lxor c lxor d
  else if t < 60 then (b land c) lor (b land d) lor (c land d)
  else b lxor c lxor d

(* The five words of the hash sha1_state *)
typedef sha1_state = @(uint, uint, uint, uint, uint)

(* Processes the block data[block_at, block_at + 64) into the sha1_state, with w as the
   message schedule (section 6.1.2) *)
fn _sha1_compress {ld:agz}{nd:pos}{block_at:nat | block_at + 64 <= nd}{lw:agz}
  (data: !$A.arr(byte, ld, nd), block_at: int block_at,
   w: !$A.arr(uint, lw, 80), h: sha1_state): sha1_state = let
  fun load {t:nat | t <= 16} .<16 - t>.
    (data: !$A.arr(byte, ld, nd), w: !$A.arr(uint, lw, 80), t: int t): void =
    if t >= 16 then ()
    else let
      val at = block_at + 4 * t
      val byte0 = _sha1_word(byte2int0($A.get<byte>(data, at)))
      val byte1 = _sha1_word(byte2int0($A.get<byte>(data, at + 1)))
      val byte2 = _sha1_word(byte2int0($A.get<byte>(data, at + 2)))
      val byte3 = _sha1_word(byte2int0($A.get<byte>(data, at + 3)))
      val () = $A.set<uint>(w, t, (byte0 << 24) lor (byte1 << 16) lor (byte2 << 8) lor byte3)
    in load(data, w, t + 1) end
  fun expand {t:int | 16 <= t; t <= 80} .<80 - t>.
    (w: !$A.arr(uint, lw, 80), t: int t): void =
    if t >= 80 then ()
    else let
      val mixed = $A.get<uint>(w, t - 3) lxor $A.get<uint>(w, t - 8) lxor $A.get<uint>(w, t - 14) lxor $A.get<uint>(w, t - 16)
      val () = $A.set<uint>(w, t, _sha1_rotl(mixed, 1))
    in expand(w, t + 1) end
  fun rounds {t:nat | t <= 80} .<80 - t>.
    (w: !$A.arr(uint, lw, 80), t: int t, a: uint, b: uint, c: uint, d: uint, e: uint): sha1_state =
    if t >= 80 then @(a, b, c, d, e)
    else let
      val temporary = _sha1_rotl(a, 5) + _sha1_mix(t, b, c, d) + e + _sha1_constant(t) + $A.get<uint>(w, t)
    in rounds(w, t + 1, temporary, a, _sha1_rotl(b, 30), c, d) end
  val () = load(data, w, 0)
  val () = expand(w, 16)
  val @(h0, h1, h2, h3, h4) = h
  val @(a, b, c, d, e) = rounds(w, 0, h0, h1, h2, h3, h4)
in @(h0 + a, h1 + b, h2 + c, h3 + d, h4 + e) end

(* data[from, stop) appended to the block in block[0, filled), each block
   compressed as it fills; the bytes left in the block, and the sha1_state *)
fun _sha1_fill {lw,lb,ld:agz}{n:pos}{stop:nat | stop <= n}{from:nat | from <= stop}{filled:nat | filled < 64} .<stop - from>.
  (h: sha1_state, w: !$A.arr(uint, lw, 80), block: !$A.arr(byte, lb, 64),
   data: !$A.borrow(byte, ld, n), stop: int stop, from: int from, filled: int filled): @([left:nat | left < 64] int left, sha1_state) =
  if from >= stop then @(filled, h)
  else let
    val () = $A.set<byte>(block, filled, $A.read<byte>(data, from))
  in
    if filled + 1 >= 64 then let
      val next = _sha1_compress(block, 0, w, h)
    in _sha1_fill(next, w, block, data, stop, from + 1, 0) end
    else _sha1_fill(h, w, block, data, stop, from + 1, filled + 1)
  end

(* The word x as four bytes at out[at, at + 4), the high one first *)
fn _sha1_put_word {lo:agz}{at:nat | at + 4 <= 20} (out: !$A.arr(byte, lo, 20), at: int at, x: uint): void = let
  val () = $A.set<byte>(out, at, $A.int2byte(_sha1_byte(x >> 24)))
  val () = $A.set<byte>(out, at + 1, $A.int2byte(_sha1_byte(x >> 16)))
  val () = $A.set<byte>(out, at + 2, $A.int2byte(_sha1_byte(x >> 8)))
in $A.set<byte>(out, at + 3, $A.int2byte(_sha1_byte(x))) end

(* The one or two blocks of padding in padding[0, last), compressed into the sha1_state *)
fn _sha1_compress_padding {lp,lw:agz}{last:int | last == 64 || last == 128}
  (padding: !$A.arr(byte, lp, 128), last: int last, w: !$A.arr(uint, lw, 80), h: sha1_state): sha1_state = let
  val first = _sha1_compress(padding, 0, w, h)
in if last = 128 then _sha1_compress(padding, 64, w, first) else first end

(* The buffers of a digest given back *)
fn _sha1_release {lp,lb,lw:agz} (padding: $A.arr(byte, lp, 128), block: $A.arr(byte, lb, 64), w: $A.arr(uint, lw, 80)): void = let
  val () = $A.free<byte>(padding)
  val () = $A.free<byte>(block)
in $A.free<uint>(w) end

fn _sha1_digest {l:agz}{n:pos}{data_len:pos | data_len <= n}{lo:agz}
  (data: !$A.borrow(byte, l, n), data_len: int data_len, out: !$A.arr(byte, lo, 20)): void = let
  val w = $A.alloc<uint>(80): [lw:agz] $A.arr(uint, lw, 80)
  val block = $A.alloc<byte>(64): [lb:agz] $A.arr(byte, lb, 64)
  val initial = @(0x67452301u, 0xefcdab89u, 0x98badcfeu, 0x10325476u, 0xc3d2e1f0u): sha1_state
  val @(tail, filled_state) = _sha1_fill(initial, w, block, data, data_len, 0, 0)
  (* the tail, 0x80, zeros and the length in bits as 64 bits, big endian,
     in one block or two (alloc zeroes what it gives) *)
  val padding = $A.alloc<byte>(128): [lp:agz] $A.arr(byte, lp, 128)
  fun copy {lp,lb:agz}{tail:nat | tail < 64}{i:nat | i <= tail} .<tail - i>.
    (block: !$A.arr(byte, lb, 64), padding: !$A.arr(byte, lp, 128), tail: int tail, i: int i): void =
    if i >= tail then ()
    else let
      val () = $A.set<byte>(padding, i, $A.get<byte>(block, i))
    in copy(block, padding, tail, i + 1) end
  val () = copy(block, padding, tail, 0)
  val () = $A.set<byte>(padding, tail, $A.int2byte(128))
  val last = (if tail + 9 > 64 then 128 else 64): [last:int | last == 64 || last == 128] int last
  val length = _sha1_word(data_len)
  val bits_high = length >> 29
  val bits_low = length << 3
  val () = $A.set<byte>(padding, last - 8, $A.int2byte(_sha1_byte(bits_high >> 24)))
  val () = $A.set<byte>(padding, last - 7, $A.int2byte(_sha1_byte(bits_high >> 16)))
  val () = $A.set<byte>(padding, last - 6, $A.int2byte(_sha1_byte(bits_high >> 8)))
  val () = $A.set<byte>(padding, last - 5, $A.int2byte(_sha1_byte(bits_high)))
  val () = $A.set<byte>(padding, last - 4, $A.int2byte(_sha1_byte(bits_low >> 24)))
  val () = $A.set<byte>(padding, last - 3, $A.int2byte(_sha1_byte(bits_low >> 16)))
  val () = $A.set<byte>(padding, last - 2, $A.int2byte(_sha1_byte(bits_low >> 8)))
  val () = $A.set<byte>(padding, last - 1, $A.int2byte(_sha1_byte(bits_low)))
  val @(h0, h1, h2, h3, h4) = _sha1_compress_padding(padding, last, w, filled_state)
  val () = _sha1_put_word(out, 0, h0)
  val () = _sha1_put_word(out, 4, h1)
  val () = _sha1_put_word(out, 8, h2)
  val () = _sha1_put_word(out, 12, h3)
  val () = _sha1_put_word(out, 16, h4)
in _sha1_release(padding, block, w) end

implement sha1_digest (data, data_len, out) = _sha1_digest(data, data_len, out)
