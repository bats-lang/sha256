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
