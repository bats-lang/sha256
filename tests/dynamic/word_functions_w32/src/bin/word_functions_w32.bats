#include "share/atspre_staload.hats"
#use arith as AR
#use sha256 as SHA

(* The proved word functions (Ch, Maj, the four sigmas) on the published
   trace of SHA-256 over "abc" (FIPS 180-2 appendix B.1; the values were
   also made by an independent implementation that hashes "abc" to the
   known digest): the first two rounds and the first message schedule
   words beyond the block. Each word is given as its halves. Prints the
   result; the harness compares it with `expected`. *)
fn plus(a: int, b: int): int = $AR.add_int_int(a, b)

fn bad(ok: bool): int = if ok then 0 else 1

(* a word as its halves, from its four bytes *)
fn halves {h,l:nat | h < 65536; l < 65536} (w: $AR.word32(h, l)): @(int, int) = let
  val (_ | b0) = $AR.word32_byte(w, 0)
  val (_ | b1) = $AR.word32_byte(w, 1)
  val (_ | b2) = $AR.word32_byte(w, 2)
  val (_ | b3) = $AR.word32_byte(w, 3)
in @(256 * b0 + b1, 256 * b2 + b3) end

fn is {h,l:nat | h < 65536; l < 65536} (w: $AR.word32(h, l), want_h: int, want_l: int): int = let
  val @(have_h, have_l) = halves(w)
in bad($AR.eq_int_int(have_h, want_h) andalso $AR.eq_int_int(have_l, want_l)) end

(* one round of section 6.2.2: the new a and the new e, from the words
   a..h, k and w *)
fn round_a_e {ah,al,bh,bl,ch,cl,dh,dl,eh,el,fh,fl,gh,gl,hh,hl,kh,kl,wh,wl:nat |
    ah < 65536; al < 65536; bh < 65536; bl < 65536; ch < 65536; cl < 65536; dh < 65536; dl < 65536;
    eh < 65536; el < 65536; fh < 65536; fl < 65536; gh < 65536; gl < 65536; hh < 65536; hl < 65536;
    kh < 65536; kl < 65536; wh < 65536; wl < 65536}
  (a: $AR.word32(ah, al), b: $AR.word32(bh, bl), c: $AR.word32(ch, cl), d: $AR.word32(dh, dl),
   e: $AR.word32(eh, el), f: $AR.word32(fh, fl), g: $AR.word32(gh, gl), h: $AR.word32(hh, hl),
   k: $AR.word32(kh, kl), w: $AR.word32(wh, wl)): @(int, int, int, int) = let
  val (_ | s1) = $SHA.big_sigma_1_w32(e)
  val (_ | ch) = $SHA.word_ch_w32(e, f, g)
  val (_ | t1a) = $AR.word32_add(h, s1)
  val (_ | t1b) = $AR.word32_add(t1a, ch)
  val (_ | t1c) = $AR.word32_add(t1b, k)
  val (_ | t1) = $AR.word32_add(t1c, w)
  val (_ | s0) = $SHA.big_sigma_0_w32(a)
  val (_ | mj) = $SHA.word_maj_w32(a, b, c)
  val (_ | t2) = $AR.word32_add(s0, mj)
  val (_ | na) = $AR.word32_add(t1, t2)
  val (_ | ne) = $AR.word32_add(d, t1)
  val @(nah, nal) = halves(na)
  val @(neh, nel) = halves(ne)
in @(nah, nal, neh, nel) end

implement main0 () = let
  (* the pieces of round 0, from the trace *)
  val (_ | s1) = $SHA.big_sigma_1_w32($AR.word32_pack(81, 14, 82, 127))
  val (_ | chv) = $SHA.word_ch_w32($AR.word32_pack(81, 14, 82, 127), $AR.word32_pack(155, 5, 104, 140), $AR.word32_pack(31, 131, 217, 171))
  val (_ | s0) = $SHA.big_sigma_0_w32($AR.word32_pack(106, 9, 230, 103))
  val (_ | mj) = $SHA.word_maj_w32($AR.word32_pack(106, 9, 230, 103), $AR.word32_pack(187, 103, 174, 133), $AR.word32_pack(60, 110, 243, 114))
  val pieces = plus(plus(is(s1, 13703, 10027), is(chv, 8069, 51596)),
                    plus(is(s0, 52768, 46206), is(mj, 14959, 58983)))
  (* round 0 and then round 1 *)
  val @(a1h, a1l, e1h, e1l) = round_a_e($AR.word32_pack(106, 9, 230, 103), $AR.word32_pack(187, 103, 174, 133), $AR.word32_pack(60, 110, 243, 114), $AR.word32_pack(165, 79, 245, 58),
    $AR.word32_pack(81, 14, 82, 127), $AR.word32_pack(155, 5, 104, 140), $AR.word32_pack(31, 131, 217, 171), $AR.word32_pack(91, 224, 205, 25), $AR.word32_pack(66, 138, 47, 152), $AR.word32_pack(97, 98, 99, 128))
  val round0 = plus(plus(bad(a1h = 23914), bad(a1l = 60365)), plus(bad(e1h = 64042), bad(e1l = 17954)))
  val @(a2h, a2l, e2h, e2l) = round_a_e($AR.word32_pack(93, 106, 235, 205), $AR.word32_pack(106, 9, 230, 103), $AR.word32_pack(187, 103, 174, 133), $AR.word32_pack(60, 110, 243, 114),
    $AR.word32_pack(250, 42, 70, 34), $AR.word32_pack(81, 14, 82, 127), $AR.word32_pack(155, 5, 104, 140), $AR.word32_pack(31, 131, 217, 171), $AR.word32_pack(113, 55, 68, 145), $AR.word32_pack(0, 0, 0, 0))
  val round1 = plus(plus(bad(a2h = 23146), bad(a2l = 55725)), plus(bad(e2h = 30926), bad(e2l = 31113)))
  (* the small sigmas of the message words *)
  val (_ | r0) = $SHA.small_sigma_0_w32($AR.word32_pack(97, 98, 99, 128))
  val (_ | r1) = $SHA.small_sigma_1_w32($AR.word32_pack(97, 98, 99, 128))
  val (_ | r2) = $SHA.small_sigma_1_w32($AR.word32_pack(0, 0, 0, 24))
  val sigmas = plus(plus(is(r0, 37902, 37103), is(r1, 32168, 25605)), is(r2, 15, 0))
  val failed = plus(plus(pieces, round0), plus(round1, sigmas))
in
  if failed = 0 then println! ("word_functions: all values agree")
  else let val () = println! ("FAIL word_functions: ", failed, " values differ") in exit_void(1) end
end
