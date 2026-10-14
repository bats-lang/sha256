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

fn is (h: int, l: int, want_h: int, want_l: int): int =
  bad($AR.eq_int_int(h, want_h) andalso $AR.eq_int_int(l, want_l))

(* one round of section 6.2.2: the new a and the new e, from the words
   a..h, k and w, each as its halves *)
fn round_a_e {ah,al,bh,bl,ch,cl,dh,dl,eh,el,fh,fl,gh,gl,hh,hl,kh,kl,wh,wl:nat |
    ah < 65536; al < 65536; bh < 65536; bl < 65536; ch < 65536; cl < 65536; dh < 65536; dl < 65536;
    eh < 65536; el < 65536; fh < 65536; fl < 65536; gh < 65536; gl < 65536; hh < 65536; hl < 65536;
    kh < 65536; kl < 65536; wh < 65536; wl < 65536}
  (ah: int ah, al: int al, bh: int bh, bl: int bl, ch: int ch, cl: int cl, dh: int dh, dl: int dl,
   eh: int eh, el: int el, fh: int fh, fl: int fl, gh: int gh, gl: int gl, hh: int hh, hl: int hl,
   kh: int kh, kl: int kl, wh: int wh, wl: int wl): @(int, int, int, int) = let
  val (_ | @(s1h, s1l)) = $SHA.big_sigma_1(eh, el)
  val (_ | @(chh, chl)) = $SHA.word_ch(eh, el, fh, fl, gh, gl)
  val (_ | @(t1ah, t1al)) = $AR.add32(hh, hl, s1h, s1l)
  val (_ | @(t1bh, t1bl)) = $AR.add32(t1ah, t1al, chh, chl)
  val (_ | @(t1ch, t1cl)) = $AR.add32(t1bh, t1bl, kh, kl)
  val (_ | @(t1h, t1l)) = $AR.add32(t1ch, t1cl, wh, wl)
  val (_ | @(s0h, s0l)) = $SHA.big_sigma_0(ah, al)
  val (_ | @(mjh, mjl)) = $SHA.word_maj(ah, al, bh, bl, ch, cl)
  val (_ | @(t2h, t2l)) = $AR.add32(s0h, s0l, mjh, mjl)
  val (_ | @(nah, nal)) = $AR.add32(t1h, t1l, t2h, t2l)
  val (_ | @(neh, nel)) = $AR.add32(dh, dl, t1h, t1l)
in @(nah, nal, neh, nel) end

implement main0 () = let
  (* the pieces of round 0, from the trace *)
  val (_ | @(s1h, s1l)) = $SHA.big_sigma_1(20750, 21119)
  val (_ | @(chh, chl)) = $SHA.word_ch(20750, 21119, 39685, 26764, 8067, 55723)
  val (_ | @(s0h, s0l)) = $SHA.big_sigma_0(27145, 58983)
  val (_ | @(mjh, mjl)) = $SHA.word_maj(27145, 58983, 47975, 44677, 15470, 62322)
  val pieces = plus(plus(is(s1h, s1l, 13703, 10027), is(chh, chl, 8069, 51596)),
                    plus(is(s0h, s0l, 52768, 46206), is(mjh, mjl, 14959, 58983)))
  (* round 0 and then round 1 *)
  val @(a1h, a1l, e1h, e1l) = round_a_e(27145, 58983, 47975, 44677, 15470, 62322, 42319, 62778,
    20750, 21119, 39685, 26764, 8067, 55723, 23520, 52505, 17034, 12184, 24930, 25472)
  val round0 = plus(is(a1h, a1l, 23914, 60365), is(e1h, e1l, 64042, 17954))
  val @(a2h, a2l, e2h, e2l) = round_a_e(23914, 60365, 27145, 58983, 47975, 44677, 15470, 62322,
    64042, 17954, 20750, 21119, 39685, 26764, 8067, 55723, 28983, 17553, 0, 0)
  val round1 = plus(is(a2h, a2l, 23146, 55725), is(e2h, e2l, 30926, 31113))
  (* the small sigmas of the message words *)
  val (_ | @(r0h, r0l)) = $SHA.small_sigma_0(24930, 25472)
  val (_ | @(r1h, r1l)) = $SHA.small_sigma_1(24930, 25472)
  val (_ | @(r2h, r2l)) = $SHA.small_sigma_1(0, 24)
  val sigmas = plus(plus(is(r0h, r0l, 37902, 37103), is(r1h, r1l, 32168, 25605)), is(r2h, r2l, 15, 0))
  val failed = plus(plus(pieces, round0), plus(round1, sigmas))
in
  if failed = 0 then println! ("word_functions: all values agree")
  else let val () = println! ("FAIL word_functions: ", failed, " values differ") in exit_void(1) end
end
