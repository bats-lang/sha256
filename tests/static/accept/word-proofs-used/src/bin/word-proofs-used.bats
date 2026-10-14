#include "share/atspre_staload.hats"
#use arith as AR
#use sha256 as SHA

(* Ch and the upper case sigma 0 of a word, each with its proof: the
   proofs are what a caller reasons from, here that the sigma is one word *)
fn use_proofs {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val (ch_proof | @(ch_high, ch_low)) = $SHA.word_ch(h, l, l, h, h, l)
  val (first | @(a_high, a_low)) = $SHA.big_sigma_0(h, l)
  val (second | @(b_high, b_low)) = $SHA.big_sigma_0(h, l)
  prval $SHA.BIG_SIGMA_0_mk(r2, r13, r22, xor_high, xor_low, xor_high2, xor_low2) = first
  prval $SHA.BIG_SIGMA_0_mk(s2, s13, s22, ys_high, ys_low, ys_high2, ys_low2) = second
  prval () = $AR.rotr_functional(r2, s2)
  prval () = $AR.rotr_functional(r13, s13)
  prval () = $AR.rotr_functional(r22, s22)
  prval () = $AR.xor_functional(xor_high, ys_high)
  prval () = $AR.xor_functional(xor_low, ys_low)
  prval () = $AR.xor_functional(xor_high2, ys_high2)
  prval () = $AR.xor_functional(xor_low2, ys_low2)
in $AR.add_int_int($AR.add_int_int(ch_high, ch_low), $AR.add_int_int(a_high, b_low)) end

implement main0 () = println! (use_proofs(1, 2))
