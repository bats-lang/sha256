#include "share/atspre_staload.hats"
#use arith as AR
#use sha256 as SHA

(* Ch and the upper case sigma 0 of a word, each with its proof: the
   proofs are what a caller reasons from, here that the sigma is one word *)
fn use_proofs {h,l:nat | h < 65536; l < 65536} (x: $AR.word32(h, l)): int = let
  val (ch_proof | ch_word) = $SHA.word_ch_w32(x, x, x)
  val (first | a_word) = $SHA.big_sigma_0_w32(x)
  val (second | b_word) = $SHA.big_sigma_0_w32(x)
  prval $SHA.BIG_SIGMA_0_mk(r2, r13, r22, xor_high, xor_low, xor_high2, xor_low2) = first
  prval $SHA.BIG_SIGMA_0_mk(s2, s13, s22, ys_high, ys_low, ys_high2, ys_low2) = second
  prval () = $AR.rotr_functional(r2, s2)
  prval () = $AR.rotr_functional(r13, s13)
  prval () = $AR.rotr_functional(r22, s22)
  prval () = $AR.xor_functional(xor_high, ys_high)
  prval () = $AR.xor_functional(xor_low, ys_low)
  prval () = $AR.xor_functional(xor_high2, ys_high2)
  prval () = $AR.xor_functional(xor_low2, ys_low2)
  val (_ | ch_byte) = $AR.word32_byte(ch_word, 1)
  val (_ | a_byte) = $AR.word32_byte(a_word, 0)
  val (_ | b_byte) = $AR.word32_byte(b_word, 3)
in $AR.add_int_int($AR.add_int_int(ch_byte, a_byte), b_byte) end

implement main0 () = println! (use_proofs($AR.word32_pack(0, 1, 0, 2)))
