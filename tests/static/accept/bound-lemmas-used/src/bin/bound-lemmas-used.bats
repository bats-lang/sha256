#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the bound lemmas are used as the digest uses them: the halves are under 65536 *)
prfn word_bounded {cells:$A.cells}{at,high,low:nat} (word: $SHA.WORD_AT(cells, at, high, low)): [high < 65536; low < 65536] void =
  $SHA.word_at_bound(word)

prfn five_bounded {cells:$A.cells}{at,h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat}
  (have: $SHA.FIVE_AT(cells, at, $SHA.five($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low))))
  : [h4_low < 65536] void =
  $SHA.five_at_bound(have)

implement main0 () = ()
