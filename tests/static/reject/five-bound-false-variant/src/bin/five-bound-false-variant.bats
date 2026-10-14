#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* each half of the five words is under 65536 *)
prfn claim {cells:$A.cells}{at,h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low:nat}
  (have: $SHA.FIVE_AT(cells, at, $SHA.five($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low))))
  : [h0_high < 65535] void =
  $SHA.five_at_bound(have)

implement main0 () = ()
