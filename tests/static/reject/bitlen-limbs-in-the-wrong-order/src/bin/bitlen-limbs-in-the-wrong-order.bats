#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the length's limbs are low, middle, high: BITLEN takes them so *)
prfn claim {count_top,count_high,count_blocks,fill,carry_low,carry_mid,byte2,byte3,byte4,byte5,byte6,byte7:nat}
  (low: $SHA.BITLEN_LOW(count_blocks, fill, carry_low, byte6, byte7), mid: $SHA.BITLEN_MID(count_high, carry_low, carry_mid, byte4, byte5),
   high: $SHA.BITLEN_HIGH(count_top, carry_mid, byte2, byte3)): $SHA.BITLEN(count_top, count_high, count_blocks, fill, 0, 0, byte2, byte3, byte4, byte5, byte6, byte7) =
  $SHA.BITLEN_mk(mid, low, high)

implement main0 () = ()
