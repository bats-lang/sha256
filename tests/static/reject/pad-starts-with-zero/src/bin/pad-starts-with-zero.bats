#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the padding starts with the byte 128 (the bit 1), not a zero byte *)
prfn claim {message,marked,zeroed,padded:$A.cells}{count_top,count_high,count_blocks,fill,zeros:nat}{byte0,byte1,byte2,byte3,byte4,byte5,byte6,byte7:int}
  (counted: $SHA.COUNTED(message, count_top, count_high, count_blocks, fill), zcount: $SHA.ZCOUNT(fill, zeros),
   bitlen: $SHA.BITLEN(count_top, count_high, count_blocks, fill, byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7),
   marking: $SHA.SNOC(message, 0, marked), zeroing: $SHA.ZSNOC(marked, zeros, zeroed),
   written: $SHA.LENSNOC(zeroed, byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7, padded))
  : $SHA.PAD(message, count_top, count_high, count_blocks, fill, padded) =
  $SHA.PAD_mk(counted, zcount, bitlen, marking, zeroing, written)

implement main0 () = ()
