#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the bytes bitlen_bytes gives are x2 ... x7, most significant first: the
   last two are not swapped *)
fn claim {count_top,count_high,count_blocks,fill:nat | count_top < 8192; count_high < 65536; count_blocks < 1024; fill < 64} (count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill)
  : [byte2,byte3,byte4,byte5,byte6,byte7:nat]
    ($SHA.BITLEN(count_top, count_high, count_blocks, fill, 0, 0, byte2, byte3, byte4, byte5, byte7, byte6) | @(int byte2, int byte3, int byte4, int byte5, int byte6, int byte7)) =
  $SHA.bitlen_bytes(count_top, count_high, count_blocks, fill)

implement main0 () = ()
