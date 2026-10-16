#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 10 bytes in the block: 45 zeros (10 + 1 + 45 + 8 = 64), not 44 *)
prfn claim (): $SHA.ZCOUNT(10, 44) = $SHA.ZCOUNT_short()

implement main0 () = ()
