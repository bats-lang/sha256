#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 60 bytes in the block: 59 zeros (60 + 1 + 59 + 8 = 128), not 60 *)
prfn claim (): $SHA.ZCOUNT(60, 60) = $SHA.ZCOUNT_long()

implement main0 () = ()
