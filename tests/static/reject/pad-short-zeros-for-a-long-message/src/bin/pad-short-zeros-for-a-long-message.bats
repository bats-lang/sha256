#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 56 bytes in the block leave no room for the length: the zeros of the
   short padding are for 55 or fewer *)
prfn claim (): $SHA.ZCOUNT(56, 0) = $SHA.ZCOUNT_short()

implement main0 () = ()
