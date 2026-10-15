#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a block is hashed only when it is full: b = 64, not 63 *)
prfn claim (): $SHA.NORM(0, 0, 0, 63, 0, 0, 1, 0) = $SHA.NORM_block()

implement main0 () = ()
