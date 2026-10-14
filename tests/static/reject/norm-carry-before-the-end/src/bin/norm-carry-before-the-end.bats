#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the carry into nh is at q = 1023 only *)
prfn claim (): $SHA.NORM(0, 0, 5, 64, 0, 1, 0, 0) = $SHA.NORM_carry()

implement main0 () = ()
