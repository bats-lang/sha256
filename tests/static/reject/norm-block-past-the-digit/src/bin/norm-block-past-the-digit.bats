#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* q = 1023 is the end of the digit: the next block carries into nh *)
prfn claim (): $SHA.NORM(0, 0, 1023, 64, 0, 0, 1024, 0) = $SHA.NORM_block()

implement main0 () = ()
