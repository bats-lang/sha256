#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the top digit n2 is under 8192: 8191 carries nowhere *)
prfn claim (): $SHA.NORM(8191, 65535, 1023, 64, 8192, 0, 0, 0) = $SHA.NORM_carry2()

implement main0 () = ()
