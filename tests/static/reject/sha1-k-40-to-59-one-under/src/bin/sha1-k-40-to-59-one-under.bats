#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_40 one under: n * 2^60 < (x + 1)^2 fails, with x = floor(sqrt(n) * 2^30) (sha256#31) *)
prfn claim (): $SHA.SHA1_K(40, 0x8f1b, 0xbcdb) = $SHA.SHA1_K_40_to_59()

implement main0 () = ()
