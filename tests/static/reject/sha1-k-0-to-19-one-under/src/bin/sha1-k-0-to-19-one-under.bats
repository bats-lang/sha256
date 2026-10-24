#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_0 one under: n * 2^60 < (x + 1)^2 fails, with x = floor(sqrt(n) * 2^30) (sha256#31) *)
prfn claim (): $SHA.SHA1_K(0, 0x5a82, 0x7998) = $SHA.SHA1_K_0_to_19()

implement main0 () = ()
