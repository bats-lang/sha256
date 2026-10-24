#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_60 one under: n * 2^60 < (x + 1)^2 fails, with x = floor(sqrt(n) * 2^30) (sha256#31) *)
prfn claim (): $SHA.SHA1_K(60, 0xca62, 0xc1d5) = $SHA.SHA1_K_60_to_79()

implement main0 () = ()
