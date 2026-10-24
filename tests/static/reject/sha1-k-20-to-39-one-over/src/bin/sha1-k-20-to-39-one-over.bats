#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_20 one over: x^2 <= n * 2^60 fails, with x = floor(sqrt(n) * 2^30) (sha256#31) *)
prfn claim (): $SHA.SHA1_K(20, 0x6ed9, 0xeba2) = $SHA.SHA1_K_20_to_39()

implement main0 () = ()
