#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_19 one over: x^3 <= p * 2^96 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(19, 0x240c, 0xa1cd) = $SHA.SHA256_K_19()

implement main0 () = ()
