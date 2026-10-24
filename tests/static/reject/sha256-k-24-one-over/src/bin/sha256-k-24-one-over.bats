#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_24 one over: x^3 <= p * 2^96 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(24, 0x983e, 0x5153) = $SHA.SHA256_K_24()

implement main0 () = ()
