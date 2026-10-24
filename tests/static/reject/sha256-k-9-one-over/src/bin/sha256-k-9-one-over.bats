#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_9 one over: x^3 <= p * 2^96 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(9, 0x1283, 0x5b02) = $SHA.SHA256_K_9()

implement main0 () = ()
