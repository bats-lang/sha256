#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_30 one over: x^3 <= p * 2^96 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(30, 0x06ca, 0x6352) = $SHA.SHA256_K_30()

implement main0 () = ()
