#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_53 one over: x^3 <= p * 2^96 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(53, 0x4ed8, 0xaa4b) = $SHA.SHA256_K_53()

implement main0 () = ()
