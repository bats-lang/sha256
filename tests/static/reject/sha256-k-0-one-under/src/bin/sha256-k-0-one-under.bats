#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_0 one under: p * 2^96 < (x + 1)^3 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(0, 0x428a, 0x2f97) = $SHA.SHA256_K_0()

implement main0 () = ()
