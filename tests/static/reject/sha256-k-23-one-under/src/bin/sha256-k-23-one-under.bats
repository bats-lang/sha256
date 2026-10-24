#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_23 one under: p * 2^96 < (x + 1)^3 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(23, 0x76f9, 0x88d9) = $SHA.SHA256_K_23()

implement main0 () = ()
