#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_32 one under: p * 2^96 < (x + 1)^3 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(32, 0x27b7, 0x0a84) = $SHA.SHA256_K_32()

implement main0 () = ()
