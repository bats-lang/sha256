#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_56 one under: p * 2^96 < (x + 1)^3 fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)
prfn claim (): $SHA.SHA256_K(56, 0x748f, 0x82ed) = $SHA.SHA256_K_56()

implement main0 () = ()
