#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* K_t is 5a827999 for t from 0 to 19: round 20 has another constant *)
prfn claim (): $SHA.SHA1_K(20, 0x5a82, 0x7999) = $SHA.SHA1_K_0_to_19()

implement main0 () = ()
