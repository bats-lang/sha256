#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* every constant of SHA-1 as the square-root definition gives it: all 4 constructors are accepted (sha256#31) *)
prfn claim_0_to_19 (): $SHA.SHA1_K(0, 0x5a82, 0x7999) = $SHA.SHA1_K_0_to_19()
prfn claim_20_to_39 (): $SHA.SHA1_K(20, 0x6ed9, 0xeba1) = $SHA.SHA1_K_20_to_39()
prfn claim_40_to_59 (): $SHA.SHA1_K(40, 0x8f1b, 0xbcdc) = $SHA.SHA1_K_40_to_59()
prfn claim_60_to_79 (): $SHA.SHA1_K(60, 0xca62, 0xc1d6) = $SHA.SHA1_K_60_to_79()

implement main0 () = ()
