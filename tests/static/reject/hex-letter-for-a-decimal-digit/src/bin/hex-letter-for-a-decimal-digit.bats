#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the letters are for the digits 10 to 15 *)
prfn claim (): $SHA.HEX_DIGIT(5, 92) = $SHA.HEX_DIGIT_letter()

implement main0 () = ()
