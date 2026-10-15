#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the digit 5 is the character 53 ('5'), not 54 *)
prfn claim (): $SHA.HEX_DIGIT(5, 54) = $SHA.HEX_DIGIT_decimal()

implement main0 () = ()
