#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the digit 10 is 'a' (97), not the character 58 *)
prfn claim (): $SHA.HEX_DIGIT(10, 58) = $SHA.HEX_DIGIT_decimal()

implement main0 () = ()
