#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 15 is not 3 * 4 + 2, the witness of the divisor 3 is not a division of 15 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.PRIME(15) =
  $SHA.PRIME_mk{3}($SHA.NO_DIVISOR_step{7, 1}($SHA.NO_DIVISOR_step{4, 2}($SHA.NO_DIVISOR_none())))

implement main0 () = ()
