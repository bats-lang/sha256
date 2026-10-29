#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 9 = 3 * 2 + 3: a remainder of 3 is no remainder of a division by 3 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.PRIME(9) =
  $SHA.PRIME_mk{3}($SHA.NO_DIVISOR_step{4, 1}($SHA.NO_DIVISOR_step{2, 3}($SHA.NO_DIVISOR_none())))

implement main0 () = ()
