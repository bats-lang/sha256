#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 9 = 3 * 3 + 0 has remainder 0: the divisor 3 is not a witness of no divisor (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.PRIME(9) =
  $SHA.PRIME_mk{3}($SHA.NO_DIVISOR_step{4, 1}($SHA.NO_DIVISOR_step{3, 0}($SHA.NO_DIVISOR_none())))

implement main0 () = ()
