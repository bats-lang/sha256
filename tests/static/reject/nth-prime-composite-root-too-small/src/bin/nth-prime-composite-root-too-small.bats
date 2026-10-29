#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 49 given the root 6 to leave out its divisor 7: 49 < 7 * 7 does not hold of r = 6 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.PRIME(49) =
  $SHA.PRIME_mk{6}($SHA.NO_DIVISOR_step{24, 1}($SHA.NO_DIVISOR_step{16, 1}($SHA.NO_DIVISOR_step{12, 1}($SHA.NO_DIVISOR_step{9, 4}($SHA.NO_DIVISOR_step{8, 1}($SHA.NO_DIVISOR_none()))))))

implement main0 () = ()
