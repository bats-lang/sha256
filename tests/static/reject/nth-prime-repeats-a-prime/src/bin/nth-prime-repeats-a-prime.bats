#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

prfn second (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

(* the prime after 3 is 3: p < q does not hold (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.NTH_PRIME(2, 3) =
  $SHA.NTH_PRIME_next(second(),
    $SHA.NONPRIMES_none(),
    $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

implement main0 () = ()
