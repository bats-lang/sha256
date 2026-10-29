#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

prfn second (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

(* 7 after 3 skips 5, whose "factorisation" 2 * 2 is 4 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.NTH_PRIME(2, 7) =
  $SHA.NTH_PRIME_next(second(),
    $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 2}(), $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 2}(), $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 3}(), $SHA.NONPRIMES_none()))),
    $SHA.PRIME_mk{2}($SHA.NO_DIVISOR_step{3, 1}($SHA.NO_DIVISOR_none())))

implement main0 () = ()
