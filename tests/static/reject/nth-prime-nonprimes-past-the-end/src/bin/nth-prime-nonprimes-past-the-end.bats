#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* nothing lies between 3 and 4, so no composite is next (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.NONPRIMES(3, 4) = $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 2}(), $SHA.NONPRIMES_none())

implement main0 () = ()
