#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 1 has no divisor from 2 to its root 1, but a prime is at least 2 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.PRIME(1) = $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())

implement main0 () = ()
