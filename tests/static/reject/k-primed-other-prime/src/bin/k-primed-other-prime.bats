#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

prfn second (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

(* the word of the cube root of 2 (K_0) given as the word of the second prime, 3 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.SHA256_K_PRIMED(1, 3, 0x428a, 0x2f98) =
  $SHA.SHA256_K_PRIMED_1(second())

implement main0 () = ()
