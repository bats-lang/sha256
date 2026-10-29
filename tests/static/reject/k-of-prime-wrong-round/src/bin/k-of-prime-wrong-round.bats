#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

prfn second (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

(* the second prime, 3, claimed as the first (K_0 of round 0): the proof is NTH_PRIME(1, 3) (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.SHA256_K_OF_PRIME(0, 3, 0x7137, 0x4491) =
  $SHA.SHA256_K_OF_PRIME_mk{1}{0, 3, 0x7137, 0x4491}(second())

implement main0 () = ()
