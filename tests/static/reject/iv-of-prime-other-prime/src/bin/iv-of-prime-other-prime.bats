#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

prfn second (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

(* the square-root word of 2 (H(0)_0) given as the word of the second prime, 3 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.SHA256_IV_OF_PRIME(1, 3, 0x6a09, 0xe667) =
  $SHA.SHA256_IV_OF_PRIME_mk{1}{1, 3, 0x6a09, 0xe667}(second())

implement main0 () = ()
