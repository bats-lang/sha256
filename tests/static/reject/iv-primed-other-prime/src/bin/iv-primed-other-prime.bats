#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

prfn second (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

(* every word of H(0) given the second prime, 3, as its prime (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.SHA256_IV_PRIMED($SHA.eight($SHA.w32(0x6a09, 0xe667), $SHA.w32(0xbb67, 0xae85), $SHA.w32(0x3c6e, 0xf372), $SHA.w32(0xa54f, 0xf53a),
    $SHA.w32(0x510e, 0x527f), $SHA.w32(0x9b05, 0x688c), $SHA.w32(0x1f83, 0xd9ab), $SHA.w32(0x5be0, 0xcd19))) =
  $SHA.SHA256_IV_PRIMED_mk(second(), second(), second(), second(), second(), second(), second(), second())

implement main0 () = ()
