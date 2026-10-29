#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the first prime is 2, the one constructor of NTH_PRIME_first gives NTH_PRIME(0, 2) (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.NTH_PRIME(0, 3) = $SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))

implement main0 () = ()
