#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 5 = 1 * 5 is no factorisation: a factor is at least 2 (sha256#78, keyword: nth-prime) *)
prfn claim (): $SHA.COMPOSITE(5) = $SHA.COMPOSITE_mk{1, 5}()

implement main0 () = ()
