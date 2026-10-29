#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the relations of NTH_PRIME as a caller writes them (sha256#78, keyword: nth-prime) *)
prfn prime_two (): $SHA.PRIME(2) = $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())
prfn prime_seven (): $SHA.PRIME(7) = $SHA.PRIME_mk{2}($SHA.NO_DIVISOR_step{3, 1}($SHA.NO_DIVISOR_none()))
prfn composite_ninety_one (): $SHA.COMPOSITE(91) = $SHA.COMPOSITE_mk{7, 13}()
prfn between_seven_and_eleven (): $SHA.NONPRIMES(7, 11) =
  $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 4}(), $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{3, 3}(), $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 5}(), $SHA.NONPRIMES_none())))
prfn second_prime (): $SHA.NTH_PRIME(1, 3) =
  $SHA.NTH_PRIME_next($SHA.NTH_PRIME_first($SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none())), $SHA.NONPRIMES_none(), $SHA.PRIME_mk{1}($SHA.NO_DIVISOR_none()))
prfn third_prime (): $SHA.NTH_PRIME(2, 5) =
  $SHA.NTH_PRIME_next(second_prime(), $SHA.NONPRIMES_next($SHA.COMPOSITE_mk{2, 2}(), $SHA.NONPRIMES_none()), $SHA.PRIME_mk{2}($SHA.NO_DIVISOR_step{2, 1}($SHA.NO_DIVISOR_none())))

(* the lookups that carry the proof, as a caller reads them *)
fn k_of_round_five (): void = let
  val (k, from_prime | word) = $SHA.sha256_k_nth_w32(5)
  prval _ = k
  prval _ = from_prime
  val _ = word
in end

fn initial_value (): void = let
  val (iv, p0, p1, p2, p3, p4, p5, p6, p7 | words) = $SHA.sha256_iv_nth_w32()
  prval _ = (iv, p0, p1, p2, p3, p4, p5, p6, p7)
  val _ = words
in end

implement main0 () = ()
