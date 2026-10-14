#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the middle limb adds the carry from the low one: 8 * 0 + 7 is 7, not 0 *)
fn claim (): void = let
  val (mid | @(carry_mid, byte4, byte5)) = $SHA.bitlen_mid(0, 7)
  prval $SHA.BITLEN_MID_mk() = mid
  val zero: int(0) = byte5
in end

implement main0 () = ()
