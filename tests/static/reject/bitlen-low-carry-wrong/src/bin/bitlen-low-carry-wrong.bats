#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 65535 bytes are 524280 bits: the low limb 0xfff8 carries 7, not 6 *)
fn claim (): void = let
  val (low | @(carry_low, byte6, byte7)) = $SHA.bitlen_low(1023, 63)
  prval $SHA.BITLEN_LOW_mk() = low
  val six: int(6) = carry_low
in end

implement main0 () = ()
