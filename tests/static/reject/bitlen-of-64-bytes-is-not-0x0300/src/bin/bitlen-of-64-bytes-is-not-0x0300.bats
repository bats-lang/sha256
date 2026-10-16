#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 64 bytes are 512 bits, 0x0200: the high byte of the low limb is 2 *)
fn claim (): void = let
  val (low | @(carry_low, byte6, byte7)) = $SHA.bitlen_low(1, 0)
  prval $SHA.BITLEN_LOW_mk() = low
  val three: int(3) = byte6
in end

implement main0 () = ()
