#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the high limb adds the carry from the middle one: 8 * 0 + 7 is 7 *)
fn claim (): void = let
  val (high | @(byte2, byte3)) = $SHA.bitlen_high(0, 7)
  prval $SHA.BITLEN_HIGH_mk() = high
  val zero: int(0) = byte3
in end

implement main0 () = ()
