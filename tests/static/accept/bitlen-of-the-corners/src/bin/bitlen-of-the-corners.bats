#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* 64 bytes are 512 bits: 0x0200. 65535 bytes (q = 1023, b = 63) are 524280
   bits, 0x07fff8: the carry from the low limb is in the middle one. The
   props are opened and the solver derives the bytes. *)
fn sixty_four (): void = let
  val (low | @(carry_low, byte6, byte7)) = $SHA.bitlen_low(1, 0)
  prval $SHA.BITLEN_LOW_mk() = low
  val two: int(2) = byte6
  val zero: int(0) = byte7
in end

fn largest_low (): void = let
  val (low | @(carry_low, byte6, byte7)) = $SHA.bitlen_low(1023, 63)
  prval $SHA.BITLEN_LOW_mk() = low
  val seven: int(7) = carry_low
  val ff: int(255) = byte6
  val f8: int(248) = byte7
in end

fn middle_carry (): void = let
  val (mid | @(carry_mid, byte4, byte5)) = $SHA.bitlen_mid(65535, 7)
  prval $SHA.BITLEN_MID_mk() = mid
  val seven: int(7) = carry_mid
  val ff: int(255) = byte4
  val ff2: int(255) = byte5
in end

fn high_limb (): void = let
  val (high | @(byte2, byte3)) = $SHA.bitlen_high(8191, 7)
  prval $SHA.BITLEN_HIGH_mk() = high
  val ff: int(255) = byte2
  val ff2: int(255) = byte3
in end

implement main0 () = ()
