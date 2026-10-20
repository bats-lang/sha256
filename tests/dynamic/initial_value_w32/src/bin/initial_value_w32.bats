#include "share/atspre_staload.hats"
#use arith as AR
#use sha256 as SHA

(* Prints the initial hash values the digests start from (sha256_iv,
   sha1_iv): the harness compares with `expected`, which make-expected.py
   computes from the definition of SHA-256's (the first 32 bits of the
   fractional parts of the square roots of the first eight primes, by
   integer square roots) and from FIPS 180-4 5.3.1 for SHA-1's. *)

fn hex4 (value: int): void = let
  val d0 = value / 4096
  val r0 = value - 4096 * d0
  val d1 = r0 / 256
  val r1 = r0 - 256 * d1
  val d2 = r1 / 16
  val d3 = r1 - 16 * d2
  fn digit (d: int): void = print_char(int2char0(if d < 10 then 48 + d else 87 + d))
in digit(d0); digit(d1); digit(d2); digit(d3) end

fn hex2 (value: int): void = let
  val d0 = value / 16
  val d1 = value - 16 * d0
  fn digit (d: int): void = print_char(int2char0(if d < 10 then 48 + d else 87 + d))
in digit(d0); digit(d1) end

fn word {h,l:nat | h < 65536; l < 65536} (w: $AR.word32(h, l)): void = let
  val (_ | b0) = $AR.word32_byte(w, 0)
  val (_ | b1) = $AR.word32_byte(w, 1)
  val (_ | b2) = $AR.word32_byte(w, 2)
  val (_ | b3) = $AR.word32_byte(w, 3)
in hex2(b0); hex2(b1); hex2(b2); hex2(b3); print_char(' ') end

implement main0 () = let
  val (_ | @(h0, h1, h2, h3, h4, h5, h6, h7)) = $SHA.sha256_iv_w32()
  val () = print("sha256 ")
  val () = (word(h0); word(h1); word(h2); word(h3); word(h4); word(h5); word(h6); word(h7))
  val () = print_newline()
  val (_ | @(g0, g1, g2, g3, g4)) = $SHA.sha1_iv_w32()
  val () = print("sha1 ")
  val () = (word(g0); word(g1); word(g2); word(g3); word(g4))
  val () = print_newline()
in end
