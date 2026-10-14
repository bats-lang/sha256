#include "share/atspre_staload.hats"
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

fn word (high: int, low: int): void = (hex4(high); hex4(low); print_char(' '))

implement main0 () = let
  val (_ | @(h0h, h0l, h1h, h1l, h2h, h2l, h3h, h3l, h4h, h4l, h5h, h5l, h6h, h6l, h7h, h7l)) = $SHA.sha256_iv()
  val () = print("sha256 ")
  val () = (word(h0h, h0l); word(h1h, h1l); word(h2h, h2l); word(h3h, h3l); word(h4h, h4l); word(h5h, h5l); word(h6h, h6l); word(h7h, h7l))
  val () = print_newline()
  val (_ | @(g0h, g0l, g1h, g1l, g2h, g2l, g3h, g3l, g4h, g4l)) = $SHA.sha1_iv()
  val () = print("sha1 ")
  val () = (word(g0h, g0l); word(g1h, g1l); word(g2h, g2l); word(g3h, g3l); word(g4h, g4l))
  val () = print_newline()
in end
