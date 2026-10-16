#include "share/atspre_staload.hats"
#use sha256 as SHA

(* The eight bytes of the length in bits (padding's last eight bytes) for
   counts n = 2^32 * n2 + 2^16 * nh + 64 * q + b, printed in hex for the
   corners of every digit: the harness compares with `expected`, which
   make-expected.py writes from Python's integers (8 * n, big endian). *)

fn hex2 (value: int): void = let
  val high_nibble = value / 16
  val low_nibble = value - 16 * high_nibble
in
  print_char(int2char0(if high_nibble < 10 then 48 + high_nibble else 87 + high_nibble));
  print_char(int2char0(if low_nibble < 10 then 48 + low_nibble else 87 + low_nibble))
end

fn show {count_top,count_high,count_blocks,fill:nat | count_top < 8192; count_high < 65536; count_blocks < 1024; fill < 64}
  (count_top: int count_top, count_high: int count_high, count_blocks: int count_blocks, fill: int fill): void = let
  val (_ | @(byte2, byte3, byte4, byte5, byte6, byte7)) = $SHA.bitlen_bytes(count_top, count_high, count_blocks, fill)
in
  print!(count_top, " ", count_high, " ", count_blocks, " ", fill, " 0000");
  hex2(byte2); hex2(byte3); hex2(byte4); hex2(byte5); hex2(byte6); hex2(byte7);
  print_newline()
end

implement main0 () = let
  val () = show(0, 0, 0, 0)
  val () = show(0, 0, 0, 1)
  val () = show(0, 0, 0, 55)
  val () = show(0, 0, 0, 63)
  val () = show(0, 0, 1, 0)
  val () = show(0, 0, 1, 7)
  val () = show(0, 0, 127, 63)
  val () = show(0, 0, 128, 0)
  val () = show(0, 0, 1022, 63)
  val () = show(0, 0, 1023, 0)
  val () = show(0, 0, 1023, 63)
  val () = show(0, 1, 0, 0)
  val () = show(0, 1, 1023, 63)
  val () = show(0, 8191, 1023, 63)
  val () = show(0, 8192, 0, 0)
  val () = show(0, 65535, 0, 0)
  val () = show(0, 65535, 1023, 63)
  val () = show(1, 0, 0, 0)
  val () = show(1, 65535, 1023, 63)
  val () = show(4095, 0, 0, 0)
  val () = show(8191, 0, 0, 0)
  val () = show(8191, 65535, 1023, 63)
  val () = show(8190, 40000, 777, 33)
in end
