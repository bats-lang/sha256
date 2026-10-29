#include "share/atspre_staload.hats"
#use arith as AR
#use sha256 as SHA

(* Prints the 64 round constants and H(0) from the lookups that carry the proof that their
   primes are the first 64 and the first eight (sha256_k_nth_w32, sha256_iv_nth_w32), and
   says `same` where the published lookup (sha256_k_w32, sha256_iv_w32) gives the same word.
   The harness compares with `expected`, which make-expected.py computes from the
   definition (sha256#78, keyword: nth-prime). *)

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
in hex2(b0); hex2(b1); hex2(b2); hex2(b3) end

fn same_word {h,l,h2,l2:nat | h < 65536; l < 65536; h2 < 65536; l2 < 65536} (a: $AR.word32(h, l), b: $AR.word32(h2, l2)): bool = let
  val (_ | a0) = $AR.word32_byte(a, 0)
  val (_ | a1) = $AR.word32_byte(a, 1)
  val (_ | a2) = $AR.word32_byte(a, 2)
  val (_ | a3) = $AR.word32_byte(a, 3)
  val (_ | b0) = $AR.word32_byte(b, 0)
  val (_ | b1) = $AR.word32_byte(b, 1)
  val (_ | b2) = $AR.word32_byte(b, 2)
  val (_ | b3) = $AR.word32_byte(b, 3)
in a0 = b0 && a1 = b1 && a2 = b2 && a3 = b3 end

fn verdict (same: bool): void = if same then println!("same") else println!("DIFFERENT")

fun constants {t:nat | t <= 64} .<64 - t>. (t: int t): void =
  if t < 64 then let
    val (_, _ | new_word) = $SHA.sha256_k_nth_w32(t)
    val (_ | old_word) = $SHA.sha256_k_w32(t)
    val () = (print("k "); print(t); print_char(' '); word(new_word); print_char(' '))
    val () = verdict(same_word(new_word, old_word))
  in constants(t + 1) end
  else ()

implement main0 () = let
  val () = constants(0)
  val (_, _ | @(n0, n1, n2, n3, n4, n5, n6, n7)) = $SHA.sha256_iv_nth_w32()
  val (_ | @(o0, o1, o2, o3, o4, o5, o6, o7)) = $SHA.sha256_iv_w32()
  val () = print("iv ")
  val () = (word(n0); print_char(' '); word(n1); print_char(' '); word(n2); print_char(' '); word(n3); print_char(' '))
  val () = (word(n4); print_char(' '); word(n5); print_char(' '); word(n6); print_char(' '); word(n7); print_char(' '))
  val all_same = same_word(n0, o0) && same_word(n1, o1) && same_word(n2, o2) && same_word(n3, o3)
                 && same_word(n4, o4) && same_word(n5, o5) && same_word(n6, o6) && same_word(n7, o7)
in verdict(all_same) end
