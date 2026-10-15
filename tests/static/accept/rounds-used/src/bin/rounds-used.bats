#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* A round of SHA-256 from the table's constant and the schedule's word, the
   round's proof taken into the rounds, and the block's proofs of both
   hashes used: what the proofs of a block say, in the standard's terms. *)
prfn step_taken
  {msg:$A.cells}{at,t:nat | t < 64}{init:$SHA.eight_words}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low,k_high,k_low,w_high,w_low,new_a_high,new_a_low,new_e_high,new_e_low:nat}
  (done: $SHA.SHA256_ROUNDS(msg, at, t, init, $SHA.eight($SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low), $SHA.w32(h_high, h_low))),
   constant: $SHA.SHA256_K(t, k_high, k_low),
   word: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t, w_high, w_low),
   step: $SHA.SHA256_ROUND($SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low), $SHA.w32(h_high, h_low), $SHA.w32(k_high, k_low), $SHA.w32(w_high, w_low), $SHA.w32(new_a_high, new_a_low), $SHA.w32(new_e_high, new_e_low)))
  : $SHA.SHA256_ROUNDS(msg, at, t+1, init, $SHA.eight($SHA.w32(new_a_high, new_a_low), $SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(new_e_high, new_e_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low))) =
  $SHA.SHA256_ROUNDS_next(done, constant, word, step)

fn hash_block {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}
  {lw:agz}{words:$A.cells}{lc:agz}{chain:$A.cells}
  {h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low:nat | h0_high < 65536; h0_low < 65536; h1_high < 65536; h1_low < 65536; h2_high < 65536; h2_low < 65536; h3_high < 65536; h3_low < 65536; h4_high < 65536; h4_low < 65536; h5_high < 65536; h5_low < 65536; h6_high < 65536; h6_low < 65536; h7_high < 65536; h7_low < 65536}
  (message: !$A.barr(lm, nm, msg), at: int at, schedule: $A.barr(lw, 256, words),
   chaining: $A.barr(lc, 32, chain),
   have: $SHA.EIGHT_AT(chain, 0, $SHA.eight($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low), $SHA.w32(h5_high, h5_low), $SHA.w32(h6_high, h6_low), $SHA.w32(h7_high, h7_low)))): void = let
  val (_, _ | @(schedule, chaining)) = $SHA.sha256_compress(message, at, schedule, chaining, have)
  val () = $A.barr_free(schedule)
  val () = $A.barr_free(chaining)
in end

implement main0 () = ()
