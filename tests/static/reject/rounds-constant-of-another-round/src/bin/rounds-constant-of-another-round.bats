#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* round t takes the table's constant for round t: the one for round 1 is another word *)
prfn claim
  {msg:$A.cells}{at,t:nat | t < 64}{init:$SHA.eight_words}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low,k_high,k_low,w_high,w_low,new_a_high,new_a_low,new_e_high,new_e_low:nat}
  (done: $SHA.SHA256_ROUNDS(msg, at, t, init, $SHA.eight($SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low), $SHA.w32(h_high, h_low))),
   constant: $SHA.SHA256_K(1, k_high, k_low),
   word: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t, w_high, w_low),
   step: $SHA.SHA256_ROUND($SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low), $SHA.w32(h_high, h_low), $SHA.w32(k_high, k_low), $SHA.w32(w_high, w_low), $SHA.w32(new_a_high, new_a_low), $SHA.w32(new_e_high, new_e_low)))
  : $SHA.SHA256_ROUNDS(msg, at, t+1, init, $SHA.eight($SHA.w32(new_a_high, new_a_low), $SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(new_e_high, new_e_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low))) =
  $SHA.SHA256_ROUNDS_next(done, constant, word, step)

implement main0 () = ()
