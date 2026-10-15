#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* SHA-1 rounds take SHA-1's schedule: a word of SHA-256's schedule is another word *)
prfn claim {msg:$A.cells}{at,t:nat | t < 80}{init:$SHA.five_words}
  {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,k_high,k_low,w_high,w_low,new_a_high,new_a_low,new_c_high,new_c_low:nat}
  (done: $SHA.SHA1_ROUNDS(msg, at, t, init, $SHA.five($SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low))),
   constant: $SHA.SHA1_K(t, k_high, k_low),
   word: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t, w_high, w_low),
   step: $SHA.SHA1_ROUND(t, $SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(k_high, k_low), $SHA.w32(w_high, w_low), $SHA.w32(new_a_high, new_a_low), $SHA.w32(new_c_high, new_c_low)))
  : $SHA.SHA1_ROUNDS(msg, at, t+1, init, $SHA.five($SHA.w32(new_a_high, new_a_low), $SHA.w32(a_high, a_low), $SHA.w32(new_c_high, new_c_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low))) =
  $SHA.SHA1_ROUNDS_next(done, constant, word, step)

implement main0 () = ()
