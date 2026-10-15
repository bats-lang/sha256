#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* The chaining value's word 0 is H0 plus the final a: the sum for word 1 is not
   word 0's *)
prfn claim {msg:$A.cells}{at:nat}{h0_high,h0_low,h1_high,h1_low,h2_high,h2_low,h3_high,h3_low,h4_high,h4_low,h5_high,h5_low,h6_high,h6_low,h7_high,h7_low,end_a_high,end_a_low,end_b_high,end_b_low,end_c_high,end_c_low,end_d_high,end_d_low,end_e_high,end_e_low,end_f_high,end_f_low,end_g_high,end_g_low,end_h_high,end_h_low,next_h0_high,next_h0_low,next_h1_high,next_h1_low,next_h2_high,next_h2_low,next_h3_high,next_h3_low,next_h4_high,next_h4_low,next_h5_high,next_h5_low,next_h6_high,next_h6_low,next_h7_high,next_h7_low:nat}
  (rounds: $SHA.SHA256_ROUNDS(msg, at, 64, $SHA.eight($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low), $SHA.w32(h5_high, h5_low), $SHA.w32(h6_high, h6_low), $SHA.w32(h7_high, h7_low)), $SHA.eight($SHA.w32(end_a_high, end_a_low), $SHA.w32(end_b_high, end_b_low), $SHA.w32(end_c_high, end_c_low), $SHA.w32(end_d_high, end_d_low), $SHA.w32(end_e_high, end_e_low), $SHA.w32(end_f_high, end_f_low), $SHA.w32(end_g_high, end_g_low), $SHA.w32(end_h_high, end_h_low))),
   add0: $AR.ADD32(h0_high, h0_low, end_a_high, end_a_low, next_h0_high, next_h0_low),
   add1: $AR.ADD32(h1_high, h1_low, end_b_high, end_b_low, next_h1_high, next_h1_low),
   add2: $AR.ADD32(h2_high, h2_low, end_c_high, end_c_low, next_h2_high, next_h2_low),
   add3: $AR.ADD32(h3_high, h3_low, end_d_high, end_d_low, next_h3_high, next_h3_low),
   add4: $AR.ADD32(h4_high, h4_low, end_e_high, end_e_low, next_h4_high, next_h4_low),
   add5: $AR.ADD32(h5_high, h5_low, end_f_high, end_f_low, next_h5_high, next_h5_low),
   add6: $AR.ADD32(h6_high, h6_low, end_g_high, end_g_low, next_h6_high, next_h6_low),
   add7: $AR.ADD32(h7_high, h7_low, end_h_high, end_h_low, next_h7_high, next_h7_low))
  : $SHA.SHA256_BLOCK(msg, at, $SHA.eight($SHA.w32(h0_high, h0_low), $SHA.w32(h1_high, h1_low), $SHA.w32(h2_high, h2_low), $SHA.w32(h3_high, h3_low), $SHA.w32(h4_high, h4_low), $SHA.w32(h5_high, h5_low), $SHA.w32(h6_high, h6_low), $SHA.w32(h7_high, h7_low)), $SHA.eight($SHA.w32(next_h0_high, next_h0_low), $SHA.w32(next_h1_high, next_h1_low), $SHA.w32(next_h2_high, next_h2_low), $SHA.w32(next_h3_high, next_h3_low), $SHA.w32(next_h4_high, next_h4_low), $SHA.w32(next_h5_high, next_h5_low), $SHA.w32(next_h6_high, next_h6_low), $SHA.w32(next_h7_high, next_h7_low))) =
  $SHA.SHA256_BLOCK_mk(rounds, add1, add0, add2, add3, add4, add5, add6, add7)

implement main0 () = ()
