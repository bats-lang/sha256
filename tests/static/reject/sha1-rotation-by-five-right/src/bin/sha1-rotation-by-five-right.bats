#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* ROTL 5 of a is ROTR 27 of a: ROTR 5 is another word *)
prfn claim {t:nat}{a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,k_high,k_low,w_high,w_low,sum1_high,sum1_low,sum2_high,sum2_low,sum3_high,sum3_low,turn5_high,turn5_low,f_high,f_low,new_a_high,new_a_low,new_c_high,new_c_low:nat}
  (wrong: $AR.ROTR(5, a_high, a_low, turn5_high, turn5_low),
   function: $SHA.SHA1_F(t, b_high, b_low, c_high, c_low, d_high, d_low, f_high, f_low),
   add1: $AR.ADD32(turn5_high, turn5_low, f_high, f_low, sum1_high, sum1_low),
   add2: $AR.ADD32(sum1_high, sum1_low, e_high, e_low, sum2_high, sum2_low),
   add3: $AR.ADD32(sum2_high, sum2_low, k_high, k_low, sum3_high, sum3_low),
   add4: $AR.ADD32(sum3_high, sum3_low, w_high, w_low, new_a_high, new_a_low),
   turn30: $AR.ROTR(2, b_high, b_low, new_c_high, new_c_low))
  : $SHA.SHA1_ROUND(t, $SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(k_high, k_low), $SHA.w32(w_high, w_low), $SHA.w32(new_a_high, new_a_low), $SHA.w32(new_c_high, new_c_low)) =
  $SHA.SHA1_ROUND_mk(wrong, function, add1, add2, add3, add4, turn30)

implement main0 () = ()
