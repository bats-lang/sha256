#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* T1 takes BIG_SIGMA_1 of e: BIG_SIGMA_0 of e is another word *)
prfn claim {a_high,a_low,b_high,b_low,c_high,c_low,d_high,d_low,e_high,e_low,f_high,f_low,g_high,g_low,h_high,h_low,k_high,k_low,w_high,w_low,big1_high,big1_low,ch_high,ch_low,sum1_high,sum1_low,sum2_high,sum2_low,sum3_high,sum3_low,t1_high,t1_low,big0_high,big0_low,maj_high,maj_low,t2_high,t2_low,new_a_high,new_a_low,new_e_high,new_e_low:nat}
  (wrong: $SHA.BIG_SIGMA_0(e_high, e_low, big1_high, big1_low),
   choice: $SHA.CH(e_high, e_low, f_high, f_low, g_high, g_low, ch_high, ch_low),
   add1: $AR.ADD32(h_high, h_low, big1_high, big1_low, sum1_high, sum1_low),
   add2: $AR.ADD32(sum1_high, sum1_low, ch_high, ch_low, sum2_high, sum2_low),
   add3: $AR.ADD32(sum2_high, sum2_low, k_high, k_low, sum3_high, sum3_low),
   add4: $AR.ADD32(sum3_high, sum3_low, w_high, w_low, t1_high, t1_low),
   big0: $SHA.BIG_SIGMA_0(a_high, a_low, big0_high, big0_low),
   majority: $SHA.MAJ(a_high, a_low, b_high, b_low, c_high, c_low, maj_high, maj_low),
   add5: $AR.ADD32(big0_high, big0_low, maj_high, maj_low, t2_high, t2_low),
   add6: $AR.ADD32(t1_high, t1_low, t2_high, t2_low, new_a_high, new_a_low),
   add7: $AR.ADD32(d_high, d_low, t1_high, t1_low, new_e_high, new_e_low))
  : $SHA.SHA256_ROUND($SHA.w32(a_high, a_low), $SHA.w32(b_high, b_low), $SHA.w32(c_high, c_low), $SHA.w32(d_high, d_low), $SHA.w32(e_high, e_low), $SHA.w32(f_high, f_low), $SHA.w32(g_high, g_low), $SHA.w32(h_high, h_low), $SHA.w32(k_high, k_low), $SHA.w32(w_high, w_low), $SHA.w32(new_a_high, new_a_low), $SHA.w32(new_e_high, new_e_low)) =
  $SHA.SHA256_ROUND_mk(wrong, choice, add1, add2, add3, add4, big0, majority, add5, add6, add7)

implement main0 () = ()
