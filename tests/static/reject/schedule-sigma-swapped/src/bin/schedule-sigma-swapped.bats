#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* W_t takes sigma 1 of W_t-2 and sigma 0 of W_t-15: sigma 0 of W_t-2 is
   not a schedule word *)
prfn claim {msg:$A.cells}{at,t:nat | 16 <= t}
  {b2h,b2l,b7h,b7l,b15h,b15l,b16h,b16l,s1h,s1l,s0h,s0l,m1h,m1l,m2h,m2l,rh,rl:nat}
  (back2: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t-2, b2h, b2l),
   back7: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t-7, b7h, b7l),
   back15: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t-15, b15h, b15l),
   back16: $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t-16, b16h, b16l),
   wrong: $SHA.SMALL_SIGMA_0(b2h, b2l, s1h, s1l), sigma0: $SHA.SMALL_SIGMA_0(b15h, b15l, s0h, s0l),
   a1: $AR.ADD32(s1h, s1l, b7h, b7l, m1h, m1l), a2: $AR.ADD32(m1h, m1l, s0h, s0l, m2h, m2l),
   a3: $AR.ADD32(m2h, m2l, b16h, b16l, rh, rl))
  : $SHA.SCHEDULE($SHA.sha256_kind(), msg, at, t, rh, rl) =
  $SHA.SCHEDULE_sha256(back2, back7, back15, back16, wrong, sigma0, a1, a2, a3)

implement main0 () = ()
