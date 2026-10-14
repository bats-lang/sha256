#include "share/atspre_staload.hats"
#use arith as AR
#use sha256 as SHA

(* sigma 0 rotates by 2, 13 and 22: a rotation by 3 in place of 2 is not
   a proof of it *)
prfn claim {h,l,ah,al,bh,bl,ch,cl,sh,sl,rh,rl:nat}
  (r3: $AR.ROTR(3, h, l, ah, al), r13: $AR.ROTR(13, h, l, bh, bl), r22: $AR.ROTR(22, h, l, ch, cl),
   xh: $AR.XOR(ah, bh, sh), xl: $AR.XOR(al, bl, sl), yh: $AR.XOR(sh, ch, rh), yl: $AR.XOR(sl, cl, rl))
  : $SHA.BIG_SIGMA_0(h, l, rh, rl) = $SHA.BIG_SIGMA_0_mk(r3, r13, r22, xh, xl, yh, yl)

implement main0 () = ()
