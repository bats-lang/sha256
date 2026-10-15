#include "share/atspre_staload.hats"
#use sha256 as SHA

(* a proof of the upper case sigma 0 of a word is not one of sigma 1 *)
prfn claim {h,l,rh,rl:nat} (pf: $SHA.BIG_SIGMA_0(h, l, rh, rl)): $SHA.BIG_SIGMA_1(h, l, rh, rl) = pf

implement main0 () = ()
