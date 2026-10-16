#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* f_t is Ch only for t from 0 to 19: round 20 takes Parity *)
prfn claim {bh,bl,ch,cl,dh,dl,fh,fl:nat}
  (choice: $SHA.CH(bh, bl, ch, cl, dh, dl, fh, fl))
  : $SHA.SHA1_F(20, bh, bl, ch, cl, dh, dl, fh, fl) =
  $SHA.SHA1_F_choose(choice)

implement main0 () = ()
