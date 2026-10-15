#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a context is finished once *)
fn claim {lo:agz} (c: $SHA.proved_ctx, out: !$A.arr(byte, lo, 64)): void = let
  val () = $SHA.proved_finish(c, out)
  val () = $SHA.proved_finish(c, out)
in end

implement main0 () = ()
