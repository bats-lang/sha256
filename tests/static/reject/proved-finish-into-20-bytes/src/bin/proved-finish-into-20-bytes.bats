#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* finish writes 64 hex digits *)
fn claim {lo:agz} (c: $SHA.proved_ctx, out: !$A.arr(byte, lo, 20)): void =
  $SHA.proved_finish(c, out)

implement main0 () = ()
