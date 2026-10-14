#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* update takes at most the bytes the array holds *)
fn claim {l:agz}{n:pos} (c: !$SHA.ctx, data: !$A.arr(byte, l, n), size: int n): void =
  $SHA.update(c, data, size + 1)

implement main0 () = ()
