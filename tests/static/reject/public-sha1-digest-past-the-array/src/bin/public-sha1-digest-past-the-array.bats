#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* sha1_digest takes at most the bytes the array holds *)
fn claim {l:agz}{n:pos}{lo:agz} (data: !$A.borrow(byte, l, n), size: int n, out: !$A.arr(byte, lo, 20)): void =
  $SHA.sha1_digest(data, size + 1, out)

implement main0 () = ()
