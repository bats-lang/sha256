#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* hash is of at least one byte: the empty message is init, then finish *)
fn claim {l:agz}{lo:agz} (data: !$A.arr(byte, l, 1), out: !$A.arr(byte, lo, 64)): void =
  $SHA.hash(data, 0, out)

implement main0 () = ()
