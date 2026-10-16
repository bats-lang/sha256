#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a byte put after a sequence is the one asked for *)
prfn claim {message:$A.cells}{value,other_value:int} (list: $SHA.LIST(message)): [message_after:$A.cells] $SHA.SNOC(message, other_value, message_after) = let
  prval (snoc, _) = $SHA.snoc_list{message}{value}(list)
in snoc end

implement main0 () = ()
