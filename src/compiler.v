Require Import wacket.
Require Import wasmLite.
Require Import List.

Require Import ZArith.
Local Open Scope Z_scope.
Open Scope list_scope.


(* a compiler from dupe to wasm, does not do any sort of type checking
     and can produce wasm code that can't transition *)
Fixpoint compile_unsafe (source : dupe) := match source with 
| D_Integer z => ((i64.const z)::nil)
| D_Boolean b => ((i32.const (if b then 1 else 0))::nil)
| D_add1 e => (compile_unsafe e) ++ ((i64.const 1)::(i64.add)::nil)
| D_sub1 e => (compile_unsafe e) ++ ((i64.const 1)::(i64.add)::nil)
| D_zero e => (compile_unsafe e) ++ (i64.eqz::nil)
| D_if b t e => 
    (compile_unsafe b) ++ 
    ((ifThenElse (compile_unsafe t) (compile_unsafe e))::nil)
end.



