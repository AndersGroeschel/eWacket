Require Import wacket.
Require Import observable.
Require Import wasmLite.
Require Import List.

Require Import String.
Require Import ZArith.
Local Open Scope Z_scope.



Inductive compilerResult : Type :=
| Succ : wasmCode -> compilerResult
| Error : string -> compilerResult
.

(* a compiler from dupe to wasm, does not do any sort of type checking
     and can produce wasm code that can't transition *)
Fixpoint compile_unsafe (source : dupe) (compiled : wasmCode) := match source with 
| D_Integer z => ((i64.const z)::compiled)
| D_Boolean b => ((i32.const (if b then 1 else 0))::compiled)
| D_add1 e => compile_unsafe e ((i64.const 1)::(i64.add)::compiled)
| D_sub1 e => compile_unsafe e ((i64.const 1)::(i64.add)::compiled)
| D_zero e => compile_unsafe e (i64.eqz::compiled)
| D_if b t e => 
    (compile_unsafe b 
    ((ifThenElse 
        (compile_unsafe t nil) 
        (compile_unsafe e nil)
    )::compiled))
end.


