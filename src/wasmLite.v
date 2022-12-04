Require Import List ZArith.
Local Open Scope Z_scope.

Require Import typeDefs.

(* based on definitions laid out here: 
   https://webassembly.github.io/spec/core/intro/index.html *)

Inductive wasmInstruction : Type :=
| i64_const: i64 -> wasmInstruction (* adds i64 to stack*)
| i32_const: i32 -> wasmInstruction (* adds i32 to stack*)
| i64_add: wasmInstruction (* pops 2 i64 from stack and pushes there sum*)
| i64_sub: wasmInstruction (* pops 2 i64 from stack and pushes there difference*)
| i64_eqz: wasmInstruction (* pops 1 i64 from stack and pushes an i32, 0 if false, 1 if true*)

(* pops a value (i64 or i32) from the stack, 
    if zero then add else branch to code otherwise add if branch to code*)
| ifThenElse: (list wasmInstruction) -> (list wasmInstruction) -> wasmInstruction 
| nop: wasmInstruction
| unreachable: wasmInstruction
.

Inductive wasmValue : Type :=
| v_i64: i64 -> wasmValue
| v_i32: i32 -> wasmValue
| trap
.


Notation "'i64.const' x" := (i64_const x) (at level 99).
Notation "'i32.const' x" := (i32_const x) (at level 99).
Notation "'i64.add' ( x ) ( y )" := (i64_add) (at level 99).
Notation "'i64.sub' ( x ) ( y )" := (i64_sub) (at level 99).
Notation "'i64.eqz' ( x )" := (i64_eqz) (at level 99).
Notation "'if' '(then' t ) '(else' e )" := (ifThenElse t e) (at level 99).


Definition wasmStack := list wasmValue.

Definition wasmCode := list wasmInstruction.

Definition wasmStep (C : wasmCode) (st : wasmStack) := match C with 
| (i64_const z)::rest => (rest, (v_i64 z)::st)
| (i32_const z)::rest  => (rest, (v_i64 z)::st)
| (i64_add)::rest => match st with 
    | (v_i64 x)::(v_i64 y)::st' => (rest, (v_i64 (x + y))::st')
    | _::trap::st' => (rest,trap::st')
    | trap::st' => (rest,trap::st')
    | _ => (rest,trap::st)
    end
| (i64_sub)::rest => match st with 
    | (v_i64 x)::(v_i64 y)::st' => (rest, (v_i64 (x - y))::st')
    | _::trap::st' => (rest,trap::st')
    | trap::st' => (rest,trap::st')
    | _ => (rest,trap::st)
    end
| (i64_eqz)::rest => match st with 
    | (v_i64 z)::st' => (rest,(v_i32 (if z =? 0 then  1 else 0))::st')
    | trap::st' => (rest,trap::st')
    | _ => (rest,trap::st)
    end
| (ifThenElse t e)::rest => match st with 
    | (v_i64 z)::st' => if Z.eqb 0 z then (e ++ rest, st') else (t ++ rest, st')
    | (v_i32 z)::st' => if Z.eqb 0 z then (e ++ rest, st') else (t ++ rest, st')
    | trap::st' => (rest,trap::st')
    | st => (rest,trap::st)
    end
| nop::rest => (rest,st)
| unreachable::rest => (rest, trap::st)
| nil => (nil,st)
end.


