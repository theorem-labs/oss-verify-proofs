(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.

Definition resp := SyscallEffect.

Module Exc.
#[universes(template)]
Inductive exc (A : Type) : Type := Unr | Ok (a : A).
Arguments Unr {A}.
Arguments Ok {A} a.
End Exc.
Import Exc.

Inductive itree (node : Type) (R : Type) : Type :=
| Ret (r : R)
| Vis (n : node) (k : resp -> itree node R).
Arguments Ret {node R} r.
Arguments Vis {node R} n k.

Fixpoint bind (node : Type) {A B} (t : itree node A) (f : A -> itree node B) : itree node B :=
match t with
| Ret r => f r
| Vis n k => Vis n (fun x => bind node (k x) f)
end.

Definition ebind {node A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) : itree node (exc B) :=
bind node t (fun r => match r with Unr => Ret Unr | Ok a => f a end).

Definition enode {node A} (n : node) (pl : resp -> option A) : itree node (exc A) :=
Vis n (fun rsp => match pl rsp with Some a => Ret (Ok a) | None => Ret Unr end).
