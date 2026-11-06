(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnModel BnTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive sysop : Type := SyGetuid | SyGeteuid | SyGetgid | SyGetegid | SyOpenCnf.

Inductive aprog (ptr : Type) (A : Type) : Type :=
| ARet (a : A)
| AUnr
| AMalloc (n : Z) (k : option ptr -> aprog ptr A)
| AFree (p : ptr) (k : aprog ptr A)
| ARealloc (p : ptr) (n : Z) (k : option ptr -> aprog ptr A)
| AReallocS (p : ptr) (n : Z) (k : option ptr -> aprog ptr A)      (* [comment removed for export] *)
| ASys (o : sysop) (k : Z -> aprog ptr A)
| AReallocI (p : ptr) (n : Z) (k : option ptr -> aprog ptr A).     (* [comment removed for export] *)
Arguments ARet {ptr A} a.
Arguments AUnr {ptr A}.
Arguments AMalloc {ptr A} n k.
Arguments AFree {ptr A} p k.
Arguments ARealloc {ptr A} p n k.
Arguments AReallocS {ptr A} p n k.
Arguments ASys {ptr A} o k.
Arguments AReallocI {ptr A} p n k.

Fixpoint apbind {ptr A B} (m : aprog ptr A) (f : A -> aprog ptr B) : aprog ptr B :=
  match m with
  | ARet a => f a
  | AUnr => AUnr
  | AMalloc n k => AMalloc n (fun r => apbind (k r) f)
  | AFree p k => AFree p (apbind k f)
  | ARealloc p n k => ARealloc p n (fun r => apbind (k r) f)
  | AReallocS p n k => AReallocS p n (fun r => apbind (k r) f)
  | ASys o k => ASys o (fun r => apbind (k r) f)
  | AReallocI p n k => AReallocI p n (fun r => apbind (k r) f)
  end.

Lemma apbind_ret {ptr A B} (a : A) (f : A -> aprog ptr B) : apbind (ARet a) f = f a.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint bt_embed {ptr A} (t : btree ptr A) : aprog ptr A :=
  match t with
  | TRet a => ARet a
  | TUnr => AUnr
  | TMalloc n k => AMalloc n (fun r => bt_embed (k r))
  | TFree p k => AFree p (bt_embed k)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive aevent : Type :=
| AvMalloc (n : Z) (p : nat)
| AvFree (p : nat)
| AvRealloc (p : nat) (n : Z) (q : nat)
| AvSys (o : sysop) (r : Z)
| AvReallocI (p : nat) (n : Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sys_answer (o : sysop) : Z := match o with SyOpenCnf => -2 | _ => 1000 end.

Fixpoint run_aprog {A} (fuel : nat) (t : aprog nat A) (next : nat) (acc : list aevent) {struct fuel}
  : list aevent * nat * option A :=
  match fuel with
  | O => (rev acc, next, None)
  | S fuel' =>
    match t with
    | ARet a => (rev acc, next, Some a)
    | AUnr => (rev acc, next, None)
    | AMalloc n k => run_aprog fuel' (k (Some next)) (S next) (AvMalloc n next :: acc)
    | AFree p k => run_aprog fuel' k next (AvFree p :: acc)
    | ARealloc p n k => run_aprog fuel' (k (Some next)) (S next) (AvRealloc p n next :: acc)
    | AReallocS p n k => run_aprog fuel' (k (Some next)) (S next) (AvRealloc p n next :: acc)
    | ASys o k => run_aprog fuel' (k (sys_answer o)) next (AvSys o (sys_answer o) :: acc)
    | AReallocI p n k => run_aprog fuel' (k (Some p)) next (AvReallocI p n :: acc)       (* [comment removed for export] *)
    end
  end.
