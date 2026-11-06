(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition pop_arg_entry := 0x2714b0%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_SIZET := 20%Z.
(* [comment removed for export] *)
Definition T_LONG := 13%Z. Definition T_ULONG := 14%Z.
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else slot.
Definition pop_arg_hi (ty : Z) (slot y : word) : word := y.


Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.




Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

