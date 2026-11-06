(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon AzStrResizeT.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RESIZE_S0 : nat := 100.     (* [comment removed for export] *)
Definition RESIZE_L0 : nat := 110.     (* [comment removed for export] *)
Definition NCLASSES : nat := 7.
Definition class_of (j : nat) : option Z := nth_error CLASSES j.

Definition CT2_resize (id : nat) : option gcallee2 :=
  if Nat.ltb id RESIZE_S0 then None
  else if Nat.ltb id (RESIZE_S0 + NCLASSES) then option_map ceS (class_of (id - RESIZE_S0))
  else if Nat.ltb id RESIZE_L0 then None
  else if Nat.ltb id (RESIZE_L0 + NCLASSES) then option_map ceL (class_of (id - RESIZE_L0))
  else None.

(* [comment removed for export] *)
Definition ct2_or (T1 T2 : nat -> option gcallee2) (id : nat) : option gcallee2 :=
  match T1 id with Some c => Some c | None => T2 id end.


(* [comment removed for export] *)
Definition resize_args_S (s mtr fb : expr) : list expr := [ELit 0; ELit 0; s; mtr; fb].
Definition resize_args_L (d sz A mtr fb : expr) : list expr := [ELit 0; ELit 0; d; sz; A; mtr; fb].

Lemma class_of_in : forall j NB, class_of j = Some NB -> In NB CLASSES.
Proof. intros j NB H. unfold class_of in H. eapply nth_error_In. exact H. Qed.

Lemma CT2_resize_cases : forall id c, CT2_resize id = Some c ->
  exists NB, In NB CLASSES /\ (c = ceS NB \/ c = ceL NB).
Proof.
  intros id c H. unfold CT2_resize in H.
  destruct (Nat.ltb id RESIZE_S0); [discriminate|].
  destruct (Nat.ltb id (RESIZE_S0 + NCLASSES)).
  - destruct (class_of (id - RESIZE_S0)) as [NB|] eqn:E; [|discriminate]. cbn in H. injection H as <-.
    exists NB. split; [eapply class_of_in; exact E | left; reflexivity].
  - destruct (Nat.ltb id RESIZE_L0); [discriminate|]. destruct (Nat.ltb id (RESIZE_L0 + NCLASSES)); [|discriminate].
    destruct (class_of (id - RESIZE_L0)) as [NB|] eqn:E; [|discriminate]. cbn in H. injection H as <-.
    exists NB. split; [eapply class_of_in; exact E | right; reflexivity].
Qed.

Lemma ct2_or_sound : forall (P : gcallee2 -> Prop) (T1 T2 : nat -> option gcallee2),
  (forall id c, T1 id = Some c -> P c) -> (forall id c, T2 id = Some c -> P c) ->
  forall id c, ct2_or T1 T2 id = Some c -> P c.
Proof.
  intros P T1 T2 H1 H2 id c H. unfold ct2_or in H. destruct (T1 id) as [c1|] eqn:E.
  - injection H as <-. exact (H1 id c1 E).
  - exact (H2 id c H).
Qed.


