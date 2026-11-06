(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec SeqExec SymExec PropExecFP SymExecFP SymExecFPSound LibBswap.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SXF. Import SXFS.

(* [comment removed for export] *)
Definition bytes_bits_sx (ks : list nat) (k0 : nat) : list bbit :=
  flat_map (fun k => map (fun j => BV k j) (seq 0 8)) ks ++ repeat (BV k0 7%nat) (64 - 8 * length ks).

Section Sx.
Variable E : env.
Variable nu : nat -> Z.
Hypothesis Hnu : forall k, 0 <= nu k < 256.

Lemma wbits_same_vals : forall x l1 l2,
  wbits nu x l1 -> length l2 = 64%nat ->
  (forall i, (i < 64)%nat -> bval nu (nth i l1 BO) = bval nu (nth i l2 BO)) ->
  wbits nu x l2.
Proof.
  intros x l1 l2 [L1 W1] L2 Hsame. split; [exact L2|].
  intros i Hi. rewrite (W1 i Hi). apply Hsame. exact Hi.
Qed.

Lemma nth_app_cases : forall {A} (l1 l2 : list A) i (d : A),
  nth i (l1 ++ l2) d = if (i <? length l1)%nat then nth i l1 d else nth (i - length l1) l2 d.
Proof.
  intros A l1 l2 i d. destruct (Nat.ltb_spec i (length l1)).
  - apply app_nth1. assumption.
  - apply app_nth2. assumption.
Qed.

Lemma flat_map_bytes_length : forall ks,
  length (flat_map (fun k => map (fun j => BV k j) (seq 0 8)) ks) = (8 * length ks)%nat.
Proof. induction ks as [|k ks IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, IH, length_map, length_seq. cbn [length]. lia. Qed.

Lemma nth_repeat_any : forall {A} (a d : A) n i, (i < n)%nat -> nth i (repeat a n) d = a.
Proof. intros A a d n. induction n as [|n IH]; intros [|i] Hi; cbn; try lia; auto. apply IH. lia. Qed.

(* [comment removed for export] *)
Theorem beval_bytes_sx : forall atoms e ks k0,
  atoms_ok E nu atoms ->
  (length ks <= 8)%nat ->
  Z.testbit (nu k0) 7 = false ->
  match beval atoms e with Some l => list_bbit_eqb l (bytes_bits_sx ks k0) | None => false end = true ->
  bv_unsigned (edenot E e) = bytes_val nu ks.
Proof.
  intros atoms e ks k0 Hok Hlen Hbit H.
  destruct (beval atoms e) as [l|] eqn:Hb; [|discriminate].
  apply list_bbit_eqb_eq in H. subst l.
  apply (wbits_bytes_val nu Hnu); [exact Hlen | apply u64_range |].
  eapply wbits_same_vals; [eapply beval_sound; eassumption | |].
  - unfold bytes_bits. rewrite length_app, flat_map_bytes_length, repeat_length. lia.
  - intros i Hi. unfold bytes_bits_sx, bytes_bits.
    rewrite !nth_app_cases. rewrite !flat_map_bytes_length.
    destruct (Nat.ltb_spec i (8 * length ks)); [reflexivity|].
    rewrite !nth_repeat_any by lia. cbn [bval]. replace (Z.of_nat 7) with 7 by reflexivity. exact Hbit.
Qed.
End Sx.
