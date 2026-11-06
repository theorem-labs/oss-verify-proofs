(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation B0 := (Z_to_bv 8 0).

(* [comment removed for export] *)
Lemma rdn_nth1 : forall segs mem (a : word) (n : nat) (bs : list byte) (j : nat),
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) 1 = Some [nth j bs B0].
Proof.
  intros segs mem a n bs j H Hj.
  rewrite (rdn_sub segs mem n a bs j 1 H) by lia.
  rewrite sub_nth; [reflexivity|]. rewrite (rdn_length _ _ _ _ _ H). exact Hj.
Qed.

Lemma rdn_nth1_0 : forall segs mem (a : word) (n : nat) (bs : list byte),
  rdn segs mem a n = Some bs -> (0 < n)%nat ->
  rdn segs mem a 1 = Some [nth 0 bs B0].
Proof. intros segs mem a n bs H Hn. rewrite <- (at_0 a). apply (rdn_nth1 segs mem a n bs 0 H Hn). Qed.

(* [comment removed for export] *)
Lemma rdn_subrun : forall segs mem (a : word) (n : nat) (bs : list byte) (j k : nat),
  rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof. intros. eapply rdn_sub; eassumption. Qed.

Lemma byte_neq_u : forall x y : byte, x <> y -> bv_unsigned x <> bv_unsigned y.
Proof. intros x y H E. apply H. apply bv_eq. exact E. Qed.

Lemma byte_eq_dec : forall x y : byte, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned y)) as [E|NE].
  - left. apply bv_eq. exact E.
  - right. intros ->. apply NE. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma runs_trans_k : forall {A : Type} segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> A -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2 (k : A), msteps segs (st1 r1) (st2 r2) /\ P2 r2 k) ->
  exists r2 (k : A), msteps segs s0 (st2 r2) /\ P2 r2 k.
Proof.
  intros A segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & k & R2 & H2).
  exists r2, k. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
Lemma runs_trans_km : forall {A : Type} segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> A -> machine_state) (P2 : bvmap 5 word -> A -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2 (k : A), msteps segs (st1 r1) (st2 r2 k) /\ P2 r2 k) ->
  exists r2 (k : A), msteps segs s0 (st2 r2 k) /\ P2 r2 k.
Proof.
  intros A segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & k & R2 & H2).
  exists r2, k. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
Lemma regs_agree_list_keeps_cs : forall (clob : list reg) regs regs',
  forallb (fun r => negb (existsb (fun x => bv_eqb x r) callee_saved)) clob = true ->
  regs_agree (fun r => In r clob) regs regs' -> keeps_cs regs regs'.
Proof.
  intros clob regs regs' Hf AG r Hr. apply AG. intros Hin.
  pose proof (ZStores.forallb_In _ _ _ Hf Hin) as E. cbn beta in E.
  apply negb_true_iff in E.
  assert (existsb (fun x : reg => bv_eqb x r) callee_saved = true); [|congruence].
  apply existsb_exists. exists r. split; [exact Hr | apply bv_eqb_refl].
Qed.

Lemma regs_agree_list_keeps : forall (clob : list reg) regs regs',
  forallb (fun r => negb (existsb (fun x => bv_eqb x r) callee_kept)) clob = true ->
  regs_agree (fun r => In r clob) regs regs' -> keeps regs regs'.
Proof.
  intros clob regs regs' Hf AG r Hr. apply AG. intros Hin.
  pose proof (ZStores.forallb_In _ _ _ Hf Hin) as E. cbn beta in E.
  apply negb_true_iff in E.
  assert (existsb (fun x : reg => bv_eqb x r) callee_kept = true); [|congruence].
  apply existsb_exists. exists r. split; [exact Hr | apply bv_eqb_refl].
Qed.

(* [comment removed for export] *)
Lemma regs_agree_drop : forall (C : list reg) (r : reg) regs regs',
  regs_agree (fun x => In x (r :: C)) regs regs' -> getr regs' r = getr regs r ->
  regs_agree (fun x => In x C) regs regs'.
Proof.
  intros C r regs regs' AG E x Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned r)) as [Heq|Hne].
  - assert (x = r) by (apply bv_eq; exact Heq). subst x. exact E.
  - apply AG. intros [Hr|Hin]; [|exact (Hx Hin)]. apply Hne. rewrite Hr. reflexivity.
Qed.
