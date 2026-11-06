(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.



Lemma lb_remove_cons_other : forall p b LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof.
  intros p b LB H. unfold lb_remove. cbn [List.filter].
  destruct (bid_eqb_spec (blk_id b) p); [contradiction|]. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive bcfg : Type := BNone | BFast (bt : ablock) | BSmall (b4 b6 : ablock) | BHalf (b6 : ablock) | BHalf4 (b4 : ablock).
Definition cfg_extra (c : bcfg) : list ablock :=
  match c with BNone => [] | BFast bt => [bt] | BSmall b4 b6 => [b4; b6] | BHalf b6 => [b6] | BHalf4 b4 => [b4] end.
Definition cfg_tt (c : bcfg) : Z := match c with BFast bt => blk_addr bt | _ => 0 end.
Definition cfg_l16 (c : bcfg) : Z := match c with BSmall _ b6 => blk_addr b6 | BHalf b6 => blk_addr b6 | _ => 0 end.
Definition cfg_l4 (c : bcfg) : Z := match c with BSmall b4 _ => blk_addr b4 | BHalf4 b4 => blk_addr b4 | _ => 0 end.

Lemma nodup_cons_inv : forall (x : bid) (l : list bid), NoDup (x :: l) -> ~ In x l /\ NoDup l.
Proof.
  intros x l H. inversion H; subst. split; [|assumption].
  intros I. apply H2. apply list_elem_of_In. exact I.
Qed.

Lemma ablock_eta : forall b : ablock, b = (blk_id b, blk_addr b, blk_size b).
Proof. intros [[i a] n]. reflexivity. Qed.


(* [comment removed for export] *)
Definition cfg_sizes_ok (c : bcfg) (n : Z) : Prop :=
  match c with
  | BNone => True
  | BFast bt => blk_size bt = 400000 * n
  | BSmall b4 b6 => blk_size b4 = 50000 * n /\ blk_size b6 = 200000 * n
  | BHalf _ => True   (* [comment removed for export] *)
  | BHalf4 _ => True
  end.

(* [comment removed for export] *)
Definition cfg_shape_ok (c : bcfg) (small n : Z) : Prop :=
  match c with
  | BNone => n = 0
  | BFast _ => small = 0
  | BSmall _ _ => small = 1
  | BHalf _ => small = 1 /\ n = 0
  | BHalf4 _ => small = 1 /\ n = 0   (* [comment removed for export] *)
  end.

Lemma nodup_app_disj : forall (l1 l2 : list bid) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND I1 I2; [destruct I1|].
  cbn in ND. apply nodup_cons_inv in ND as [NI ND]. destruct I1 as [->|I1].
  - apply NI. apply in_or_app. right. exact I2.
  - exact (IH l2 x ND I1 I2).
Qed.

Lemma outside_app : forall A B x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof.
  induction A as [|[l h] A IH]; intros B x; cbn; [tauto|]. rewrite IH. tauto.
Qed.

End ACeilS1.
