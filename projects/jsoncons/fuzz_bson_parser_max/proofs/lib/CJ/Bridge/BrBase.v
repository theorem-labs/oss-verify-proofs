(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Bridge Require Import BrRegs.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_msteps_cat : forall a b, Exec.msteps segs a b -> CatSim.msteps segs a b.
Proof.
  intros a b H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
  impl segs (at_node segs) (ITree.bind _ t f) Q ms ->
  impl segs (at_node segs) t (fun r ms' => impl segs (at_node segs) (f r) Q ms') ms.
Proof.
  intros A B t. induction t as [r | n k IH]; intros f Q ms H; cbn in *.
  - apply evt_done. exact H.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. apply IH. apply Hk.
Qed.

Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms,
  impl segs (at_node segs) (ebind t f) (epost Q) ms ->
  impl segs (at_node segs) t
       (fun r ms' => match r with Ok a => impl segs (at_node segs) (f a) (epost Q) ms' | Unr => True end) ms.
Proof.
  intros A B t f Q ms H. unfold ebind in H. apply impl_bind_inv in H.
  eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

(* [comment removed for export] *)
Lemma impl_vis_inv : forall {A} n (k : resp -> itree node A) Q ms,
  impl segs (at_node segs) (Vis n k) Q ms ->
  evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. intros A n k Q ms H. exact H. Qed.

Lemma impl_enode_inv : forall {A} n (pl : resp -> option A) Q ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms.
Proof.
  intros A n pl Q ms H. cbn in H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp a E. specialize (Hk rsp). rewrite E in Hk. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma areg_eqv : forall ms ms' r, ms_eqv ms ms' -> is_x0 r = false -> areg ms r = areg ms' r.
Proof. intros ms ms' r (HR & _) Hr. unfold areg. apply HR, Hr. Qed.

Lemma at_node_eqv : forall n ms ms', ms_eqv ms ms' -> at_node segs n ms -> at_node segs n ms'.
Proof.
  intros n ms ms' Heqv Hat. pose proof Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  destruct n; cbn [at_node] in *; rewrite <- ?Hsvc, <- ?Hm, <- ?Hro;
    repeat (rewrite <- (areg_eqv ms ms' _ Heqv) by (vm_compute; reflexivity)); exact Hat.
Qed.

Lemma nret_eqv : forall ms ms' rsp, ms_eqv ms ms' -> ms_eqv (nret ms rsp) (nret ms' rsp).
Proof. intros ms ms' rsp H. unfold nret. apply advance_past_svc_eqv, apply_effect_eqv, H. Qed.

(* [comment removed for export] *)
Lemma evt_eqv_transfer : forall P ms ms', ms_eqv ms ms' -> evt segs P ms ->
  exists ms1 ms1', P ms1 /\ ms_eqv ms1 ms1' /\ CatSim.msteps segs ms' ms1'.
Proof.
  intros P ms ms' Heqv (ms1 & Hms & HP).
  destruct (msteps_eqv segs ms ms1 (cj_msteps_cat _ _ Hms) ms' Heqv) as (ms1' & Hms' & Heqv1).
  exists ms1, ms1'. auto.
Qed.

End WithSegs.
