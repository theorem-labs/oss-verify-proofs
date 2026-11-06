(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes Frame.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import Monad.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Bridge Require Import BrRegs BrBase.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma cat_msteps_cj : forall a b, CatSim.msteps segs a b -> Exec.msteps segs a b.
Proof.
  intros a b H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
  - apply Exec.msteps_refl.
  - eapply Exec.msteps_cons; [split; [exact Hsvc| exact Hstep]| exact IH].
Qed.

Lemma impl_eqv_transfer : forall {R} (t : itree node R) Q ms ms',
  impl segs (at_node segs) t Q ms -> ms_eqv ms ms' ->
  impl segs (at_node segs) t (fun r ms1' => exists ms1, Q r ms1 /\ ms_eqv ms1 ms1') ms'.
Proof.
  intros R t. induction t as [r | n k IH]; intros Q ms ms' H Heqv; cbn [impl] in *.
  - destruct (evt_eqv_transfer segs _ _ _ Heqv H) as (ms1 & ms1' & HQ & Heqv1 & Hms).
    exists ms1'. split; [apply cat_msteps_cj; exact Hms|]. exists ms1. auto.
  - destruct (evt_eqv_transfer segs _ _ _ Heqv H) as (ms1 & ms1' & [Hat Hk] & Heqv1 & Hms).
    exists ms1'. split; [apply cat_msteps_cj; exact Hms|]. split; [eapply at_node_eqv; [exact Heqv1| exact Hat]|].
    intros rsp. eapply IH; [apply Hk| apply nret_eqv; exact Heqv1].
Qed.

Lemma implM_eqv_transfer : forall {St A} (c : Monad.M St A) s Q ms ms',
  implM segs c s Q ms -> ms_eqv ms ms' ->
  implM segs c s (fun a s' ms1' => exists ms1, Q a s' ms1 /\ ms_eqv ms1 ms1') ms'.
Proof.
  intros St A c s Q ms ms' H Heqv. unfold implM in *.
  eapply impl_mono; [eapply impl_eqv_transfer; [exact H| exact Heqv]|].
  intros [|[a s']] ms1' (ms1 & HQ & Heqv1); cbn in *; [exact I|]. exists ms1. auto.
Qed.

(* [comment removed for export] *)
Context {fx : FPState}.

Lemma mkst_eqv_canon : forall R pc M rom,
  ms_eqv (MS (canon_regs R) fp_regs pc fp_csr None M rom) (mkst R pc M rom).
Proof.
  intros R pc M rom. unfold ms_eqv, MS, mkst; cbn. repeat split; try reflexivity.
  apply regs_eqv_sym, canon_regs_eqv.
Qed.

(* [comment removed for export] *)
Lemma MS_is_mkst : forall R pc M rom, MS R fp_regs pc fp_csr None M rom = mkst R pc M rom.
Proof. reflexivity. Qed.

Lemma ms_eqv_MS_inv : forall R F pc fc m rom ms',
  ms_eqv (MS R F pc fc None m rom) ms' ->
  ms' = MS (ms_regs ms') F pc fc None m rom /\ regs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m rom [R' F' pc' svc' rv' fc' m' rom'] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); cbn in *.
  subst. split; [reflexivity| exact H1].
Qed.

End WithSegs.
