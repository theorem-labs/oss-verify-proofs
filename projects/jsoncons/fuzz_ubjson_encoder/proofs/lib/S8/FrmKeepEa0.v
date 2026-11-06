(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim FPSteps FrmKeep FrmKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require FrmFastScan.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.

Module FRMA0.
Definition XLO : Z := 0x51000.
Definition XSZ : Z := 0xe1000.

Lemma segs_facts :
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      && (negb (seg_executable seg) || ((Z.of_N (seg_base seg) =? XLO) && (Z.of_N (seg_size seg) =? XSZ)))) RSEGS = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma FSCAN : forallb (FrmFastScan.FRMF.fseg FRM.word_frm_safe RSEGS 450 1024) RSEGS = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma no_wx : forall seg, In seg RSEGS -> seg_executable seg && seg_writable seg = false.
Proof.
  intros seg IN. pose proof (proj1 (forallb_forall _ _) segs_facts seg IN) as H. cbn beta in H.
  apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
Qed.
Lemma xseg : forall seg, In seg RSEGS -> seg_executable seg = true -> Z.of_N (seg_base seg) = XLO /\ Z.of_N (seg_size seg) = XSZ.
Proof.
  intros seg IN X. pose proof (proj1 (forallb_forall _ _) segs_facts seg IN) as H. cbn beta in H.
  apply andb_true_iff in H as [_ H]. rewrite X in H. cbn [negb orb] in H. apply andb_true_iff in H as [H1 H2].
  split; apply Z.eqb_eq; assumption.
Qed.

Theorem fetch_safe : forall a w, fetch_word RSEGS a = Some w \/ fetch_tail RSEGS a = Some w -> FRM.word_frm_safe w = true.
Proof. exact (FrmFastScan.FRMF.fetch_safe_of_fscan_FRM RSEGS 450 1024 FSCAN). Qed.

Theorem step_fz : forall s s', RiscvSemantics.step RSEGS s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof. exact (FRM.step_fz RSEGS no_wx fetch_safe). Qed.
Theorem msteps_fz : forall s s', msteps RSEGS s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof. exact (FRM.msteps_fz RSEGS no_wx fetch_safe). Qed.
Theorem msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps RSEGS (@mkst fx R pc M (seg_rom RSEGS)) (@mkst fx' R' pc' M' (seg_rom RSEGS)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof. exact (FRM.msteps_fz_mkst RSEGS no_wx fetch_safe fx fx' R R' pc pc' M M'). Qed.
End FRMA0.

Ltac frm_solve := FRMK.frm_solve_with FRMA0.msteps_fz_mkst.
