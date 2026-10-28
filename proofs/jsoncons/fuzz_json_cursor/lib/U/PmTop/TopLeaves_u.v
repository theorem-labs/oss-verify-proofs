(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_leaves_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TL.
Module G := Cut_leaves_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Lemma ret_67c8c : CL.is_ret_at RSEGS 0x69b2c. Proof. CL.solve_is_ret. Qed.
Lemma ret_8c1a4 : CL.is_ret_at RSEGS 0x8e044. Proof. CL.solve_is_ret. Qed.
Definition CSV : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma csv_in : forall r : reg, In (bv_unsigned r) callee_saved_idx -> In (ridx r) CSV.
Proof. intros r H. unfold ridx. unfold callee_saved_idx in H. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem istream_dtor_ok : TPS.istream_dtor_spec L.
Proof.
  intros sp r fx R M model K Hh Hl HK0 Hfp (Hra & (Hr1 & Hr2) & Hsp & Htp & Hstk) Hcont.
  unfold PML.cfg. apply (CL.ret_cps RSEGS fx R _ M model K ret_67c8c Hh Hl).
  - rewrite Hra. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hr2.
  - rewrite Hra. apply (Hcont fx R M Hfp I); [apply L5.regs_preserved_refl | apply L5.frame_but_refl | apply mem_grows_refl].
Qed.

Theorem locale_dtor_ok : PMS.locale_dtor_spec L.
Proof.
  intros o sp r fx R M model K Hh Hl HK0 Hfp ((Hra & (Hr1 & Hr2) & Hsp & Htp & Hstk) & Ha0 & Hoz & Hcell) Hcont.
  pose (oz := o). assert (Ha0' : getr R 10%bv = Z_to_bv 64 oz) by exact Ha0. assert (Hcell' : L5.u64_at RSEGS M oz PML.CLASSIC_IMP) by exact Hcell.
  set (E := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (U10 : bv_unsigned (ev E 10) = oz) by (unfold E; rewrite (CL5.ev_reg R _ _ 10%bv), Ha0'; apply u64_of_Z; lia).
  change PML.PC_LOCALE_DTOR with (CC.cp_pc G.cp0).
  apply (TK.stretch_cps FPM G.cp0 fx E R M model K (G.plans 0%nat _ eq_refl) Hh Hl Hfp).
  - exact (regs_ok_id R _ _).
  - unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := oz) (z := PML.CLASSIC_IMP); [ev_start | lia | lia | reflexivity | exact Hcell'].
    + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. destruct k as [|k]; [|destruct k; discriminate Hnth]. injection Hnth as <-.
    rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    assert (Hag32 : env_agree 32 E E') by exact Hag.
    assert (R1 : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (TK.keeps_id_sound _ _ R _ _ E' R' M M' [1%nat] 1%bv HLF eq_refl Hag32 ltac:(cbn; tauto)); exact Hra).
    unfold PML.cfg. apply (CL.ret_cps RSEGS fx' R' _ M model K ret_8c1a4 Hh Hl).
    + rewrite R1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hr2.
    + rewrite R1. apply (Hcont fx' R' M Hfp' I); [| apply L5.frame_but_refl | apply mem_grows_refl].
      intros x Hx. exact (TK.keeps_id_sound _ _ R _ _ E' R' M M' CSV x HLF eq_refl Hag32 (csv_in x Hx)).
Qed.
End S.
End TL.

