(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_libiface D_auxv Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_activewA Atp_defsA Pj_lftoi1A Pj_defsA Pj_os_defsA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Arm21.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Theorem arm21_okA : forall W, arm_cpsA RT PMc W 21.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  change (el_arm_pcA 21) with EL_EXIT_A.
  eapply (POST false (rt_credit RT Σ) Σ m fc F).
  unfold arm_postA.
  split; [cbn [artxA]; split; [exact ARTg| reflexivity]|]. split; [exact MIg|]. split; [exact STg|]. split; [exact FRM|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [change (arm_costA 21 (ae_n E) (ae_sn E) (zlength (ae_p1 E))) with 0; lia|].
  split; [unfold rt_pres_fp; intros x _ _; reflexivity|].
  split; [exists jr, jos; exact AM| intros D; discriminate D].
Qed.
End Arm21.
