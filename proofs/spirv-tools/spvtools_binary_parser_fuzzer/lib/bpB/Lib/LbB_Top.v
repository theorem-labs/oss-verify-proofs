(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH1 LbB_TopH2 LbB_TopA LbB_TopA1 LbB_TopT LbB_TopM.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Top.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis HPO : binary_parse_stmtA H LINV_P5.

  Theorem fuzz_A : fuzz_stmt H FZP_A.
  Proof.
    unfold fuzz_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF CH D N lo B shi ds errv.
    intros VIS FZ Ha0 Ha1 BY LEN NR D16 PD DZ RH KR BS BC BL RA SPB BB SP16 ST CE LO ER MI TP LV RA2 AC ADD RF LFL S0 SSHI CHN PF CHU TRO ALs.
    cbn [fz_inv fz_small fz_cnt fz_large fz_pf fz_tr_ok fz_cost FZP_A] in *.
    pose proof (rt_bp_base H HH) as HB.
    set (e := HEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF CH D N lo B shi ds).
    assert (HP : hpre H e).
    { unfold hpre. cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m e_mo e_s e_LB e_LF
                        e_CH e_D e_N e_lo e_B e_shi e_ds e eSP].
      split; [exact FZ|]. split; [exact BY|]. split; [exact LEN|]. split; [split; [lia | exact NR]|]. split; [exact D16|].
      split; [exact PD|]. split; [exact DZ|]. split; [exact RH|]. split; [exact BS|]. split; [exact BC|]. split; [exact BL|].
      split; [exact RA|]. split; [exact SPB|]. split; [exact BB|]. split; [exact SP16|]. split; [exact ST|]. split; [exact CE|].
      split; [exact LO|]. split; [exists errv; exact ER|]. split; [exact MI|]. split; [exact TP|]. split; [exact LV|].
      split; [exact RA2|]. split; [exact AC|]. split; [exact ADD|]. split; [exact RF|]. split; [exact LFL|]. split; [exact S0|].
      split; [exact SSHI|]. split; [exact CHN|]. split; [exact PF|]. split; [exact CHU|]. exact ALs. }
    subst a0 a1.
    change (hpost H e (mkCfg msF mo)) with (hpost H e (mkCfg msF mo)).
    change (fuzz_post H FZP_A ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF N lo B shi m mo) with (hpost H e).
    destruct (Z.eq_dec N 0) as [N0|N0].
    -
      eapply (ahh_evt_then H HB (hZ_post H e)); [exact KR | exact VIS | |].
      { eapply evt_cut; [exact (tA0 H HH e t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP)|].
        intros ms1 P1. exact (tAz H HH e ms1 HP N0 P1). }
      intros msF1 mo1 KR1 MP1 PZ.
      destruct PZ as (ff & fp & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & VIS1 & HI1).
      apply (seg_T H HH e (mkCfg msF1 mo1) HP).
      exists ff, fp, [], s, LB, F, fc, x1, x5, x6, x7, (Z_to_bv 64 (eS1 e)), x10, x11, x12, x13, x14, x15, x16, x17,
        (Z_to_bv 64 (sh ff + 4)), (Z_to_bv 64 (sh ff)), (Z_to_bv 64 0x7fff8000), (e_s7 e), (e_s8 e), (e_s9 e), (e_s10 e), (Z_to_bv 64 0),
        x28, x29, x30, x31, m'.
      cbn [cfg_ms cfg_model]. split; [exact VIS1|]. split; [exact KR1|]. split; [exact MP1|]. split; [exact FZ|].
      split; [exact HI1|]. split; [apply Permutation_refl|].
      pose proof (top_cost_nonneg N ltac:(lia)). cbn [e_s e_N e]. lia.
    -
      eapply (ahh_evt_then H HB (hA_post H e)); [exact KR | exact VIS | |].
      { eapply evt_cut; [exact (tA0 H HH e t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP)|].
        intros ms1 P1. exact (tA1 H HH e ms1 HP ltac:(cbn [e_N e]; lia) P1). }
      intros msF1 mo1 KR1 MP1 PA.
      exact (seg_CC H HH HPO TRO e msF1 mo1 HP ltac:(cbn [e_N e]; lia) KR1 MP1 PA).
  Qed.
End Top.
