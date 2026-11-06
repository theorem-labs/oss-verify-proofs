(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_SR LbA_Conv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_Own LbA_RtOwn LbA_DStat LbA_HKit LbA_HStKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit2 LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoQ LbA_WoF LbA_WoS1 LbA_WoS2 LbA_WoS3 LbA_WoT2 LbA_WoPm LbA_WoU LbA_WoG LbA_WoS4 LbA_WoS5 LbA_WoEnd.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoTop.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis MVA : st_mva_stmt H.
  Hypothesis DTOR : st_dtor_stmt H.
  Hypothesis PM : parse_module_stmtA H LINV_P5.
  Let HB := rt_bp_base H HHb.

  Lemma wp3_nodup : forall (e : went H) ff fp s LB b c d ms, wp3_post H e ff fp s LB b c d ms -> List.NoDup (map blk_id LB).
  Proof.
    intros e ff fp s LB b c d ms P. destruct P as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & _ & HI & _).
    exact (ah_nodup H HB _ _ _ (winv_rh H _ _ _ _ _ _ _ HI)).
  Qed.

  Theorem parse_entry_okA : forall apo : bool, po_stmt_at H LINV_P5 (if apo then APO_ENTRY else AWO_ENTRY) (negb apo).
  Proof.
    intros apo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo
      s LB LF CH ctx env words n lo B shi errv VIS FZ Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 HA7 CTX HN WRD RH KR BS BC BL RA SPB B64 SP16 ST CE LO
      ER MI TP RAE LV AC RF LFL S0 SSHI CHN PF CHU PTR PCOST.
    set (e := WEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF CH ctx env words n lo B shi).
    assert (HP : wpre H e).
    { unfold wpre. cbn [w_m w_n w_LB w_sp w_fc w_ctx w_env w_words w_s w_B w_lo w_tp w_ra w_LF w_shi w_s0 w_CH wSP e].
      split; [exact FZ|]. split; [exact CTX|]. split; [exact HN|]. split; [exact WRD|]. split; [exact RH|].
      split; [exact BS|]. split; [exact BC|]. split; [exact BL|]. split; [exact RA|]. split; [exact SPB|]. split; [exact B64|].
      split; [exact SP16|]. split; [exact ST|]. split; [exact CE|]. split; [exact LO|]. split; [exists errv; exact ER|].
      split; [exact MI|]. split; [exact TP|]. split; [exact RAE|]. split; [exact LV|]. split; [exact AC|]. split; [exact RF|].
      split; [exact LFL|]. split; [exact S0|]. split; [exact SSHI|]. split; [exact CHN|]. split; [exact PF|]. split; [exact CHU | exact PCOST]. }
    change (as_SR H (wpost H e) (mkCfg msF mo)).

    eapply (ahh_evt_then H HB (e0_post H e) _ s msF _ mo); [exact KR | exact VIS | |].
    { eapply evt_cut; [| intros ms P; exact (e0b H HHb e ms HP P)].
      exact (e0a H HHb e apo t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP ltac:(intros E; apply HA7; rewrite E; reflexivity)
               Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6). }
    intros msF0 mo0 KR0 MP0 P0.

    eapply (seg_on1 H HHb _ e msF0 mo0 HP KR0 MP0 P0).
    intros ff fp msF1 mo1 q1 p1 b1 KR1 MP1 AL1 NI1 P1.
    eapply (seg_on2 H HHb _ e ff fp msF1 mo1 q1 p1 b1 HP KR1 MP1 AL1 NI1 P1).
    intros msF2 mo2 q2 p2 b2 KR2 MP2 AL2 NI2 P2.
    eapply (seg_on3 H HHb _ e ff fp msF2 mo2 q2 p1 p2 b1 b2 HP KR2 MP2 AL2 NI1 NI2 P2).
    intros msF3 mo3 q3 p3 b3 KR3 MP3 AL3 NI3 P3.

    eapply (seg_on4 H HHb _ e ff fp msF3 mo3 q3 p1 p2 p3 b1 b2 b3 HP KR3 MP3 AL3 (wp3_nodup e ff fp q3 _ b1 b2 b3 _ P3) P3).
    intros msF4 mo4 q4 p4 g KR4 MP4 AL4 ND4 P4.
    eapply (seg_on5 H HHb _ e ff fp msF4 mo4 q4 p1 p2 p3 p4 b1 b2 b3 g HP KR4 MP4 AL4 ND4 P4).
    intros msF5 mo5 q5 p5 h KR5 MP5 AL5 ND5 P5.
    eapply (seg_on6 H HHb _ e ff fp msF5 mo5 q5 p1 p2 p3 p4 p5 b1 b2 b3 g h HP KR5 MP5 AL5 ND5 P5).
    intros msF6 mo6 q6 p6 k KR6 MP6 AL6 ND6 P6.

    eapply (seg_mva1 H HHb HOWN MVA PTR _ e ff fp msF6 mo6 q6 p1 p2 p3 p4 p5 p6 b1 b2 b3 g h k HP KR6 MP6 AL6 P6).
    intros msF7 mo7 q7 LB7 XS7 KR7 MP7 AL7 PERM7 P7.
    eapply (seg_dt1 H HHb HOWN DTOR PTR _ e ff fp msF7 mo7 q7 LB7 XS7 p4 p5 p6 g h k HP KR7 MP7 AL7 PERM7 P7).
    intros msF8 mo8 q8 LB8 XS8 KR8 MP8 AL8 PERM8 P8.
    eapply (seg_pm1 H HHb HOWN PM PTR _ e ff fp msF8 mo8 q8 LB8 XS8 p4 p5 p6 g h k HP KR8 MP8 AL8 PERM8 P8).
    intros msF10 mo10 q10 LB10 LBs XS10 c' KR10 MP10 AL10 P10.

    eapply (seg_on7 H HHb _ e ff fp msF10 mo10 q10 LB10 LBs XS10 c' k HP KR10 MP10 AL10 P10).
    intros msF11 mo11 q11 p7 u F' fc' r KR11 MP11 AL11 PF11 NI7 FZ' P11.
    eapply (seg_on8 H HHb _ e ff fp msF11 mo11 q11 LB10 LBs XS10 c' p7 k r u F' fc' HP KR11 MP11 AL11 PF11 NI7 P11).
    intros msF12 mo12 q12 p8 v KR12 MP12 AL12 NI8 P12.
    eapply (seg_on9 H HHb _ e ff fp msF12 mo12 q12 LB10 LBs XS10 c' p7 p8 r u v F' fc' HP KR12 MP12 AL12 PF11 NI7 NI8 P12).
    intros msF13 mo13 q13 p9 w KR13 MP13 AL13 NI9 P13.

    eapply (seg_mva2 H HHb HOWN MVA PTR _ e ff fp msF13 mo13 q13 LB10 LBs XS10 c' p7 p8 p9 r u v w F' fc' HP KR13 MP13 AL13 PF11 NI7 NI8 NI9 FZ' P13).
    intros msF14 mo14 q14 LB14 XS14 KR14 MP14 AL14 PERM14 P14.
    eapply (seg_dt2 H HHb HOWN DTOR PTR _ e ff fp msF14 mo14 q14 LB14 XS14 p7 p8 p9 r u v w HP KR14 MP14 AL14 PERM14 P14).
    intros msF15 mo15 q15 LB15 XS15 KR15 MP15 AL15 PERM15 P15.
    eapply (seg_dt3 H HHb HOWN DTOR PTR _ e ff fp msF15 mo15 q15 LB15 XS15 p7 p8 p9 r u v w HP KR15 MP15 AL15 PERM15 P15).
    intros msF16 mo16 q16 LB16 XS16 KR16 MP16 AL16 PERM16 P16.

    exact (seg_end H HHb e ff fp msF16 mo16 q16 LB16 XS16 r w HP KR16 MP16 AL16 PERM16 P16).
  Qed.

  Theorem binary_parse_okA : binary_parse_stmtA H LINV_P5.
  Proof. exact (parse_entry_okA true). Qed.
End WoTop.
