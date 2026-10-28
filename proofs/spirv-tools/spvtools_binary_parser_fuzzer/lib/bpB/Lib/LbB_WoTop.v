(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_Own LbB_RtOwn LbB_DStat LbB_HKit LbB_HStKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit2 LbB_WoKit3 LbB_WoSt LbB_WoSt2 LbB_WoMs LbB_WoCall LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoE0 LbB_WoE0b LbB_WoS1 LbB_WoS2 LbB_WoS3 LbB_WoBP LbB_WoPm LbB_WoU LbB_WoS4 LbB_WoS5 LbB_WoEnd.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PiStmt LbB_HdrGet LbB_DiagStmt.
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
  Hypothesis PI : parse_inst_stmtB H LINV_P5.
  Hypothesis HG : hdr_get_stmt.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV_P5 ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA.
  Let HB := rt_bp_base H HHb.

  Theorem parse_entry_okA : forall apo : bool, po_stmt_at H LINV_P5 (if apo then APO_ENTRY else AWO_ENTRY) (negb apo).
  Proof using HHb HOWN MVA DTOR PI HG ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64.
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

    eapply (seg_on13 H HHb HOWN PTR _ e msF0 mo0 (w_mo e) HP KR0 MP0 P0).
    intros ff fp msF3 mo3 q3 XS3 p1 p2 p3 b1 b2 b3 LB3 KR3 MP3 AL3 ND3 P3.
    eapply (seg_on46 H HHb HOWN PTR _ e ff fp msF3 mo3 (w_mo e) q3 XS3 p1 p2 p3 b1 b2 b3 HP KR3 MP3 AL3 ND3 P3).
    intros msF6 mo6 q6 XS6 p4 p5 p6 g h k LB6 KR6 MP6 AL6 ND6 P6.
    eapply (seg_mva1 H HHb HOWN MVA DTOR PTR _ e ff fp msF6 mo6 (w_mo e) q6 XS6 p1 p2 p3 p4 p5 p6 b1 b2 b3 g h k HP KR6 MP6 AL6 ND6 P6).
    intros msF7 mo7 q7 LB7 XS7 KR7 MP7 AL7 PERM7 P7.
    eapply (seg_dt1 H HHb HOWN MVA DTOR PTR _ e ff fp msF7 mo7 (w_mo e) q7 LB7 XS7 p4 p5 p6 g h k HP KR7 MP7 AL7 PERM7 P7).
    apply (wpm_bp H HHb PI (proj1 PTR) HG ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64 e ff fp _ (w_mo e)).
    assert (TRS : forall r, In r RESV_DEL_RAS -> trace_ok (as_TR H) APC0_FREE [r]).
    { intros r Hr. destruct PTR as [_ W]. rewrite Forall_forall in W. apply W.
      apply in_app_iff. right. apply in_app_iff. right. exact Hr. }
    assert (TRO : trace_ok (as_TR H) APC0_FREE [LbB_ResvB.RESV_OPND_DEL_RA])
      by (apply TRS; unfold RESV_DEL_RAS; cbn [In]; left; reflexivity).
    assert (TRW : trace_ok (as_TR H) APC0_FREE [LbB_ResvB.rv_del_ra LbB_ResvB.RESV_W32])
      by (apply TRS; unfold RESV_DEL_RAS; cbn [In]; right; left; reflexivity).
    assert (TRT : trace_ok (as_TR H) APC0_FREE [LbB_ResvB.rv_del_ra LbB_ResvB.RESV_TYP])
      by (apply TRS; unfold RESV_DEL_RAS; cbn [In]; right; right; left; reflexivity).

    refine (wu_top H HHb (wpost H e) e ff fp (w_mo e) _).
    intros msU moU sU LBU LBsU XSU mU cPU rU u5 u6 u7 u12 u13 u14 u15 u16 u17 u10 u11 u28 u29 u30 u31 FU fcU
      KRU MPU ALU AL0U FZU WU TSU LSU LCU LLU RRU VISU.
    refine (seg_on7 H HHb TRO (wpost H e) e ff fp XSU sU LBU LBsU [] mU msU moU cPU u5 u6 u7 u12 u13 u14 u15 u16 u17
              (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3504))
              (Z_to_bv 64 rU) u10 u11 u28 u29 u30 u31 FU fcU HP WU TSU LSU LCU LLU KRU AL0U VISU _).
    intros msA moA sA pA bA mA v5 v6 v7 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 KRA MPA ALA WA TSA BA NIA VISA.
    refine (seg_on8 H HHb TRW (wpost H e) e ff fp XSU sA ((pA, bA, 500) :: LBU) LBsU [(pA, bA, 500)] mA msA moA cPU pA bA
              v5 v6 v7 v12 v13 v14 v15 v16 v17
              (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3504))
              (Z_to_bv 64 rU) u10 u11 v28 v29 v30 v31 FU fcU HP WA TSA (or_introl eq_refl) BA
              ltac:(rewrite lb_small_wcons by lia; lia) ltac:(cbn [length]; lia) ltac:(rewrite nlarge_wcons by lia; exact LLU)
              KRA ltac:(lia) VISA _).
    intros msB moB sB pB bB mB w5 w6 w7 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 KRB MPB ALB WB TSB B7B BB NIB VISB.
    refine (seg_on9 H HHb TRT (wpost H e) e ff fp XSU sB ((pB, bB, 100) :: (pA, bA, 500) :: LBU) LBsU [(pB, bB, 100); (pA, bA, 500)]
              mB msB moB cPU pA pB bA bB w5 w6 w7 w12 w13 w14 w15 w16 w17
              (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 rU) u10 u11 w28 w29 w30 w31 FU fcU
              HP WB TSB (or_intror (or_introl eq_refl)) B7B (or_introl eq_refl) BB
              ltac:(rewrite !lb_small_wcons by lia; lia) ltac:(cbn [length]; lia) ltac:(rewrite !nlarge_wcons by lia; exact LLU)
              KRB ltac:(lia) VISB _).
    intros msC moC sC pC bC mC z5 z6 z7 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 KRC MPC ALC WC TSC B7C B8C B9C NIC VISC.
    refine (seg_mva2 H HHb HOWN MVA PTR (wpost H e) e ff fp XSU sC ((pC, bC, 100) :: (pB, bB, 100) :: (pA, bA, 500) :: LBU) LBsU
              mC msC moC cPU pA pB pC bA bB bC z5 z6 z7 z12 z13 z14 z15 z16 z17
              (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 rU) (Z_to_bv 64 (ff + 3272)) u10 u11
              z28 z29 z30 z31 FU fcU HP WC TSC B7C B8C B9C FZU KRC ltac:(lia) VISC _).
    intros msD moD sD LBD mD XSD d5 d6 d7 d11 d12 d13 d14 d15 d16 d17 d28 d29 d30 d31 FD fcD KRD MPD ALD FZD WD RPD ADD VISD.
    refine (seg_dt2 H HHb HOWN DTOR PTR (wpost H e) e ff fp XSD sD LBD [(pC, bC, 100); (pB, bB, 100); (pA, bA, 500)] mD msD moD
              (mkfreshA 0 0 bA bB bC) (state_emptied (mkfreshA 0 0 bA bB bC)) d5 d6 d7 d11 d12 d13 d14 d15 d16 d17
              (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 rU) (Z_to_bv 64 (ff + 3272)) u10 u11
              d28 d29 d30 d31 FD fcD HP WD RPD (state_sh_emptied mD _) ltac:(reflexivity) ADD FZD KRD ltac:(lia) VISD _).
    intros msE moE sE LBE mE XSE f5 f6 f7 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 FE fcE KRE MPE ALE FZE WE VISE.
    refine (seg_dt3 H HHb HOWN DTOR PTR (wpost H e) e ff fp XSE sE LBE [(pC, bC, 100); (pB, bB, 100); (pA, bA, 500)] mE msE moE
              (mkfreshA 0 0 bA bB bC) f5 f6 f7 f11 f12 f13 f14 f15 f16 f17
              (Z_to_bv 64 (-8)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3504))
              (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 rU) (Z_to_bv 64 (ff + 3272)) u10 u11 f28 f29 f30 f31 FE fcE
              HP WE FZE KRE ltac:(lia) VISE _).
    intros msG moG sG LBG mG XSG g5 g6 g7 g10 g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 FG fcG KRG MPG ALG FZG WG VISG.
    exact (seg_end H HHb e ff fp msG moG sG LBG XSG mG rU g5 g6 g7 g10 g11 g12 g13 g14 g15 g16 g17
             (Z_to_bv 64 (-8)) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 (ff + 3272))
             u10 u11 g28 g29 g30 g31 FG fcG HP KRG
             (ah_mpres_trans H HB _ _ _ (ah_mpres_trans H HB _ _ _ (ah_mpres_trans H HB _ _ _ (ah_mpres_trans H HB _ _ _
                (ah_mpres_trans H HB _ _ _ (ah_mpres_trans H HB _ _ _ MPU MPA) MPB) MPC) MPD) MPE) MPG)
             ltac:(lia) FZG WG RRU VISG).
  Qed.

  Theorem binary_parse_okA : binary_parse_stmtA H LINV_P5.
  Proof. exact (parse_entry_okA true). Qed.
End WoTop.
