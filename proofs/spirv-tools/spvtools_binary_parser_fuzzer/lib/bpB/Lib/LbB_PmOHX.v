(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RtOwn LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmWords LbB_PmCells LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmOL LbB_PmWKit LbB_PmWEx LbB_PmOHK LbB_PmOHX2.

Definition RT_PM_OHX_1 : list (reg * expr) :=
  [(1%bv, ELit 0xf12d8); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EVar 32);
   (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880));
   (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984));
   (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section OHX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HEXH : exhausted_stmtA H LINV.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_ohx : forall (w : pmwA H) s LB LBs m mo c msF R F fc (io iwc op t : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf136c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EEFB0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 t ->
    0 <= t < 2 ^ 31 ->
    0 <= io <= c_widx c ->
    0 <= iwc < 2 ^ 16 ->
    c_widx c < io + iwc ->
    0 <= op < 2 ^ 16 ->
    wa_n w <= c_widx c ->
    pm_bud (wa_n w) c ->
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] ->
    rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 op)] ->
    CHECKKA H LINV w Q ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame HEXH.
    intros w s LB LBs m mo c msF R F fc io iwc op t Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HT10 Ht Hio Hiwc HLT2 Hop HGE Hbud CIO COP K.
    pose proof (pm_geom H w OK) as G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)])) m [KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 43); KWord (SA (EVar WV_FF) 10112) 8 (EVar 41); KWord (SA (EVar WV_FF) 9050) 2 (EVar 42); KRange (EVar 10) 0 2147483647]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)])) OK (env_world_seed H w R [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)])) as EF.
      apply Forall_cons; [| idtac].
      { pmk_entry H HHm w OK X0 (env_world_seed H w R [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)]). }
      apply Forall_cons; [| idtac].
      { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 10112) _ 0%nat (C8 (Z_to_bv 64 io))); [exact CIO | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity]. }
      apply Forall_cons; [| idtac].
      { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9050) _ 0%nat (C2 (Z_to_bv 64 op))); [exact COP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity]. }
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot _ (EVar 10)) with (PropExec.getr R 10%bv). rewrite HT10, u_lit64a, Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)]
          [KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 43); KWord (SA (EVar WV_FF) 10112) 8 (EVar 41); KWord (SA (EVar WV_FF) 9050) 2 (EVar 42); KRange (EVar 10) 0 2147483647] HK1 300%nat [AEXHAUSTED] [true] 44%N
          (OB_PARSED_OPERAND :: S_INSTR) (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_OHX_1.
    { pose proof (pmw_bounds H w OK) as BND. split_scs; first [ pm_br H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)])) (env_world_seed H w R [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 (c_widx c)]) | match goal with |- ?g => idtac "SCLEFT" g end ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_OHX_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (pmw_bounds H w OK) as BNDc.
    eapply (pm_exhausted H HHbp LINV HEXH w _ _ _ _ _ _ _ TBL_EEF44 [] 0 msF1 R1 F fc 0xf12d8 io op t _ OK X1 eq_refl eq_refl KR1 VIS1 RF1 FZ0);
      [ rtf HT1 | reflexivity | lia | rtf HT1 | rtf HT1 | exact G4_1 | rtf HT1
      | (rewrite (HR1 _); cbn [sr_get s_regs nth]; cbn [edenot]; ev_xs; reflexivity)
      | (rewrite (HR1 _); cbn [sr_get s_regs nth]; apply (edenot_zext16 _ 42 op); [reflexivity | lia])
      | (rewrite (HR1 _); cbn [sr_get s_regs nth]; change (edenot _ (EVar 10)) with (PropExec.getr R 10%bv); exact HT10)
      | lia | lia | lia | unfold PM_RESERVE; lia | unfold PM_PF, PM_DTOR_RAS, PM_EXH_RAS; cbn [map app]; inlist | ].
    intros msFx mox mx Rx Fx fcx stx LBx KRx VISx RFx FZx Xx KEEPx G10x FFKx.
    eapply (pm_ohx2 H HHbp LINV LINV_frame w stx LBx LBs mx mox c msFx Rx Fx fcx (0 + 2 ^ 20) Q OK Xx Htr Hbud Hbsz KRx VISx RFx FZx);
      [ apply (regs_tbl_sub w [] Rx (rt_keepK KEPT_REGS RT_PM_OHX_1) RT_CHECK); [exact (regs_keepK w [] R1 Rx _ KEPT_REGS HT1 KEEPx) | vm_compute; reflexivity]
      | rewrite (KEEPx 3%bv ltac:(inb)); exact G3_1 | rewrite (KEEPx 4%bv ltac:(inb)); exact G4_1 | exact G10x | exact K ].
  Qed.

End OHX.
