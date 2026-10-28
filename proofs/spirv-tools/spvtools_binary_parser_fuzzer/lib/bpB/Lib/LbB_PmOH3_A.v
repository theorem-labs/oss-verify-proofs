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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLeaf LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmOHK.

Section OH3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_oh3_A : forall (w : pmwA H) s LB LBs m mo c msF R F fc (io op t x0 : Z) (Q : config -> Prop),
    pmw_okA H w ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R ->
    PMXA H LINV w s LB LBs m mo c S_OPER TBL_EEF44 [] -> regs_tbl w R RT_EF07Cc ->
    PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= x0 < 2 ^ 32 -> PropExec.getr R 10%bv = Z_to_bv 64 (sx32A x0) -> PropExec.getr R 11%bv = Z_to_bv 64 (c_endian c) ->
    PropExec.getr R 18%bv = Z_to_bv 64 t -> PropExec.getr R 22%bv = Z_to_bv 64 op -> PropExec.getr R 25%bv = Z_to_bv 64 io ->
    c_endian c = 0 \/ c_endian c = 1 -> 1 <= t <= 107 ->
    (forall msF1 mo1 m1 R1 (word : Z), as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf1494) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_ARM ->
       PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (t - 1) -> 0 <= word < 2 ^ 32 ->
       PropExec.getr R1 18%bv = Z_to_bv 64 t -> PropExec.getr R1 21%bv = Z_to_bv 64 (sx32A word) ->
       PropExec.getr R1 22%bv = Z_to_bv 64 op -> PropExec.getr R1 25%bv = Z_to_bv 64 io ->
       rw_cells asegs m1 (wa_ff w + 176) [C4 (Z_to_bv 64 word)] -> ffkeepX w [(176, 4)] m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame HTL.
    intros w s LB LBs m mo c msF R F fc io op t x0 Q OK KR0 VIS0 RF0 X0 HT0 G3_0 G4_0 Hx0 E10_0 E11_0
           T18_0 O22_0 I25_0 Hend Ht K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (x0, c_endian c) w s LB LBs m mo c
              S_OPER TBL_EEF44 [] [] 0 msF R F fc 0xf1478 Q);
      [ exact OK | exact X0 | exact KR0 | exact VIS0 | exact RF0 | rtf HT0 | rtf HT0 | reflexivity | lia | lia | reflexivity
      | cbn beta iota; split; [exact Hx0|]; split; [exact E10_0|]; split; [destruct Hend as [-> | ->]; lia | exact E11_0]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 KP1 MU1 WM1 (wv & Hwv & E10_1).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (transitivity (PropExec.getr R 3%bv); [apply KP1; cbn; tauto | exact G3_0]).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (transitivity (PropExec.getr R 4%bv); [apply KP1; cbn; tauto | exact G4_0]).
    assert (T18_1 : PropExec.getr R1 18%bv = Z_to_bv 64 t) by (transitivity (PropExec.getr R 18%bv); [apply KP1; cbn; tauto | exact T18_0]).
    assert (O22_1 : PropExec.getr R1 22%bv = Z_to_bv 64 op) by (transitivity (PropExec.getr R 22%bv); [apply KP1; cbn; tauto | exact O22_0]).
    assert (I25_1 : PropExec.getr R1 25%bv = Z_to_bv 64 io) by (transitivity (PropExec.getr R 25%bv); [apply KP1; cbn; tauto | exact I25_0]).
    assert (E18 : edenot (Eseed R1 (wenv_vals w ++ [])) (EAlu ALU_ADD (EVar 18) (ELit (-1))) = Z_to_bv 64 (t - 1))
      by exact (ev_add (Eseed R1 (wenv_vals w ++ [])) 18 t (-1) T18_1 ltac:(lia) ltac:(lia)).
    assert (FK1 : ffkeepX w [] m m1).
    { apply (ffkeepX_munch w [] _ m m1 MU1 WM1). apply Forall_cons; [left; cbn [fst]; lia | apply Forall_nil]. }
    pose proof (regs_keep w [] R R1 RT_EF07Cc HT0 KP1) as HT1.
    pm_go HHm LINV_frame OK X1 KR1 VIS1 RF1 HT1 (@nil word) (@nil kentry) 100%nat [0xf1494] [true] 41%N
          S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_ARM.
    { split_scs. cbn [sc_denot]. rewrite E18. change (edenot _ (ELit 106)) with (Z_to_bv 64 106).
      rewrite br_geu by lia. apply Bool.negb_true_iff, Z.ltb_ge. lia. }
    intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HTx2 HR2 Hlf2.
    lazymatch type of X2 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M2 := mm) in * end.
    replace (s_pc SSr) with 0xf1494 in VIS2 by reflexivity.
    pose proof (ev_ff H w _ OK (env_world_seed H w R1 [])) as TEF. change (EVar WV_FF) with (EVar 33%N) in TEF.
    assert (FK2 : ffkeepX w [(176, 4)] m1 M2).
    { pose proof (munch_sym (Eseed R1 (wenv_vals w ++ [])) m1 (s_log SSr) [(EVar 33, 176, 180)] Hlf2
                    ltac:(vm_compute; reflexivity)) as TMU.
      cbn [num_wins map] in TMU. rewrite TEF in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (C176 : rw_cells asegs M2 (wa_ff w + 176) [C4 (Z_to_bv 64 wv)]).
    { eapply (rw_cells_log_nth_sb (Eseed R1 (wenv_vals w ++ [])) m1 (s_log SSr) 0 (EVar 33) 176 4 (EVar 10)
                (wa_ff w + 176) (C4 (Z_to_bv 64 wv)) Hlf2);
        [ reflexivity | reflexivity | rewrite TEF; reflexivity
        | eapply wr_at_sub; [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) | lia | change (fsz PM_FCLASS) with 16384; lia | lia]
        | reflexivity | exact I | rewrite (w2lb4_sx32A wv Hwv); f_equal; exact (eq_sym E10_1) ]. }
    eapply (K msF2 mo2 M2 R2 wv KR2 VIS2 RF2 X2 HTx2).
    - rewrite (HR2 3%bv). exact G3_1.
    - rewrite (HR2 4%bv). exact G4_1.
    - rewrite (HR2 10%bv). exact E18.
    - exact Hwv.
    - rewrite (HR2 18%bv). exact T18_1.
    - rewrite (HR2 21%bv). exact E10_1.
    - rewrite (HR2 22%bv). exact O22_1.
    - rewrite (HR2 25%bv). exact I25_1.
    - exact C176.
    - exact (ffkeepX_trans w [] [(176, 4)] [(176, 4)] m m1 M2 FK1 FK2 (incl_nil_l _) (incl_refl _)).
  Qed.
End OH3.
