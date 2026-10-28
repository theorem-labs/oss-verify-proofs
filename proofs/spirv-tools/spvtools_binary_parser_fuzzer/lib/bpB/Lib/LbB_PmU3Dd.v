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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmPD.

Definition RT_PM_U3_DFD_1 : list (reg * expr) := [(1%bv, ELit 994516); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_DFD_3 : list (reg * expr) := [(1%bv, ELit 994536); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (11%bv, ELit 150720); (12%bv, ELit 40); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_DFD_5 : list (reg * expr) := [(1%bv, ELit 994548); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_DFD_7 : list (reg * expr) := [(1%bv, ELit 994560); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 8576)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_DFD_9 : list (reg * expr) := [(1%bv, ELit 994560); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac lit_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac lit_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Section U3Dd.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HINT : put_int_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u3_dfd : forall (w : pmwA H) s LB LBs m mo c msF R F fc (t : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2bf8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    pm_bud (wa_n w) c ->
    PropExec.getr R 18%bv = Z_to_bv 64 t ->
    0 <= t < 2 ^ 31 ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc t Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD T18_0 Ht K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 200%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 38; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_DFD_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    replace (s_pc SSr) with APDIAG in VIS1 by reflexivity.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (T18_1 : PropExec.getr R1 18%bv = Z_to_bv 64 t) by (rewrite (HR1 18%bv); exact T18_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 38; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 8576 _ (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | first [reflexivity | cbn; reflexivity]
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    assert (T18_2 : PropExec.getr R2 18%bv = Z_to_bv 64 t) by (transitivity (PropExec.getr R1 18%bv); [apply KEEP2; cbn; tauto | exact T18_1]).
    subst TB2.
    pose proof (regs_keep w _ R1 R2 RT_PM_U3_DFD_1 HTx1 KEEP2) as HT2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word)
          (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 38; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_DFD_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    replace (s_pc SSr0) with APUT_CSEQ in VIS3 by reflexivity.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    assert (T18_3 : PropExec.getr R3 18%bv = Z_to_bv 64 t) by (rewrite (HR3 18%bv); exact T18_2).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 38; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] 0 msF3 R3 F2 fc2 8576 _ _ _ (-4) (0) Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc
      | lit_bytes
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ [] 0 _ _ 8576 (-4) (0) OK X2 (env_world_seed H w R2 []) Hlf3);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS2]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    assert (T18_4 : PropExec.getr R4 18%bv = Z_to_bv 64 t) by (transitivity (PropExec.getr R3 18%bv); [apply KEEP4; cbn; tauto | exact T18_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_U3_DFD_3 HTx3 KEEP4) as HT4.
    pm_go HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word)
          (@nil kentry) 100%nat [APUT_INT] (@nil bool) 41%N
          [3; 4; 38; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_DFD_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    replace (s_pc SSr1) with APUT_INT in VIS5 by reflexivity.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    assert (G11_5 : PropExec.getr R5 11%bv = Z_to_bv 64 (t mod 2 ^ 64)).
    { rewrite (HR5 11%bv). rewrite Z.mod_small by lia. exact T18_4. }
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_INT 0 (2 ^ 31) (fun x => x mod 2 ^ 64) HINT w s4 LB4 LBs M5 mo5 c
              [3; 4; 38; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB4 _ msF5 R5 F4 fc4 8576 _ t (-4) (0 + 40) Q);
      [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5 | exact FZ4
      | rtf HTx5 | reflexivity | lia | rtf HTx5 | rtf HTx5 | exact G4_5 | rtf HTx5 | exact G11_5 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ TB4 _ _ _ 8576 (-4) (0 + 40) OK X4 (env_world_seed H w R4 []) Hlf5);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS4]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF6 mo6 R6 F6 fc6 s6 LB6 m6 TB6 KR6 VIS6 RF6 FZ6 X6 KEEP6 (DS6 & HR10_6) FR6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_keep w _ R5 R6 RT_PM_U3_DFD_5 HTx5 KEEP6) as HT6.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS6) as ERR6.
    assert (HK6 : know_ok asegs (Eseed R6 (wenv_vals w ++ [])) m6 [KWord (SA (EVar WV_FF) 8936) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R6 (wenv_vals w ++ [])) OK (env_world_seed H w R6 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m6 (wa_ff w + 8576 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR6 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word)
          [KWord (SA (EVar WV_FF) 8936) 4 (ELit 4294967292)] HK6 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 38; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_DFD_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    replace (s_pc SSr2) with ADS_DTOR in VIS7 by reflexivity.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s6 LB6 LBs M7 mo7 c
              [3; 4; 38; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB6 _ msF7 R7 F6 fc6 8576 _ (-4) (0 + 40 + 24) Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact FZ6
      | rtf HTx7 | reflexivity | lia | rtf HTx7 | rtf HTx7 | exact G4_7 | rtf HTx7
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s6 LB6 LBs m6 mo6 c _ _ _ _ _ _ _ 8576 (-4) (0 + 40 + 24) OK X6 (env_world_seed H w R6 []) Hlf7);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS6]
      | cbn; tauto
      | ].
    intros msF8 mo8 R8 F8 fc8 s8 LB8 m8 TB8 KR8 VIS8 RF8 FZ8 X8 KEEP8 (TB8e & ADDR8) FR8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    subst TB8.
    pose proof (regs_keep w _ R7 R8 RT_PM_U3_DFD_7 HTx7 KEEP8) as HT8.
    pm_go HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          (@nil kentry) 400%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_DFD_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    replace (s_pc SSr3) with OL_CHECK in VIS9 by reflexivity.
    eapply (K s8 LB8 LBs M9 mo9 c msF9 R9 F8 fc8 TBL_EEF44 _ 4294967292);
      [ exact X9 | apply incl_refl | exact Htr | exact BUD | exact Hbsz | exact KR9 | exact VIS9 | exact RF9
      | exact FZ8 | exact (regs_tbl_sub w [] R9 RT_PM_U3_DFD_9 RT_CHECK HTx9 ltac:(vm_compute; reflexivity))
      | rewrite (HR9 3%bv); exact G3_8 | rewrite (HR9 4%bv); exact G4_8 | rtf HTx9 | lia ].
  Qed.

End U3Dd.
