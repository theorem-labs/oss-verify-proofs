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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_HFind.

Definition RT_PM_U6_D0_1 : list (reg * expr) := [(1%bv, ELit 996544); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551606); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_D0_3 : list (reg * expr) := [(1%bv, ELit 996564); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (11%bv, ELit 149312); (12%bv, ELit 21); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_D0_5 : list (reg * expr) := [(1%bv, ELit 996576); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, ELit 18446744073709551606); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_D0_7 : list (reg * expr) := [(1%bv, ELit 996576); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 656)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551606); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_DD_1 : list (reg * expr) := [(1%bv, ELit 993348); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551606); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_DD_3 : list (reg * expr) := [(1%bv, ELit 993368); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (11%bv, ELit 149376); (12%bv, ELit 3); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_DD_5 : list (reg * expr) := [(1%bv, ELit 993380); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_DD_7 : list (reg * expr) := [(1%bv, ELit 993400); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (11%bv, ELit 149408); (12%bv, ELit 26); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_DD_9 : list (reg * expr) := [(1%bv, ELit 993412); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, ELit 18446744073709551606); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_DD_11 : list (reg * expr) := [(1%bv, ELit 993412); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 1120)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551606); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac u6d_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac u6d_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Ltac u6d_pc VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.

Section U6d.
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
  Hypothesis HPDIAGE : pdiagE_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTLbAPmU6d_0 : list (Z * expr) := TBL_EEF44.
  Lemma pm_u6_d0 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2744) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    pm_bud (wa_n w) c ->
    PropExec.getr R 21%bv = Z_to_bv 64 0 ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using DSL HCSEQ HDTOR HHbp HPDIAGE LINV_frame.
    intros w s LB LBs m mo c msF R F fc Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD H21 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) (@nil kentry) 200%nat [APDIAG_E] [true] 41%N
          [3; 4; 6; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_D0_1.
    { split_scs. cbn [sc_denot].
      change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 21)) with (PropExec.getr R 21%bv).
      rewrite H21. first [ reflexivity | vm_compute; reflexivity ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    u6d_pc VIS1 APDIAG_E.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG_E true HPDIAGE w s LB LBs M1 mo1 c
              [3; 4; 6; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 656 _ (-10) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2. subst TB2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    pose proof (regs_keep w _ R1 R2 RT_PM_U6_D0_1 HTx1 KEEP2) as HT2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 6; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_D0_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    u6d_pc VIS3 APUT_CSEQ.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 6; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] 0 msF3 R3 F2 fc2 656 _ _ _ (-10) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u6d_acc
      | u6d_bytes
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ [] 0 _ _ 656 (-10) 0 OK X2 (env_world_seed H w R2 []) Hlf3);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS2]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_U6_D0_3 HTx3 KEEP4) as HT4.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS4) as ERR4.
    assert (HK4 : know_ok asegs (Eseed R4 (wenv_vals w ++ [])) m4 [KWord (SA (EVar WV_FF) 1016) 4 (ELit 4294967286)]).
    { pose proof (ev_ff H w (Eseed R4 (wenv_vals w ++ [])) OK (env_world_seed H w R4 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 656 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-10) mod 2 ^ 32))));
        [exact ERR4 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word)
          [KWord (SA (EVar WV_FF) 1016) 4 (ELit 4294967286)] HK4 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 6; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_D0_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    u6d_pc VIS5 ADS_DTOR.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s4 LB4 LBs M5 mo5 c
              [3; 4; 6; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB4 _ msF5 R5 F4 fc4 656 _ (-10) (0 + 21) Q);
      [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5 | exact FZ4
      | rtf HTx5 | reflexivity | lia | rtf HTx5 | rtf HTx5 | exact G4_5 | rtf HTx5
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 656 (-10) (0 + 21) OK X4 (env_world_seed H w R4 []) Hlf5);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS4]
      | cbn; tauto
      | ].
    intros msF6 mo6 R6 F6 fc6 s6 LB6 m6 TB6 KR6 VIS6 RF6 FZ6 X6 KEEP6 (TB6e & ADDR6) FR6. subst TB6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_keep w _ R5 R6 RT_PM_U6_D0_5 HTx5 KEEP6) as HT6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) 200%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_D0_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    u6d_pc VIS7 OL_CHECK.
    eapply (K s6 LB6 LBs M7 mo7 c msF7 R7 F6 fc6 TBL_EEF44 _ (2 ^ 32 - 10));
      [ exact X7 | intros ? h; exact h | exact Htr | exact BUD | exact Hbsz | exact KR7 | exact VIS7 | exact RF7
      | exact FZ6 | exact (regs_tbl_sub w [] R7 RT_PM_U6_D0_7 RT_CHECK HTx7 ltac:(vm_compute; reflexivity))
      | rewrite (HR7 3%bv); exact G3_6 | rewrite (HR7 4%bv); exact G4_6 | rtf HTx7 | lia ].
  Qed.

  Lemma pm_u6_dd : forall (w : pmwA H) s LB LBs m mo c msF R F fc (q wv : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2760) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    pm_bud (wa_n w) c ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_ff w + 9060) ->
    PropExec.getr R 10%bv = Z_to_bv 64 q ->
    16 <= q /\ q + 24 <= 2 ^ 47 ->
    rw_cells asegs m (wa_ff w + 9060) [C4 (Z_to_bv 64 wv)] ->
    0 <= wv < 2 ^ 32 ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using DSL HCSEQ HDTOR HHbp HPDIAGE HU32 LINV_frame.
    intros w s LB LBs m mo c msF R F fc q wv Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD G21_0 HR10 HQ HWV HWVR K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HT0' : regs_tbl w R (RT_ARM ++ [(21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060))])).
    { apply regs_tbl_app; [exact HT0|]. apply Forall_cons; [| apply Forall_nil].
      cbn [fst snd]. rewrite G21_0. symmetry. eapply ev_add; [reflexivity | lia | lia]. }
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [])) m [KRange (EVar 10) 16 (2 ^ 47)]).
    { apply Forall_cons; [| apply Forall_nil].
      cbn [kentry_ok].
      change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 10)) with (PropExec.getr R 10%bv).
      rewrite HR10, Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.mod_small by lia. lia. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0' (@nil word)
          [KRange (EVar 10) 16 (2 ^ 47)] HK1 200%nat [APDIAG_E] (@nil bool) 41%N
          [3; 4; 7; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_DD_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    u6d_pc VIS1 APDIAG_E.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG_E true HPDIAGE w s LB LBs M1 mo1 c
              [3; 4; 7; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 1120 _ (-10) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2. subst TB2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    pose proof (regs_keep w _ R1 R2 RT_PM_U6_DD_1 HTx1 KEEP2) as HT2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 7; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_DD_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    u6d_pc VIS3 APUT_CSEQ.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 7; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] 0 msF3 R3 F2 fc2 1120 _ _ _ (-10) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u6d_acc
      | u6d_bytes
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ [] 0 _ _ 1120 (-10) 0 OK X2 (env_world_seed H w R2 []) Hlf3);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS2]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_U6_DD_3 HTx3 KEEP4) as HT4.
    destruct (ff_junk H LINV w _ _ _ _ _ _ _ _ _ _ _ 9060 4 X4 ltac:(unfold AFS_HDR in Q4; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (bj & CBj).
    assert (LBj : length bj = 4%nat) by (destruct CBj as [[Hwf _] _]; cbn in Hwf; tauto).
    destruct (cb4_as_c4 m4 _ bj LBj CBj) as (Cj & Hxj).
    set (xj := bytes_le_to_Z bj) in *.
    assert (HK4 : know_ok asegs (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 xj])) m4 [KWord (SA (EVar WV_FF) 9060) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 xj])) OK (env_world_seed H w R4 [Z_to_bv 64 xj])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 9060) _ 0%nat (C4 (Z_to_bv 64 xj)));
        [ exact Cj | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 [Z_to_bv 64 xj]
          [KWord (SA (EVar WV_FF) 9060) 4 (EVar 41)] HK4 100%nat [APUT_U32] (@nil bool) 42%N
          [3; 4; 7; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_DD_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    u6d_pc VIS5 APUT_U32.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 1120 (-10) (0 + 3) OK X4
                  (env_world_seed H w R4 [Z_to_bv 64 xj]) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    eapply (pm_put_num H HHbp LINV ds_repA DSL _ _ _ _ HU32 w s4 LB4 LBs M5 mo5 c
              [3; 4; 7; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF5 R5 F4 fc4 1120 _ xj (-10) (0 + 3) Q);
      [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5 | exact FZ4
      | rtf HTx5 | reflexivity | lia | rtf HTx5 | rtf HTx5 | exact G4_5 | rtf HTx5
      | rewrite (HR5 11%bv); transitivity (Z_to_bv 64 (sx32A xj));
          [ exact (edenot_sext32 (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 xj])) 41 xj eq_refl Hxj)
          | f_equal; unfold sx32A, PrsGrammar.sx32, LbB_DiagStmt.sx32; destruct (xj <? 2 ^ 31); cbn beta iota; lia ] | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | exact DS5
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF6 mo6 R6 F6 fc6 s6 LB6 m6 TB6 KR6 VIS6 RF6 FZ6 X6 KEEP6 (DS6 & HR10_6) FR6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_tbl_restrict w [] _ R6 (rt_keep RT_PM_U6_DD_5) (regs_keep w _ R5 R6 RT_PM_U6_DD_5 HTx5 KEEP6) ltac:(vm_compute; reflexivity)) as HT6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 7; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_DD_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    u6d_pc VIS7 APUT_CSEQ.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s6 LB6 LBs M7 mo7 c
              [3; 4; 7; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF7 R7 F6 fc6 1120 _ _ _ (-10) (0 + 3 + 24) Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact FZ6
      | rtf HTx7 | reflexivity | lia | rtf HTx7 | rtf HTx7 | exact G4_7 | rtf HTx7 | rtf HTx7 | rtf HTx7
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u6d_acc
      | u6d_bytes
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s6 LB6 LBs m6 mo6 c _ _ _ _ _ _ _ 1120 (-10) (0 + 3 + 24) OK X6 (env_world_seed H w R6 []) Hlf7);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS6]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF8 mo8 R8 F8 fc8 s8 LB8 m8 TB8 KR8 VIS8 RF8 FZ8 X8 KEEP8 (DS8 & HR10_8) FR8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    pose proof (regs_keep w _ R7 R8 RT_PM_U6_DD_7 HTx7 KEEP8) as HT8.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS8) as ERR8.
    assert (HK8 : know_ok asegs (Eseed R8 (wenv_vals w ++ [])) m8 [KWord (SA (EVar WV_FF) 1480) 4 (ELit 4294967286)]).
    { pose proof (ev_ff H w (Eseed R8 (wenv_vals w ++ [])) OK (env_world_seed H w R8 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m8 (wa_ff w + 1120 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-10) mod 2 ^ 32))));
        [exact ERR8 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          [KWord (SA (EVar WV_FF) 1480) 4 (ELit 4294967286)] HK8 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 7; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_DD_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    u6d_pc VIS9 ADS_DTOR.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s8 LB8 LBs M9 mo9 c
              [3; 4; 7; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB8 _ msF9 R9 F8 fc8 1120 _ (-10) (0 + 3 + 24 + 26) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ8
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s8 LB8 LBs m8 mo8 c _ _ _ _ _ _ _ 1120 (-10) (0 + 3 + 24 + 26) OK X8
                  (env_world_seed H w R8 []) Hlf9);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS8]
      | cbn; tauto
      | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (TB10e & ADDR10) FR10. subst TB10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_keep w _ R9 R10 RT_PM_U6_DD_9 HTx9 KEEP10) as HT10.
    pm_go HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word) (@nil kentry) 200%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U6_DD_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    u6d_pc VIS11 OL_CHECK.
    eapply (K s10 LB10 LBs M11 mo11 c msF11 R11 F10 fc10 TBL_EEF44 _ (2 ^ 32 - 10));
      [ exact X11 | intros ? h; exact h | exact Htr | exact BUD | exact Hbsz | exact KR11 | exact VIS11 | exact RF11
      | exact FZ10 | exact (regs_tbl_sub w [] R11 RT_PM_U6_DD_11 RT_CHECK HTx11 ltac:(vm_compute; reflexivity))
      | rewrite (HR11 3%bv); exact G3_10 | rewrite (HR11 4%bv); exact G4_10 | rtf HTx11 | lia ].
  Qed.

End U6d.
