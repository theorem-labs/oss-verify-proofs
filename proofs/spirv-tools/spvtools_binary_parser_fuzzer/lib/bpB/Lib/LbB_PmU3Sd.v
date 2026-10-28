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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL.

Definition RT_PM_U3_SCD4_1 : list (reg * expr) := [(1%bv, ELit 991360); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (18%bv, ELit 4); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD4_3 : list (reg * expr) := [(1%bv, ELit 991368); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 4); (18%bv, ELit 4); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD4_5 : list (reg * expr) := [(1%bv, ELit 991376); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD4_7 : list (reg * expr) := [(1%bv, ELit 991392); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD4_9 : list (reg * expr) := [(1%bv, ELit 991412); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (11%bv, ELit 149664); (12%bv, ELit 5); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD4_11 : list (reg * expr) := [(1%bv, ELit 991428); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD4_13 : list (reg * expr) := [(1%bv, ELit 991428); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_1 : list (reg * expr) := [(1%bv, ELit 991360); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (18%bv, ELit 5); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_3 : list (reg * expr) := [(1%bv, ELit 991368); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 5); (18%bv, ELit 5); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_5 : list (reg * expr) := [(1%bv, ELit 991376); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_7 : list (reg * expr) := [(1%bv, ELit 991392); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_9 : list (reg * expr) := [(1%bv, ELit 991412); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (11%bv, ELit 149664); (12%bv, ELit 5); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_11 : list (reg * expr) := [(1%bv, ELit 991428); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 2512)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3_SCD5_13 : list (reg * expr) := [(1%bv, ELit 991428); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

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
Ltac fixpc VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.
Ltac stk := first [ lia | unfold TL_STACK, AINTRIN_STACK; lia | vm_compute; split; discriminate ].
Section U3Sd.
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
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u3_scd4 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1fa0) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    pm_bud (wa_n w) c ->
    PropExec.getr R 21%bv = Z_to_bv 64 0 ->
    PropExec.getr R 18%bv = Z_to_bv 64 4 ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD HX21 HX18 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (regs_tbl_cons w [] R RT_ARM 21%bv (ELit 0) ltac:(rewrite HX21; reflexivity) HT0) as HT0a.
    pose proof (regs_tbl_cons w [] R _ 18%bv (ELit 4) ltac:(rewrite HX18; reflexivity) HT0a) as HT0z.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0z (@nil word)
          (@nil kentry) 200%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    fixpc VIS1 APDIAG.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 2512 _ (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | first [reflexivity | cbn; reflexivity]
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    subst TB2.
    pose proof (regs_keep w _ R1 R2 RT_PM_U3_SCD4_1 HTx1 KEEP2) as HT2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word)
          (@nil kentry) 100%nat [AT_OPERAND_TYPE_STR] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    fixpc VIS3 AT_OPERAND_TYPE_STR.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ _ _ _ _ 2512 (-4) 0 OK X2 (env_world_seed H w R2 []) Hlf3
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS2) as DS3.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_OPERAND_TYPE_STR _ _ _ _ (tla_operand_type_str HTL) 4 w _ _ _ _ _ c _ _ _ _ _ msF3 R3 F2 fc2 _ _);
      [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | rtf HTx3 | rtf HTx3 | reflexivity | lia | stk | reflexivity
      | cbn beta iota; split; [lia|]; split; [rtf HTx3 | exact (LINV_relro _ (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3))]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF4 mo4 M4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 (p & n & CS4 & Er4 & Hpn).
    vm_compute in Hpn. injection Hpn as Ep En. subst n.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w [] R3 R4 RT_PM_U3_SCD4_3 HTx3 KEEP4) as HT4.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s2 LB2 LBs M3 mo3 c _ _ _ _ _ M4 _ 2512 (-4) 0 OK X3 MU4
                  ltac:(stk) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS3) as DS4.
    pm_go HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word)
          (@nil kentry) 100%nat [ASTRLEN_STUB] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    fixpc VIS5 ASTRLEN_STUB.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    assert (E10_5 : PropExec.getr R5 10%bv = Z_to_bv 64 p) by (rewrite (HR5 10%bv); exact Er4).
    assert (E18_5 : PropExec.getr R5 18%bv = Z_to_bv 64 p) by (rewrite (HR5 18%bv); exact Er4).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs M4 mo4 c _ _ _ _ _ _ _ 2512 (-4) 0 OK X4 (env_world_seed H w R4 []) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    eapply (pm_leafS H HHm LINV LINV_frame ASTRLEN_STUB _ _ _ _ (strlen_cstr_tleaf (ah_strlen H HHm)) (p, 19) w _ _ _ _ _ c _ _ _ _ _ msF5 R5 F2 fc2 _ _);
      [ exact OK | exact X5 | exact KR5 | exact VIS5 | exact RF5 | rtf HTx5 | rtf HTx5 | reflexivity | lia | stk | reflexivity
      | cbn beta iota; split; [exact CS4 | exact E10_5]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF6 mo6 M6 R6 KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 SL6. cbn [snd] in SL6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    assert (E18_6 : PropExec.getr R6 18%bv = Z_to_bv 64 p) by (transitivity (PropExec.getr R5 18%bv); [apply KEEP6; cbn; tauto | exact E18_5]).
    pose proof (regs_keep w [] R5 R6 RT_PM_U3_SCD4_5 HTx5 KEEP6) as HT6.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s2 LB2 LBs M5 mo5 c _ _ _ _ _ M6 _ 2512 (-4) 0 OK X5 MU6
                  ltac:(stk) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS5) as DS6.
    subst p.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word)
          (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    fixpc VIS7 APUT_CSEQ.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs M6 mo6 c _ _ _ _ _ _ _ 2512 (-4) 0 OK X6 (env_world_seed H w R6 []) Hlf7
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS6) as DS7.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M7 mo7 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF7 R7 F2 fc2 2512 _ _ _ (-4) 0 Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact FZ2
      | rtf HTx7 | reflexivity | lia | rtf HTx7 | rtf HTx7 | exact G4_7 | rtf HTx7
      | rewrite (HR7 11%bv); exact E18_6 | rewrite (HR7 12%bv); exact SL6
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc
      | lit_bytes
      | exact DS7
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF8 mo8 R8 F8 fc8 s8 LB8 m8 TB8 KR8 VIS8 RF8 FZ8 X8 KEEP8 (DS8 & HR10_8) FR8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    pose proof (regs_keep w _ R7 R8 RT_PM_U3_SCD4_7 HTx7 KEEP8) as HT8.
    pm_go HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    fixpc VIS9 APUT_CSEQ.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s8 LB8 LBs m8 mo8 c _ _ _ _ _ _ _ 2512 (-4) (0 + 19) OK X8 (env_world_seed H w R8 []) Hlf9
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS8) as DS9.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s8 LB8 LBs M9 mo9 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF9 R9 F8 fc8 2512 _ _ _ (-4) (0 + 19) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ8
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9 | rtf HTx9 | rtf HTx9
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc
      | lit_bytes
      | exact DS9
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (DS10 & HR10_10) FR10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_keep w _ R9 R10 RT_PM_U3_SCD4_9 HTx9 KEEP10) as HT10.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS10) as ERR10.
    assert (HK10 : know_ok asegs (Eseed R10 (wenv_vals w ++ [])) m10 [KWord (SA (EVar WV_FF) 2872) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R10 (wenv_vals w ++ [])) OK (env_world_seed H w R10 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m10 (wa_ff w + 2512 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR10 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word)
          [KWord (SA (EVar WV_FF) 2872) 4 (ELit 4294967292)] HK10 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    fixpc VIS11 ADS_DTOR.
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s10 LB10 LBs M11 mo11 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB10 _ msF11 R11 F10 fc10 2512 _ (-4) (0 + 19 + 5) Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HTx11 | reflexivity | lia | rtf HTx11 | rtf HTx11 | exact G4_11 | rtf HTx11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s10 LB10 LBs m10 mo10 c _ _ _ _ _ _ _ 2512 (-4) (0 + 19 + 5) OK X10 (env_world_seed H w R10 []) Hlf11);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS10]
      | cbn; tauto
      | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 (TB12e & ADDR12) FR12.
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (transitivity (PropExec.getr R11 4%bv); [apply KEEP12; cbn; tauto | exact G4_11]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (transitivity (PropExec.getr R11 3%bv); [apply KEEP12; cbn; tauto | exact G3_11]).
    subst TB12.
    pose proof (regs_keep w _ R11 R12 RT_PM_U3_SCD4_11 HTx11 KEEP12) as HT12.
    pm_go HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 (@nil word)
          (@nil kentry) 400%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD4_13.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HTx13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M13 := mm) in * end.
    fixpc VIS13 OL_CHECK.
    eapply (K s12 LB12 LBs M13 mo13 c msF13 R13 F12 fc12 TBL_EEF44 _ 4294967292);
      [ exact X13 | apply incl_refl | exact Htr | exact BUD | exact Hbsz | exact KR13 | exact VIS13 | exact RF13
      | exact FZ12 | exact (regs_tbl_sub w [] R13 RT_PM_U3_SCD4_13 RT_CHECK HTx13 ltac:(vm_compute; reflexivity))
      | rewrite (HR13 3%bv); exact G3_12 | rewrite (HR13 4%bv); exact G4_12 | rtf HTx13 | lia ].
  Qed.

  Lemma pm_u3_scd5 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1fa0) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    pm_bud (wa_n w) c ->
    PropExec.getr R 21%bv = Z_to_bv 64 0 ->
    PropExec.getr R 18%bv = Z_to_bv 64 5 ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD HX21 HX18 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (regs_tbl_cons w [] R RT_ARM 21%bv (ELit 0) ltac:(rewrite HX21; reflexivity) HT0) as HT0a.
    pose proof (regs_tbl_cons w [] R _ 18%bv (ELit 5) ltac:(rewrite HX18; reflexivity) HT0a) as HT0z.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0z (@nil word)
          (@nil kentry) 200%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    fixpc VIS1 APDIAG.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 2512 _ (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | first [reflexivity | cbn; reflexivity]
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    subst TB2.
    pose proof (regs_keep w _ R1 R2 RT_PM_U3_SCD5_1 HTx1 KEEP2) as HT2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word)
          (@nil kentry) 100%nat [AT_OPERAND_TYPE_STR] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    fixpc VIS3 AT_OPERAND_TYPE_STR.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ _ _ _ _ 2512 (-4) 0 OK X2 (env_world_seed H w R2 []) Hlf3
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS2) as DS3.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_OPERAND_TYPE_STR _ _ _ _ (tla_operand_type_str HTL) 5 w _ _ _ _ _ c _ _ _ _ _ msF3 R3 F2 fc2 _ _);
      [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | rtf HTx3 | rtf HTx3 | reflexivity | lia | stk | reflexivity
      | cbn beta iota; split; [lia|]; split; [rtf HTx3 | exact (LINV_relro _ (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3))]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF4 mo4 M4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 (p & n & CS4 & Er4 & Hpn).
    vm_compute in Hpn. injection Hpn as Ep En. subst n.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w [] R3 R4 RT_PM_U3_SCD5_3 HTx3 KEEP4) as HT4.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s2 LB2 LBs M3 mo3 c _ _ _ _ _ M4 _ 2512 (-4) 0 OK X3 MU4
                  ltac:(stk) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS3) as DS4.
    pm_go HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word)
          (@nil kentry) 100%nat [ASTRLEN_STUB] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    fixpc VIS5 ASTRLEN_STUB.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    assert (E10_5 : PropExec.getr R5 10%bv = Z_to_bv 64 p) by (rewrite (HR5 10%bv); exact Er4).
    assert (E18_5 : PropExec.getr R5 18%bv = Z_to_bv 64 p) by (rewrite (HR5 18%bv); exact Er4).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs M4 mo4 c _ _ _ _ _ _ _ 2512 (-4) 0 OK X4 (env_world_seed H w R4 []) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    eapply (pm_leafS H HHm LINV LINV_frame ASTRLEN_STUB _ _ _ _ (strlen_cstr_tleaf (ah_strlen H HHm)) (p, 8) w _ _ _ _ _ c _ _ _ _ _ msF5 R5 F2 fc2 _ _);
      [ exact OK | exact X5 | exact KR5 | exact VIS5 | exact RF5 | rtf HTx5 | rtf HTx5 | reflexivity | lia | stk | reflexivity
      | cbn beta iota; split; [exact CS4 | exact E10_5]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF6 mo6 M6 R6 KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 SL6. cbn [snd] in SL6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    assert (E18_6 : PropExec.getr R6 18%bv = Z_to_bv 64 p) by (transitivity (PropExec.getr R5 18%bv); [apply KEEP6; cbn; tauto | exact E18_5]).
    pose proof (regs_keep w [] R5 R6 RT_PM_U3_SCD5_5 HTx5 KEEP6) as HT6.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s2 LB2 LBs M5 mo5 c _ _ _ _ _ M6 _ 2512 (-4) 0 OK X5 MU6
                  ltac:(stk) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS5) as DS6.
    subst p.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word)
          (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    fixpc VIS7 APUT_CSEQ.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs M6 mo6 c _ _ _ _ _ _ _ 2512 (-4) 0 OK X6 (env_world_seed H w R6 []) Hlf7
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS6) as DS7.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M7 mo7 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF7 R7 F2 fc2 2512 _ _ _ (-4) 0 Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact FZ2
      | rtf HTx7 | reflexivity | lia | rtf HTx7 | rtf HTx7 | exact G4_7 | rtf HTx7
      | rewrite (HR7 11%bv); exact E18_6 | rewrite (HR7 12%bv); exact SL6
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc
      | lit_bytes
      | exact DS7
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF8 mo8 R8 F8 fc8 s8 LB8 m8 TB8 KR8 VIS8 RF8 FZ8 X8 KEEP8 (DS8 & HR10_8) FR8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    pose proof (regs_keep w _ R7 R8 RT_PM_U3_SCD5_7 HTx7 KEEP8) as HT8.
    pm_go HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    fixpc VIS9 APUT_CSEQ.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s8 LB8 LBs m8 mo8 c _ _ _ _ _ _ _ 2512 (-4) (0 + 8) OK X8 (env_world_seed H w R8 []) Hlf9
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS8) as DS9.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s8 LB8 LBs M9 mo9 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF9 R9 F8 fc8 2512 _ _ _ (-4) (0 + 8) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ8
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9 | rtf HTx9 | rtf HTx9
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc
      | lit_bytes
      | exact DS9
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (DS10 & HR10_10) FR10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_keep w _ R9 R10 RT_PM_U3_SCD5_9 HTx9 KEEP10) as HT10.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS10) as ERR10.
    assert (HK10 : know_ok asegs (Eseed R10 (wenv_vals w ++ [])) m10 [KWord (SA (EVar WV_FF) 2872) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R10 (wenv_vals w ++ [])) OK (env_world_seed H w R10 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m10 (wa_ff w + 2512 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR10 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word)
          [KWord (SA (EVar WV_FF) 2872) 4 (ELit 4294967292)] HK10 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 10; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    fixpc VIS11 ADS_DTOR.
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s10 LB10 LBs M11 mo11 c
              [3; 4; 10; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB10 _ msF11 R11 F10 fc10 2512 _ (-4) (0 + 8 + 5) Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HTx11 | reflexivity | lia | rtf HTx11 | rtf HTx11 | exact G4_11 | rtf HTx11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s10 LB10 LBs m10 mo10 c _ _ _ _ _ _ _ 2512 (-4) (0 + 8 + 5) OK X10 (env_world_seed H w R10 []) Hlf11);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS10]
      | cbn; tauto
      | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 (TB12e & ADDR12) FR12.
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (transitivity (PropExec.getr R11 4%bv); [apply KEEP12; cbn; tauto | exact G4_11]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (transitivity (PropExec.getr R11 3%bv); [apply KEEP12; cbn; tauto | exact G3_11]).
    subst TB12.
    pose proof (regs_keep w _ R11 R12 RT_PM_U3_SCD5_11 HTx11 KEEP12) as HT12.
    pm_go HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 (@nil word)
          (@nil kentry) 400%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U3_SCD5_13.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HTx13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M13 := mm) in * end.
    fixpc VIS13 OL_CHECK.
    eapply (K s12 LB12 LBs M13 mo13 c msF13 R13 F12 fc12 TBL_EEF44 _ 4294967292);
      [ exact X13 | apply incl_refl | exact Htr | exact BUD | exact Hbsz | exact KR13 | exact VIS13 | exact RF13
      | exact FZ12 | exact (regs_tbl_sub w [] R13 RT_PM_U3_SCD5_13 RT_CHECK HTx13 ltac:(vm_compute; reflexivity))
      | rewrite (HR13 3%bv); exact G3_12 | rewrite (HR13 4%bv); exact G4_12 | rtf HTx13 | lia ].
  Qed.

End U3Sd.
