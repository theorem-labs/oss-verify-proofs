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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmVops LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_SnStmt LbB_PmU9K LbB_PmU9c.

Definition RT_PM_U9_S4E_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U9s4e.
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

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u9_s4e : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3b10) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 SN_ERR ->
    pm_bud (wa_n w) c ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 BUD CK.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 10) 1 (2 ^ 64)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 10)) with (PropExec.getr R 10%bv). rewrite HX10, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold SN_ERR. rewrite Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 1 (2 ^ 64)] HK1 20%nat [0xf12dc] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U9_S4E_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U9_S4E_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ _ _ _ _ ?tb _ _ _ => pose proof (tbl_incl TBL_EEF44 tb ltac:(vm_compute; reflexivity)) as IT end. replace (s_pc SSr) with OL_CHECK in VIS1 by reflexivity. eapply (CK _ _ _ _ _ _ _ _ _ _ _ _ (2 ^ 32 - 4) X1 IT Htr BUD Hbsz KR1 VIS1 RF1 FZ0 (regs_tbl_sub w [] R1 _ RT_CHECK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); [ rewrite (HR1 23%bv); apply (eq_trans (y := PropExec.getr R 10%bv)); [reflexivity | rewrite HX10; apply bv_eq; vm_compute; reflexivity] | lia ].
  Qed.

End U9s4e.
