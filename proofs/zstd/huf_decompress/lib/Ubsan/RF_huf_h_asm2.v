(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_h_iface RF_huf_iface_m RF_huf_h_kit RF_huf_h_lib RF_huf_h_split.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_asm2 () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission4Spec7Harness8free_optC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure>implM_from_evtC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks5blockC46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps4bptrC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface5RHEAPC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8rauxv_okK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePHRHEAP_blocks_nodup_proofC47Corelib5Lists7ListDef3mapI46Stdlib5Lists4List5NoDup00C5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks6blk_idC5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_facts<lb_remove_hdC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps8raw_freeC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=fuzz_one_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface:rfree_postK47Corelib4Init5Logic2or01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_faC5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_soI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface:rheap_presC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_addrC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_sizeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_ifaceCrheap_pres_rw_cellsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_ifaceArheap_pres_weakenC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface@rheap_pres_transK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission4Spec5Monad9implM_retC5ARocqVerifyHarness?AgentSubmission4Spec5Monad:implM_bindK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission6Malloc<Malloc_iface9lb_removeC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5implMC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission4Spec7Harness=PRODUCER_SIZEI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep6RERRNOC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit9errno_litK4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RATPK4ELinuxProcessSemantics5Riscv5Instr5aluop01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface;RFREE_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep5RLIBCC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RCTXC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep:RSSP_GUARDC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep8RGOT_SSPC4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission3Lib6MonadX:implM_retbI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=rclient_rangeC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split8hM_stateC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_dbufC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rblock_rangeC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness6hp_mtlC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness8DT_BYTESC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split7fz_restK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness?huf_draws_rangeC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness9huf_drawsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_streamsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:hp_symbolsC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness7hp_restC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<DTABLE_BYTESC46Stdlib5Lists4List9app_assocC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split@RHEAP_disj_splitC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib6ZArith6BinInt1Z3divC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split@payload_own_disjC46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib2hkC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib7hC_postC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib<phaseC_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit8fh_fp_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit<fh_transportK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split>lb_remove_mid'C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface?rfree_null_specC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_h_asm27fz_tailC5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission4Spec5Monad9implM_evtC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface7prod_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=HARNESS_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split5PC_HMI5ARocqVerifyHarness?AgentSubmission4Spec:HufHarness:huf_params00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib=PC_HC_EXIT_RAC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_lib8PFREE_HC".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.

Section Second.
  Variable dt_ok : fmem -> Z -> Z -> Prop.
  Hypothesis RDT1 : huf_rdt_stmt dt_ok PHUF_RDT_X1.
  Hypothesis RDT2 : huf_rdt_stmt dt_ok PHUF_RDT_X2.
  Hypothesis DEC1 : huf_dec_stmt dt_ok PHUF_DEC_1X.
  Hypothesis DEC4 : huf_dec_stmt dt_ok PHUF_DEC_4X.
  Hypothesis FREE : rfree_stmt.
  Hypothesis PFREE : prod_free_stmt.

  Ltac walk_to pc := repeat (lazymatch goal with
     | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
     | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_true | if_false]
     | |- evt _ _ (MS _ _ _ _ _ _ _) => zstep end).
  Ltac walk_toc c := let v := eval cbv in c in walk_to v.

  Lemma rw_cells_prefix : forall m A pre post, rw_cells usegs m A (pre ++ post) -> rw_cells usegs m A pre.
  Proof.
    intros m A pre post H. unfold rw_cells, cells_at in *. destruct H as [[WF BA] WR].
    assert (WF1 : cells_wf pre).
    { clear -WF. induction pre as [|c pre IH]; cbn in *; [exact I| tauto]. }
    assert (EB : cells_bytes (pre ++ post) = cells_bytes pre ++ cells_bytes post).
    { clear. induction pre as [|c pre IH]; cbn; [reflexivity| rewrite IH, app_assoc; reflexivity]. }
    rewrite EB in BA. destruct BA as (B1 & B2 & B3). rewrite cells_size_app in WR. destruct WR as (W1 & W2 & W3).
    rewrite length_app in B2.
    split; [split; [exact WF1|]|].
    - split; [exact B1|]. split; [lia|].
      intros i Hi. rewrite B3 by (rewrite length_app; lia). apply nth_error_app1. exact Hi.
    - split; [exact W1|]. split; [lia|]. intros i Hi. apply W3. lia.
  Qed.

  Lemma RHEAP_pre_disj : forall s m pre l1 b1 l2 b2 l3,
    RHEAP s (pre ++ l1 ++ b1 :: l2 ++ b2 :: l3) m ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
  Proof.
    intros s m pre l1 b1 l2 b2 l3 H. apply (RHEAP_disj_split s m (pre ++ l1) b1 l2 b2 l3).
    rewrite <- app_assoc. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_tail : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (s : PState) (LB : list block) (AB lo : Z) (p : bptr) (P : Z) (s3' : PState)
      (rax t0 t1 t2 y1 a0 a1 a2 a3 a4 a5 a6 a7 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3 t4 t5 t6 : word) (m3 : mem) (errv3 : word)
      (j0 : list byte) (z1 z2 : word),
    frm0 fc -> bv_unsigned sp <= AB -> ATOP <= lo -> lo <= bv_unsigned sp - 16384 -> bv_unsigned sp mod 16 = 0 ->
    RHEAP s3' ((p, P, PRODUCER_SIZE) :: LB) m3 ->
    rauxv_ok m3 AB -> rw_cells usegs m3 RERRNO [C4 errv3] ->
    rw_cells usegs m3 (bv_unsigned sp + -128) [CB 8 j0; C8 z1; C8 z2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                                               C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m3 lo (bv_unsigned sp + -128) -> mem_inv usegs m3 ->
    rheap_pres LB (bv_unsigned sp) m m3 -> ps_so s3' = ps_so s ->
    implM usegs (Harness.free_opt raw_free (Some p) ;;; mret 0) s3'
      (fuzz_one_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 P) y1 a0 a1 a2 a3 a4 a5 a6 a7
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1348c) fc None m3 (seg_rom usegs)).
Proof.
  intros until z2. intros FC SPB LOA LOS SPA HP AUX ERR FR ST MI RP SO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  unfold Harness.free_opt.
  apply implM_from_evt. walk_toc PPROD_FREE. apply evt_done.
  eapply implM_bind.
  { unfold prod_free_stmt in PFREE.
    eapply PFREE with (A := P) (n := PRODUCER_SIZE) (lo := lo) (B := AB) (LB := (p, P, PRODUCER_SIZE) :: LB);
      try reflexivity; unfold RFREE_STACK; rewrite ?unsigned_lit by lia;
      first [exact HP | exact AUX | exact ST | exact MI | (left; reflexivity) | lia
            | (rewrite errno_lit; unfold RERRNO; exact ERR)]. }
  cbv beta. intros [] s4' ms4 PO.
  destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & -> & MI4 & ST4
                  & ERR4 & AUX4 & RP4 & FA4 & SO4 & HP4).
  rewrite (lb_remove_hd p (p, P, PRODUCER_SIZE) LB eq_refl (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP)) in RP4, HP4.
  rewrite ?unsigned_lit in ST4, RP4 by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
  pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP4 FR ltac:(left; lia)) as FR4.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  apply implM_ret.
  repeat zstep.
  apply evt_done. unfold fuzz_one_post.
  do 14 eexists. exists F, fc, m4, errv3. split; [reflexivity|].
  split; [lia|]. split; [exact MI4|]. split; [exact FC|].
  split; [release_frame FR4 ST4 (bv_unsigned sp); exact ST4|].
  split; [rewrite errno_lit; exact ERR4|]. split; [exact AUX4|].
  split; [eapply rheap_pres_trans; [exact RP| eapply rheap_pres_weaken; [exact RP4| lia| intros b Hb; exact Hb]]|].
  split; [exact HP4| congruence].
Qed.

  Theorem fz_second :
    forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z)
           (producer dt wksp dBuf : option bptr) (s' : PState) (ms' : machine_state),
      Forall (fun c => 0 <= c < 256) payload ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      D mod 16 = 0 -> 0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      bv_unsigned sp <= AB -> AB <= 2^47 -> ATOP <= lo -> lo <= bv_unsigned sp - HARNESS_STACK ->
      frm0 fc -> bv_unsigned sp mod 16 = 0 ->
      hM_state ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB AB lo D payload m producer dt wksp dBuf s' ms' ->
      implM usegs (fz_rest producer dt wksp dBuf) s'
            (fuzz_one_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m) ms'.
Proof.
  intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB D pl AB lo producer dt wksp dBuf s' ms'.
  intros PLB RR DM D0 DA PLEN SPB AB47 LOA LOS FC SPA HM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  unfold HARNESS_STACK in LOS. unfold zlength in *.
  pose proof (huf_draws_range pl (zlen pl) ltac:(lia)) as HR. cbv zeta in HR.
  destruct HR as (HR1 & HR2 & HR3 & HR4 & HR5). unfold HUF_TABLELOG_MAX in HR4.
  destruct HM as (p & pd & pw & P & DT & W & DST & LBd & f1 & f2 & f3 & f4 & f5 & j0 & jdt & jw & jd
                  & rax & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & errv1
                  & -> & -> & -> & HD & -> & G1 & G2 & G3 & G4 & G5 & HP1 & BRP & BRD & BRW & AUX1 & ERR1 & FR1 & PB1
                  & PR1 & DTC & WC1 & DC & ST1 & MI1 & RP1 & SO1).
  pose proof BRP as (BP1 & BP2 & BP3 & BP4 & BP5). pose proof BRD as (BD1 & BD2 & BD3 & BD4 & BD5).
  pose proof BRW as (BW1 & BW2 & BW3 & BW4 & BW5). unfold PRODUCER_SIZE in BP3, BP4, BP5.
  assert (DTB : 8 <= DT_BYTES (hp_mtl (huf_draws pl (zlen pl))) <= 16388).
  { unfold DT_BYTES.
    pose proof (Z.pow_le_mono_r 2 _ 12 ltac:(lia) (proj2 HR4)) as E1.
    pose proof (Z.pow_pos_nonneg 2 (hp_mtl (huf_draws pl (zlen pl))) ltac:(lia) ltac:(lia)) as E2.
    change (2 ^ 12) with 4096 in E1. lia. }
  assert (HP1' : RHEAP s' ((LBd ++ [(pw, W, 8704); (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl))));
                                    (p, P, PRODUCER_SIZE)]) ++ LB) m1) by (rewrite <- app_assoc; exact HP1).
  assert (DJS : hk (P + 16 <= DT \/ DT + DTABLE_BYTES (hp_mtl (huf_draws pl (zlen pl))) <= P)
                /\ hk (D + zlen pl <= DT \/ DT + DTABLE_BYTES (hp_mtl (huf_draws pl (zlen pl))) <= D)
                /\ hk (D + zlen pl <= W \/ W + 8704 <= D)
                /\ hk (DT + DTABLE_BYTES (hp_mtl (huf_draws pl (zlen pl))) <= W \/ W + 8704 <= DT)).
  { unfold hk, DTABLE_BYTES.
    pose proof (payload_own_disj s' m1 _ LB (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) (bv_unsigned sp) D (zlen pl)
                  HP1' ltac:(apply in_or_app; right; right; left; reflexivity) RR ltac:(lia) DA ltac:(lia)) as J1.
    pose proof (payload_own_disj s' m1 _ LB (pw, W, 8704) (bv_unsigned sp) D (zlen pl)
                  HP1' ltac:(apply in_or_app; right; left; reflexivity) RR ltac:(lia) DA ltac:(lia)) as J2.
    pose proof (RHEAP_pre_disj s' m1 LBd [(pw, W, 8704)] (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) []
                  (p, P, PRODUCER_SIZE) LB HP1) as J3.
    pose proof (RHEAP_pre_disj s' m1 LBd [] (pw, W, 8704) [] (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))
                  ((p, P, PRODUCER_SIZE) :: LB) HP1) as J4.
    cbn [blk_addr blk_size fst snd] in J1, J2, J3, J4. unfold PRODUCER_SIZE in J3. lia. }
  assert (DSTF : hk ((DST = 0 /\ hp_dbuf (huf_draws pl (zlen pl)) = 0) \/ (0 < DST /\ DST mod 8 = 0))
                 /\ DST + hp_dbuf (huf_draws pl (zlen pl)) <= ATOP
                 /\ hk (D + zlen pl <= DST \/ DST + hp_dbuf (huf_draws pl (zlen pl)) <= D)
                 /\ hk (DT + DTABLE_BYTES (hp_mtl (huf_draws pl (zlen pl))) <= DST
                        \/ DST + hp_dbuf (huf_draws pl (zlen pl)) <= DT)
                 /\ hk (W + 8704 <= DST \/ DST + hp_dbuf (huf_draws pl (zlen pl)) <= W)).
  { unfold hk, DTABLE_BYTES. destruct HD as [(_ & -> & HZ & ->)|(pb & _ & -> & BRB)].
    - rewrite HZ. lia.
    - pose proof BRB as (BB1 & BB2 & BB3 & BB4 & BB5).
      pose proof (payload_own_disj s' m1 [(pb, DST, hp_dbuf (huf_draws pl (zlen pl))); (pw, W, 8704);
                    (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))); (p, P, PRODUCER_SIZE)] LB
                    (pb, DST, hp_dbuf (huf_draws pl (zlen pl))) (bv_unsigned sp) D (zlen pl) HP1 ltac:(left; reflexivity)
                    RR ltac:(lia) DA ltac:(lia)) as J1.
      pose proof (RHEAP_disj_split s' m1 [] (pb, DST, hp_dbuf (huf_draws pl (zlen pl))) [(pw, W, 8704)]
                    (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) ((p, P, PRODUCER_SIZE) :: LB) HP1) as J2.
      pose proof (RHEAP_disj_split s' m1 [] (pb, DST, hp_dbuf (huf_draws pl (zlen pl))) []
                    (pw, W, 8704) ((pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) :: (p, P, PRODUCER_SIZE) :: LB)
                    HP1) as J3.
      cbn [blk_addr blk_size fst snd] in J1, J2, J3. lia. }
  destruct DJS as (DJ1 & DJ2 & DJ3 & DJ4). destruct DSTF as (DF1 & DF2 & DF3 & DF4 & DF5).
  pose proof (rw_cells_prefix m1 _ [CB 8 j0; C8 (Z_to_bv 64 (hp_streams (huf_draws pl (zlen pl))));
                                    C8 (Z_to_bv 64 (hp_symbols (huf_draws pl (zlen pl))))] _ FR1) as FRp.
  eapply implM_evt.
  { eapply phaseC_proof with (dt_ok := dt_ok) (SP := bv_unsigned sp + -128) (P := P) (D := D) (DT := DT) (W := W)
      (DST := DST) (dbs := hp_dbuf (huf_draws pl (zlen pl))) (mtl := hp_mtl (huf_draws pl (zlen pl)))
      (streams := hp_streams (huf_draws pl (zlen pl))) (symbols := hp_symbols (huf_draws pl (zlen pl)))
      (rest := hp_rest (huf_draws pl (zlen pl))) (lo := lo) (pl := pl) (m0 := m1) (gp := gp) (tp := Z_to_bv 64 RATP)
      (F := F) (fc := fc);
      first [ eassumption | exact FRp | (unfold DTABLE_BYTES; lia) | (unfold hk, DTABLE_BYTES in *; lia) ]. }
  intros msC HC.
  destruct HC as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & c16 & c17
                  & c18 & c19 & c20 & c21 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  assert (TR : RHEAP s' (LBd ++ (pw, W, 8704) :: (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))
                         :: (p, P, PRODUCER_SIZE) :: LB) m2
               /\ rauxv_ok m2 AB /\ rw_cells usegs m2 RERRNO [C4 errv1] /\ rheap_pres LB (bv_unsigned sp) m1 m2).
  { destruct HD as [(_ & -> & HZ & ->)|(pb & _ & -> & BRB)].
    - apply (munch_weaken _ [(bv_unsigned sp + -128 - 4096, bv_unsigned sp + -128);
                             (DT, DT + DTABLE_BYTES (hp_mtl (huf_draws pl (zlen pl)))); (W, W + 8704)]) in MU2;
        [| unfold sub_fp; intros x; cbn [outside]; rewrite HZ; intuition lia].
      destruct (fh_transport s' [(pw, W, 8704); (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))); (p, P, PRODUCER_SIZE)]
                  LB m1 m2 _ AB (bv_unsigned sp) HP1 MU2 WM2) as (T1 & T2 & T3 & T4).
      { rewrite Forall_forall. intros iv HI. cbn [In] in HI. unfold fh_fp_ok.
        destruct HI as [<-|[<-|[<-|[]]]]; cbn [fst snd].
        - left. lia.
        - right. exists (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))).
          split; [cbn [In]; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; unfold DTABLE_BYTES; lia].
        - right. exists (pw, W, 8704). split; [cbn [In]; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
      { lia. }
      split; [exact T1|]. split; [exact (T2 AUX1)|]. split; [exact (T3 _ ERR1)| exact T4].
    - pose proof BRB as (BB1 & BB2 & BB3 & BB4 & BB5).
      destruct (fh_transport s' [(pb, DST, hp_dbuf (huf_draws pl (zlen pl))); (pw, W, 8704);
                  (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))); (p, P, PRODUCER_SIZE)]
                  LB m1 m2 _ AB (bv_unsigned sp) HP1 MU2 WM2) as (T1 & T2 & T3 & T4).
      { rewrite Forall_forall. intros iv HI. cbn [In] in HI. unfold fh_fp_ok.
        destruct HI as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
        - left. lia.
        - right. exists (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))).
          split; [cbn [In]; right; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; unfold DTABLE_BYTES; lia].
        - right. exists (pw, W, 8704). split; [cbn [In]; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - right. exists (pb, DST, hp_dbuf (huf_draws pl (zlen pl))).
          split; [cbn [In]; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
      { lia. }
      split; [exact T1|]. split; [exact (T2 AUX1)|]. split; [exact (T3 _ ERR1)| exact T4]. }
  destruct TR as (HP2 & AUX2 & ERR2 & RP2).
  pose proof FR1 as FR2.
  eapply rw_cells_transport in FR2;
    [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; unfold DTABLE_BYTES; lia].
  assert (EL1 : LBd ++ (pw, W, 8704) :: (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) :: (p, P, PRODUCER_SIZE) :: LB
                = (LBd ++ [(pw, W, 8704)]) ++ (pd, DT, DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))
                  :: (p, P, PRODUCER_SIZE) :: LB)
    by (rewrite <- app_assoc; reflexivity).
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP2) as ND2.
  unfold fz_rest.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (A := DT) (n := DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) (lo := lo) (B := AB);
      try reflexivity; unfold RFREE_STACK; rewrite ?unsigned_lit by lia;
      first [exact HP2 | exact AUX2 | exact ST2 | exact MI2 | (apply in_or_app; right; right; left; reflexivity) | lia
            | (rewrite errno_lit; unfold RERRNO; exact ERR2)]. }
  cbv beta. intros [] s3' ms3 PO.
  destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m3 & -> & MI3 & ST3
                  & ERR3 & AUX3 & RP3 & FA3 & SO3 & HP3).
  rewrite (lb_remove_mid' pd _ _ _ _ EL1 eq_refl ND2) in RP3, HP3.
  rewrite ?unsigned_lit in ST3, RP3 by lia. rewrite errno_lit in ERR3. unfold RERRNO in ERR3.
  unfold PC_HC_EXIT_RA. rewrite ret_pc_even by (first [lia | reflexivity]).
  assert (EL2 : (LBd ++ [(pw, W, 8704)]) ++ (p, P, PRODUCER_SIZE) :: LB = LBd ++ (pw, W, 8704) :: (p, P, PRODUCER_SIZE) :: LB)
    by (rewrite <- app_assoc; reflexivity).
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP3) as ND3.
  apply implM_from_evt. walk_toc RFREE_SYM. apply evt_done.
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (A := W) (n := 8704) (lo := lo) (B := AB);
      try reflexivity; unfold RFREE_STACK; rewrite ?unsigned_lit by lia;
      first [exact HP3 | exact AUX3 | exact ST3 | exact MI3
            | (apply in_or_app; left; apply in_or_app; right; left; reflexivity) | lia
            | (rewrite errno_lit; unfold RERRNO; exact ERR3)]. }
  cbv beta. intros [] s4' ms4 PO.
  destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MI4 & ST4
                  & ERR4 & AUX4 & RP4 & FA4 & SO4 & HP4).
  rewrite (lb_remove_mid' pw _ _ _ _ EL2 eq_refl ND3) in RP4, HP4.
  rewrite ?unsigned_lit in ST4, RP4 by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  apply implM_from_evt. walk_toc RFREE_SYM. apply evt_done.
  assert (RP14 : rheap_pres LB (bv_unsigned sp) m m4).
  { eapply rheap_pres_trans; [exact RP1|].
    eapply rheap_pres_trans; [exact RP2|].
    eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact RP3| lia| intros b Hb; apply in_or_app; right; right; exact Hb]|].
    eapply rheap_pres_weaken; [exact RP4| lia| intros b Hb; apply in_or_app; right; right; exact Hb]. }
  pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP3 FR2 ltac:(left; lia)) as FR3.
  pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP4 FR3 ltac:(left; lia)) as FR4.
  assert (SO4' : ps_so s4' = ps_so s) by congruence.
  destruct HD as [(-> & -> & HZ & ->)|(pb & -> & -> & BRB)].
  - cbn [Harness.free_opt]. apply implM_retb.
    eapply implM_evt; [eapply rfree_null_spec; reflexivity|].
    intros ms5 ->. rewrite ret_pc_even by (first [lia | reflexivity]).
    eapply (fz_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB AB lo p P);
      first [exact FC | lia | exact HP4 | exact AUX4 | exact ERR4 | exact FR4 | exact ST4 | exact MI4 | exact RP14
            | exact SO4'].
  - pose proof BRB as (BB1 & BB2 & BB3 & BB4 & BB5). cbn [app] in HP4, RP4.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (A := DST) (n := hp_dbuf (huf_draws pl (zlen pl))) (lo := lo) (B := AB);
        try reflexivity; unfold RFREE_STACK; rewrite ?unsigned_lit by lia;
        first [exact HP4 | exact AUX4 | exact ST4 | exact MI4 | (left; reflexivity) | lia
              | (rewrite errno_lit; unfold RERRNO; exact ERR4)]. }
    cbv beta. intros [] s5' ms5 PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m5 & -> & MI5 & ST5
                    & ERR5 & AUX5 & RP5 & FA5 & SO5 & HP5).
    rewrite (lb_remove_hd pb (pb, DST, hp_dbuf (huf_draws pl (zlen pl))) ((p, P, PRODUCER_SIZE) :: LB) eq_refl
               (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP4)) in RP5, HP5.
    rewrite ?unsigned_lit in ST5, RP5 by lia. rewrite errno_lit in ERR5. unfold RERRNO in ERR5.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ RP5 FR4 ltac:(left; lia)) as FR5.
    eapply (fz_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB AB lo p P);
      first [exact FC | lia | exact HP5 | exact AUX5 | exact ERR5 | exact FR5 | exact ST5 | exact MI5
            | (eapply rheap_pres_trans; [exact RP14| eapply rheap_pres_weaken; [exact RP5| lia| intros b Hb; right; exact Hb]])
            | congruence].
Qed.

End Second.
End CANSEC1.
