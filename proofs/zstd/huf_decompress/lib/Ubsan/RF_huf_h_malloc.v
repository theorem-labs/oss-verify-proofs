(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RF_huf_iface_m RF_huf_h_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_malloc () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5implMC5ARocqVerifyHarness?AgentSubmission4Spec7Harness;fuzz_mallocC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit>implM_post_evtC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure>implM_from_evtC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps4bptrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission4Spec5Monad9implM_retC5ARocqVerifyHarness?AgentSubmission4Spec5Monad9implM_unrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad:implM_bindC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface5RHEAPC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8rauxv_okC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4list01C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m@fuzz_malloc_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_faC5ARocqVerifyHarness?AgentSubmission4Spec6PState5ps_soC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface:rheap_presK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitDrauxv_ok_stack_frameC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rclient_addrC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=ralloc_staticC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission6Malloc<Malloc_iface8in_blockK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_addrC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePGRHEAP_block_range_proofC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_sizeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rblock_rangeC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitCrheap_pres_of_munchC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitARHEAP_stack_frameK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z6ltb_ltK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps:raw_mallocC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rmalloc_postC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=raddr_exposedC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_ifaceCrheap_pres_rw_cellsC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_ifaceArheap_pres_weakenC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface@rheap_pres_transK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m@fuzz_malloc_stmtC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C47Corelib5Lists7ListDef6firstnC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula07C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps8ptr_addrC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep6RERRNOC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit9errno_litC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op205I5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00I47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks5blockK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_mAFUZZ_MALLOC_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RATPC5ARocqVerifyHarness?AgentSubmission4Spec4Prog;new_handlerC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m<PFUZZ_MALLOCI47Corelib4Init9Datatypes9Empty_set00K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=RMALLOC_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep5RLIBCC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RCTXC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep:RSSP_GUARDC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep8RGOT_SSPC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m@prod_create_postC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit8fh_fp_okK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit<fh_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m@prod_create_stmtC5ARocqVerifyHarness?AgentSubmission4Spec7Harness=PRODUCER_SIZEC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_mAPROD_CREATE_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m<PPROD_CREATEC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps8raw_freeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface:rfree_postC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m>prod_free_stmtC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface;RFREE_STACKC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_iface_m:PPROD_FREE".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Section FuzzMalloc.
  Hypothesis MALLOC : rmalloc_stmt.

  Theorem fuzz_malloc_proof : fuzz_malloc_stmt.
Proof.
unfold fuzz_malloc_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP A0 NR.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold FUZZ_MALLOC_STACK, RMALLOC_STACK in LOS. atop_facts.
subst tp a0. rewrite errno_lit in ERR. unfold RERRNO in ERR.
unfold Harness.fuzz_malloc.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
assert (RP : forall m1, munch [(lo, bv_unsigned sp)] m m1 -> wmono usegs m m1 -> rheap_pres LB (bv_unsigned sp) m m1).
{ intros m1 MU1 WM1. eapply rheap_pres_of_munch; [exact MU1| exact WM1| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]].
  pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
destruct (0 <? n) eqn:N0.
- apply Z.ltb_lt in N0.
  apply implM_from_evt.
  carve_frame 16%nat ST.
  unfold PFUZZ_MALLOC. zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. lia. }
  zstep. apply evt_done.
  assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; lia| constructor]]).
  assert (AUX1 : rauxv_ok m0 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; lia| constructor]]).
  eapply implM_bind.
  { unfold rmalloc_stmt in MALLOC.
    eapply MALLOC with (lo := lo) (B := B) (n := n).
    all: try reflexivity. all: rewrite ?unsigned_lit by lia.
    all: first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | (unfold RMALLOC_STACK; lia)]. }
  cbv beta. intros r s' ms1 PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
  rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia.
  replace (ret_pc (Z_to_bv 64 0x21078)) with (Z_to_bv 64 0x21078) by (symmetry; rpc).
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [CB 8 (firstn 8 junk); C8 ra])
    by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
  destruct r as [p|].
  + destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    apply implM_ret.
    zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
    zstep. zstep. zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold fuzz_malloc_post.
    do 15 eexists. exists m2, errv1. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
    split; [eapply rheap_pres_trans; [eapply RP; [exact MU| exact WM]| eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]]|].
    split; [exact FAE|]. split; [exact SOE|]. exists A, junk2.
    split; [reflexivity|]. split; [exact BR|]. split; [exact HP2|]. split; [exact BLK| exact HEXP].
  + destruct RR as (-> & HP2).
    cbn beta iota. unfold Prog.new_handler.
    eapply implM_bind with (Q1 := fun _ _ _ => False); [apply implM_unr| intros e; destruct e].
- apply Z.ltb_ge in N0. assert (n = 0) by lia. subst n.
  apply implM_ret.
  carve_frame 16%nat ST.
  unfold PFUZZ_MALLOC. zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
  zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold fuzz_malloc_post.
  do 15 eexists. exists m0, errv. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|]. split; [rewrite errno_lit; exact ERR|].
  split; [eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; lia| constructor]]|].
  split; [eapply RP; [exact MU| exact WM]|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; lia| constructor]].
Qed.
End FuzzMalloc.

Section Create.
  Hypothesis FMALLOC : fuzz_malloc_stmt.

  Theorem prod_create_proof : prod_create_stmt.
Proof.
unfold prod_create_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold PROD_CREATE_STACK, FUZZ_MALLOC_STACK, RMALLOC_STACK in LOS. atop_facts.
subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
apply implM_from_evt.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
carve_frame 32%nat ST.
unfold PPROD_CREATE. do 4 zstep. zstep. zstep. zstep. zstep. apply evt_done.
assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
assert (AUX1 : rauxv_ok m0 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
eapply implM_post_evt.
{ unfold fuzz_malloc_stmt in FMALLOC.
eapply FMALLOC with (lo := lo) (B := B) (n := PRODUCER_SIZE); try reflexivity; unfold RATP, FUZZ_MALLOC_STACK, RMALLOC_STACK, PRODUCER_SIZE; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (227376 + -164) with 227212; exact ERR]. }
cbv beta. intros r s' ms1 PO.
destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x20eb4)) with (Z_to_bv 64 0x20eb4) by (symmetry; rpc).
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 (take 8 (take 16 (take 24 junk))); C8 s1; C8 s0; C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
clear FR ST MI ERR AUX1.
destruct r as [p|]; [| destruct RR as (RR & _); unfold PRODUCER_SIZE in RR; lia].
destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
assert (RA : 0 <= A < 2^64) by (atop_facts; lia).
unfold PRODUCER_SIZE in BLK. change (Z.to_nat 16) with 16%nat in BLK.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app] in BLK.
pose proof (munch_refl [(A, A + 16)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
assert (LA : Z.land A 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
zstep. if_cases KN; zify_cond KN. { exfalso. lia. }
zstep. zstep. if_cases KA; zify_cond KA. { exfalso. lia. }
zstep. zstep.
destruct (fh_transport s' [(p, A, PRODUCER_SIZE)] LB m2 m3 _ B (bv_unsigned sp + -32) HP2 MU2 WM2
ltac:(constructor; [right; exists (p, A, PRODUCER_SIZE); split; [left; reflexivity| unfold PRODUCER_SIZE; cbn; lia] | constructor]) ltac:(atop_facts; lia))
as (HP3 & AUX3 & _ & HPR23).
specialize (AUX3 AUX2).
zstep. zstep. zstep. zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold prod_create_post.
do 15 eexists. exists m3, errv1. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX3|].
split.
{ eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]]|].
{ pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]|].
eapply rheap_pres_weaken; [exact HPR23| lia| intros b Hb; exact Hb]. }
split; [exact FAE|]. split; [exact SOE|]. exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [exact BR|].
split; [exact HP3|]. split; [exact BLK| exact HEXP].
Qed.
End Create.

Section Free.
  Hypothesis FREE : rfree_stmt.

  (* [comment removed for export] *)
  Theorem prod_free_proof : prod_free_stmt.
Proof.
  unfold prod_free_stmt. intros until errv. intros HP IN AUX SPB ST LOA LOS ERR MI TP A0.
  apply implM_from_evt. unfold PPROD_FREE. zstep. apply evt_done.
  unfold rfree_stmt in FREE. eapply FREE; eassumption.
Qed.
End Free.
End CANSEC1.
