(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (free_return, phaseDE); the zero-mapped stack depth; zstd/simple_decompress's proofs, with this binary's addresses; free_return and phaseDE use this unit's RSTAT and target-run post (atx_state), as zstd_frame_info's do). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface F_atexit RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3 RF_main_B4 RF_main_C.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_main_D () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MonadX@implM_bind_assocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;Stdio_iface@fwrite_diag_postC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_iface@emit_printf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5Plain=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctx6MFRAMEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain9RF_main_D5BASE2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctx2LOC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5Plain;RDriver_ctx5RSTATC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctx8sp_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01C59OSSVerify5KrLib5Plain>RMalloc_ifacePGRHEAP_block_range_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rblock_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5Plain9RF_main_C6RQEXITC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5Plain=RMalloc_iface:rfree_postC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Plain=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Startup_kit9envp_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem4argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C59OSSVerify5KrLib5Plain=RMalloc_ifaceCrheap_pres_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctx?RSTAT_heap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctxEstdout_file_heap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctxFstderr_file0_heap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=Harness_ifaceAstderr_file0_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctx;main_returnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib6Malloc<Malloc_iface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep6RERRNOC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00C59OSSVerify5KrLib5Plain=RMalloc_iface;RFREE_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Plain=RDriver_iface5PMAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface;PSTAGE2_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_C4RUN0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5Plain9RF_main_C3HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RF_main_A4BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC59OSSVerify5KrLib5Plain=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le16C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib6Common:Stdio_pure<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib7SysStepArw_cells_bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib4Spec4Prog3runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z9add_assocC59OSSVerify5KrLib5Plain=RDriver_iface@ptarget_run_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6zbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgreeCzbytes_map_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgreeBmap_unsigned_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib5Plain=RDriver_iface9pdrv_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface?pdrv_pres_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_iface7rin_ivsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface=ralloc_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula02C59OSSVerify5KrLib6Common8DrvAgree?rw_cells_magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8F_atexit9atx_stateC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5Plain;RDriver_ctx>RSTAT_drv_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RDriver_ctxEstderr_file0_drv_presC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z7mod_addC59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib3Lib7ZBridge=bv_lts_zero_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib5Plain=RDriver_ifaceHptarget_alloc_count_specC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuc59OSSVerify5KrLib5Plain9RF_main_D;free_returnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib5Plain9RF_main_C9main_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MonadX:implM_retbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;alloc_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9COUNT_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RDriver_ifaceAPTARGET_RUN_STACKC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5Plain=RDriver_iface;pstdout_ivsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT} {lx : launchT}.
Section D.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (J8 : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.
  Hypothesis TRUN : ptarget_run_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N p_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Notation RUN0' := (RUN0 sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition BASE2 (mm : mem) : Prop :=
    stk psegs mm LO' (usp0 + -128) /\ mem_inv psegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ stderr_file0 mm.

  (* [comment removed for export] *)
  Lemma free_return : forall (code : Z) (s : PState) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    RHEAP s [(bufp, A, cap)] mm -> FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells psegs mm RERRNO [C4 errv] ->
    implM psegs (raw_free bufp ;;; mret code) s RQEXIT
      (GST 0x12f24 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros P0 FR (ST & MI & RS & AUX & SE) SOF ERR.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF. unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 6144513) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 227376) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x12f2c)) with (Z_to_bv 64 0x12f2c) by (symmetry; rpc).
    cbn [lb_remove filter bptr_eqb fst snd] in HEAP3, HPR3.
    apply implM_ret. change (RQEXIT code s2) with (pat_exit code s2).
    eapply (main_return sp0 argv envp TID VSP HT code s2).
    - unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
    - unfold LO. first [exact ST3| replace (usp0 - 6144513) with (usp0 + -6144513) by lia; exact ST3].
    - eapply RSTAT_heap_pres; [exact HPR3| exact RS].
    - rewrite bptr_eqb_refl in HEAP3 || idtac. exact HEAP3.
    - rewrite SOE3. eapply stdout_file_heap_pres; [exact HPR3| exact SOF].
    - apply stderr_file0_file. eapply stderr_file0_heap_pres; [exact HPR3| exact SE].
    - exact MI3.
  Qed.

  (* [comment removed for export] *)
  Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0' bufp A cap DATA cw L cfg sc s ms ->
    implM psegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s RQEXIT ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R0.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & junk & errv
                    & -> & HD & PST0 & SO0 & BLK & FR & BA & ERR & FRM).
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. pose proof ERR as ERR0. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_tail. rewrite ECFG.
    unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { eapply TRUN with (lo := usp0 - 6144513) (AB := usp0) (p := bufp) (cap := cap);
        rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      - exact PST0.
      - left; reflexivity.
      - rewrite zbytes_map_unsigned. exact BLKB.
      - apply map_unsigned_range.
      - unfold zlength. rewrite length_map. lia.
      - lia.
      - lia.
      - unfold zlength. rewrite length_map. lia.
      - exact TR.
      - exact SE.
      - exact AUX.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - unfold PTARGET_RUN_STACK, HARNESS_STACK. lia.
      - unfold RATP. rewrite (unsigned_lit 227376) by lia. exact ERR.
      - exact MI.
      - exact FRM.
      - rewrite SO0. exact SOF.
      - reflexivity.
      - clear -SF. destruct SF as (_ & S16 & _). Z.div_mod_to_equations. lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold wz, zlength. rewrite length_map. reflexivity. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1
                    & -> & RR & MI1 & FRM1 & ST1 & ERR1 & AUX1 & DP & P1 & SOF1 & AX1).      (* [comment removed for export] *)
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
    unfold RATP in ERR1. rewrite ?(unsigned_lit 227376) in ERR1 by lia.
    replace (ret_pc (Z_to_bv 64 0x12ea4)) with (Z_to_bv 64 0x12ea4) by (symmetry; rpc).
    pose proof (pdrv_pres_agree _ _ _ _ DP) as AG.
    apply (rw_cells_magree psegs _ _ _ _ _ AG) in FR.
    2:{ intros a Ha. cbn in Ha. split; [left; lia|]. unfold pstdout_ivs, PINIT_FLAG, PAEF_INCB, PATX. cbn. lia. }
    assert (RS1 : RSTAT TID m1) by (eapply RSTAT_drv_pres; [exact DP| exact RS| exists true; exact AX1]).
    assert (SE1 : stderr_file0 m1) by (eapply stderr_file0_drv_pres; [exact DP| exact SE]).
    assert (BA2 : BASE2 m1) by (split; [exact ST1| split; [exact MI1| split; [exact RS1| split; [exact AUX1| exact SE1]]]]).
    clear AG DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    - (* [comment removed for export] *)
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 RQEXIT msx) end.
      apply implM_bind_assoc. eapply implM_bind; [apply ptarget_alloc_count_spec|].
      cbv beta. intros n s2 ms2 (-> & -> & ->). apply implM_retb.
      replace (ret_pc (Z_to_bv 64 0x12eb4)) with (Z_to_bv 64 0x12eb4) by (symmetry; rpc).
      unfold COUNT_MAX. change (if 0 <? 251 then 0 else 251) with 0.
      unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 RQEXIT msx) end.
      eapply free_return; [exact P1| exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
    - (* [comment removed for export] *)
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implM_retb.
      unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. zstep.
      apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1 RQEXIT msx) end.
      eapply free_return; [exact P1| exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
  Qed.
End D.
End CANSEC1.
