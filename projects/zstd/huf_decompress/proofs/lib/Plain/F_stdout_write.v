(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (rw_cells_recast, C4_low32, rw_cells_C4_eq and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_syscalls F_stdio_write StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_stdout_write () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib5Plain>F_stdout_write8C4_low32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write?rw_cells_recastC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z:land_assocK47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MonadX@implM_bind_assocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_writefnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure:implM_rdsoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=F_stdio_write@stdio_write_postC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write<stdout_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5Plain:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib5Plain>F_stdout_writeCstdout_writefn_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write6wfn_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBstdout_stdio_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write?rw_cells_C4_CB4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib3Lib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC59OSSVerify5KrLib3Lib8PropExec7b_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr06C59OSSVerify5KrLib3Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zx8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib3Lib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec8alu_andiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib7ZBridge;zr_land_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge:zr_mod_anyC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib5Plain>F_stdout_write@flags_byte_and64C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C59OSSVerify5KrLib3Lib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib3Lib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C59OSSVerify5KrLib3Lib8PropExec7w_addiwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib6Common:Stdio_pure:sx32_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC59OSSVerify5KrLib3Lib5Nodes4aregC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode>dec_plain_SomeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9efferr_ciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode7eff0_ciC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Lib7SysStepBunsigned_errno_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write>rw_cells_C4_eqC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write?rw_cells_CB4_C4C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure5boxedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5Plain=F_stdio_write@stdio_write_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep>apply_mem_noneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C59OSSVerify5KrLib3Lib7SysStep:nret_MSsvcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:Stdio_pure;implM_updsoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep9evt_ecallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@zext_extract_le1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_write;firstn1_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MonadX:implM_syskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MonadX:implM_retbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C59OSSVerify5KrLib3Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain>F_stdout_writeBSTDOUT_WRITE_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls7got_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:F_syscalls9ssp_guardC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=F_stdio_writeASTDIO_WRITE_DEPTHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:TIOCGWINSZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C59OSSVerify5KrLib5Plain:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
  file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].


(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells psegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells psegs m A (pre ++ C4 a :: post) -> rw_cells psegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells psegs m A (C4 v :: cs) -> rw_cells psegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.

Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells psegs m A (CB 4 (le4 v) :: cs) -> rw_cells psegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.

Section StdoutWrite.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

  (* [comment removed for export] *)
  Definition so_after (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  Lemma stdout_writefn_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells psegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at psegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at psegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (0x59000 <= lo) ->
      ssp_cells m canary -> mem_inv psegs m ->
      (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (bv_unsigned sp < 2^47) -> (S + zlength s <= 2^47) ->          (* [comment removed for export] *)
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      implM psegs (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI S0 Shi SP47 S47 SEPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. change psegs with psegs in GOT, GUARD. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
    assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
    unfold stdout_writefn. apply implM_rdso.
    unfold stdout_cells, wfn_of, lbf_of in *.
    destruct (so_first (get_so st)) eqn:FIRST.
    -
      apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      pose proof (wmono_refl psegs m) as WM.
      apply implM_sysk.
      change (bytes_at psegs m S (to_bytes s)) with (boxed (bytes_at psegs m S (to_bytes s))) in SRC.
      change (bytes_at psegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at psegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 9 step. rewrite firstn1_le4, zext_extract_le1. unfold zx8.
      step. step. step. fix_lit_store. step.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
      do 10 step. step_ecall.
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply sx32_small; lia).
      split. { at_node_red; split_spine; try reflexivity; try lia. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0. cbv iota.
      apply implM_updso.
      unfold implM. apply impl_from_evt. sys_nret.
      do 5 step.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      step. step.
      fix_lbf FC.
      step. apply evt_done.
      rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
      unfold stdout_stdio_write. apply (implM_rdso psegs get_so). rewrite get_set. cbn [so_buf].
      apply rw_cells_CB4_C4 in FC.
      eapply implM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH; lia | unfold GLOBALS_TOP; lia | unfold got_ssp; lia | unfold ssp_guard; lia
                   | unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
                   | destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
                   | right; unfold zlength in BUFL |- *; split; lia
                   | src_now SRC SEPS MU LSB ]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite !unsigned_lit in MU2, ST2 by lia.
      apply implM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].
      replace (ret_pc (Z_to_bv 64 0x20050)) with (Z_to_bv 64 0x20050 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct SSP2 as [GOT2 GUARD2]. change psegs with psegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport psegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
      step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + apply (munch_trans _ m m0 m2).
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + eapply wmono_trans; [exact WM | exact WM2].
      + split; [exact GOT2 | exact GUARD2].
      + rewrite ?set_set. reflexivity.
    -
      apply (implM_retb psegs). unfold stdout_stdio_write. apply (implM_rdso psegs get_so).
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      eapply implM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold GLOBALS_TOP; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
        all: first [ destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
                   | right; unfold zlength in BUFL |- *; split; lia ]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      apply implM_upd. apply evt_done. rewrite ?get_set.
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + rewrite ?set_set. reflexivity.
  Qed.
End StdoutWrite.
