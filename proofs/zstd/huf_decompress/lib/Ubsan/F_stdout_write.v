(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import F_syscalls F_stdio_write StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_stdout_write () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib3MemAZ_to_le_bytes_modC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells<cells_wf_appC47Corelib4Init9Datatypes3appc5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write8C4_low32C5ARocqVerifyHarness?AgentSubmission3Lib5Cells?cells_bytes_appC47Corelib4Init3Nat3addC5ARocqVerifyHarness?AgentSubmission3Lib5Cells>cells_size_appc5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write?rw_cells_recastK47Corelib4Init9Datatypes4list02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C47Corelib4Init5Logic5proj2I47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z:land_assocK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec5Monad5implMC5ARocqVerifyHarness?AgentSubmission3Lib6MonadX@implM_bind_assocC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio>stdout_writefnC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure:implM_rdsoC5ARocqVerifyHarness?AgentSubmission5Ubsan=F_stdio_write@stdio_write_postC47Corelib4Init9Datatypes3fstC5ARocqVerifyHarness?AgentSubmission3Lib5ITree4implC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep=impl_from_evtC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5epostK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9so_activec5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write<stdout_cellsC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio8to_bytesC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5Ubsan:StdioFiles9ssp_cellsC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addc5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_writeCstdout_writefn_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRc5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write6wfn_ofK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib3Mem>bytes_at_boundC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio8so_firstC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio6so_bufC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9so_lbf_nlC5ARocqVerifyHarness?AgentSubmission4Spec5Stdio6upd_soK5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node06C5ARocqVerifyHarness?AgentSubmission4Spec5Monad4msysC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4munrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5mbindC5ARocqVerifyHarness?AgentSubmission4Spec5Monad4mretC5ARocqVerifyHarness?AgentSubmission4Spec5StdioBstdout_stdio_writeC5ARocqVerifyHarness?AgentSubmission5Ubsan:StdioFiles:file_cellsI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01c5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write?rw_cells_C4_CB4C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib5Nodes7at_nodeC5ARocqVerifyHarness?AgentSubmission3Lib6Decode9dec_ioctlK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib5ITree4nretK47Corelib7Numbers7BinNums1Z03K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC56Stdlib6ZArith6BinInt1Z9add_assocK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeC47Corelib5Lists7ListDef6firstnK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_cb_splitC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zx8K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_andiC45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_andiI47Corelib4Init5Logic2or00K4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;zr_land_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqc5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write@flags_byte_and64C47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_luiC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5b_luiK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure:sx32_smallC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib6MState5MSsvcC4ELinuxProcessSemantics5Riscv7Prelude4tgetK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4aregC5ARocqVerifyHarness?AgentSubmission3Lib6Decode>dec_plain_SomeC5ARocqVerifyHarness?AgentSubmission3Lib6Decode9efferr_ciC5ARocqVerifyHarness?AgentSubmission3Lib6Decode7eff0_ciI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission3Lib7SysStepBunsigned_errno_retC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'c5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write>rw_cells_C4_eqK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdio_writeK5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st01c5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write?rw_cells_CB4_C4K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_nilC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure5boxedK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5Ubsan=F_stdio_write@stdio_write_specC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;stk_releaseC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneC5ARocqVerifyHarness?AgentSubmission4Spec5Monad9implM_updC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep>apply_mem_noneK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C5ARocqVerifyHarness?AgentSubmission3Lib7SysStep:nret_MSsvcC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure;implM_updsoC5ARocqVerifyHarness?AgentSubmission3Lib7SysStep9evt_ecallC5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le1c5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_write;firstn1_le4C5ARocqVerifyHarness?AgentSubmission3Lib6MonadX:implM_syskC5ARocqVerifyHarness?AgentSubmission3Lib6MonadX:implM_retbC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK46Stdlib9micromega7EnvRing5PExpr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission4Spec5Monad:implM_bindc5ARocqVerifyHarness?AgentSubmission5Ubsan>F_stdout_writeBSTDOUT_WRITE_DEPTHC5ARocqVerifyHarness?AgentSubmission5Ubsan:F_syscalls7got_sspC5ARocqVerifyHarness?AgentSubmission5Ubsan:F_syscalls9ssp_guardK47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC5ARocqVerifyHarness?AgentSubmission3Lib5ITree4respI5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00C5ARocqVerifyHarness?AgentSubmission5Ubsan=F_stdio_writeASTDIO_WRITE_DEPTHI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00I5ARocqVerifyHarness?AgentSubmission3Lib6Decode4sret00C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio:TIOCGWINSZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission5Ubsan:StdioFiles;GLOBALS_TOPI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00".
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
  rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells usegs m A cs'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01Hh11Ah22Ebh32Esh42Hbh52Hwh63Hwfh74Hwf'h82csh93cs'h:1lh;1mh<1np;1p;4p;3p;6p10000p4p7210g000\R0p4p710p8g001:j12Tg001_j1>Tg002=j1:Tg002`j1?Tg003Bj1=Tg003bj49Tg004Xj48Tg005Oj10Tg006Hj15Tg006hj46Tg007Zj13Tg008Qj11Tg009Kj34Tg009ej47TP0j6<Tg00:Zj4;Tg00;5#2#2#2R0#2#2#2#>#:%>0#:R0#?[g00;Zg00<8#=R1g00<mR2f3R3f2R4f1R5C9g00=bR6P2f4R7P3P4C8P2P7P3%04#5C6%34%=0R0%13%1734g00>=R8%07f5R9#034P2f8R:f7R;P9C9[[[f0R<P2f6R=P9P7C8P6%39P2P;P=%19C7P2P:P;%0=#5C6%3=%1;%1:R=540%0:f9R:#0R9548P2f<R6f;R>P:C9[[[[P<%3;P2f:R;P:P=C7P2P>P;%59C6%3:%1;%1>540%0>%06R>548P2f?R;f>R:P6C8P2P;P:%5>C6%36P2P;P:%16R6C7P4P0f=R4#1P2f@R:P;P<C7X:0P7P6P5E<C;P8%04P2P:P;%5<C6X<8P3P>P<E<C;W3W2W7W5W4W6P5P<O2n2001000000120000000W0P5P<O2n2001000000120000000W0X91W8W1W;o"). Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01lh11Eh27__arithh34__ffh48__varmaph55__with61ah71bh81zp;1p;2p;3p;6p;4p;7g001:j11Tg001_j1BTg002=j1<Tg00>\j23Tg00?Fj16Tg00?dj2MTg00@Aj24Tg009Kj30Tg003Bj1=Tg00@aj15Tg00A@j22Tg00B=j29Tg000\j6CTg00BWj1PTg00C7j1OTg00CUj1NTg00D3j1LTg00D^j27Tg00EAj3KTg00Edj4JTg00FOj7ITg00G3j2HTg00GUj2GTg00HAj3FTg00H`j4ETg00IRj2@Tg00Ioj2;Tg006Hj1DTg00JKj4:Tg00KIj6?Tg00Kej1>Tg00LUj18Tg00MJj1ATg00;5#1R0#1R1#1R2#1#1R3#1#BR4#<R5g00;ZR6f1R7,34R8%60%63R3'MR0'4R9f0R:,34/4030%B2#<#=R;g00N?#5#5#5#5R<f2R=,34R>/40R?'2R@12<>RA90;:X0;P;12<9RBf3,34/40,2<=0;:X0;P6P912<:=0;@X8619;BP?P:EC12<8P<P8P3g00N^R8#P%=8%O6%N6%L6R8g00OJg00OiR?P?g00PIR?P6%62R2,76%61R1,765K6g00Pi1763CJg00QPFI1H8?P:P=g00R0R?g00RPR8'91G:==0?8dg00S0=F67CEb3b4b51@21/;3P:b2%D<,@2/;3eR2C:E?PAP<P>P3P2C:E?%>=%>750;e%8=#A%87#A50;eW1X75W6o"). Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells usegs m A (pre ++ C4 a :: post) -> rw_cells usegs m A (pre ++ C4 b :: post).
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01ah11bh21Hh31lh43Hwfh51nh61Ah71Eh82H1h92H2h:2_Hh;3_H0h<1mh=4posth>3prep;1p;2p;3p;4p;6p;8g001:j18Tg001_j1LTg002=j1DTg002`j1OTg003Bj1KTg00>\j2ITg00?Fj1GTg00?dj2STg00@Aj2BTg009Kj36Tg00LUj12Tg003bj4MTg004Xj4JTg005Oj14Tg006Hj1?Tg006hj4>Tg007Zj10Tg008Qj11Tg009ej4FTg00=bR0j2;Tg00SNj2RTg00:Zj4QTg00TIj33Tg00MJj1HTg00B=j2ATg00Tfj3PTg000\j6:Tg00Uhj2@Tg00Vfj2<Tg00W=j2ETg00X:j8NTg00YCj3=Tg00<8R1f2R2f1R3f0R45=133p=5A=134p=7A3134p=9%23==14p=Cg00;5#8R5#8#8R6#8#8R7#8#LR8#DR9%L6#DR6#O[g00;ZR:%K1R11I82%G5%G7'SR7'B1I83/B756:g00<mR:f6R7f5R8f4R5f3R;#2R<;53CMf7R=P7%25R>/72R?,98R@17<2RA,98RBP4P0P:P=P7P@CJP:P=P7%4@RC#?C>17>;RD,97#0P4P:f9REf8RF%27=5=5CJP0%2==5F8RG#0P:f:RHPE%1GCFP:f;RGPH%2FRI=5E7#4#?C>A5HI=#0[P4%2E=5H=#0P:f=R=f<RI%2H=5GF#1CFP:f>R:P=%2G=5IE#4#?C>P01934#0%02RI%03RE';RF[RH%04,;E1923#0RE[RJ%0;/;I\E1R34REP3n2001000000120000000X11X01PH^11^01P4P:1C=GRGP;O3%0:%0G';P0PHPJ19;2#0\FPEP4n2001000000120000000X11X01PJ^11^01P4f@RJ1C:=P0%0Jf?#2R0/7=#0fAR=#0170:#0';P3fBR0#0%20R0/7J#0fD#0170=#0P3P4CQW9W8P3P4O2n2001000000120000000O3b2b4b2W;W:W4P3P4O2n2001000000121000000W2P3P4O2n2001000000121000000%K6R0%18R=%1A536RJ%28=57;R:#19604X30P0%1?936=RE%17RF%1D536=604X30P0%H<R<%H>R>%1;RH536936FA364H936F560X30%12936<936=,A0P>AP5;3E:A60JEe%1@1@8?E:%1B1@8AE:g00>=R@%48RE%4A'<%4:96@4X5@P@%4?,<ERE%47%4D'<=6@4X5@1A@EPC1E8?E:%4B1E8AE:GNW2W7X=1X19X09W>W6W<o"). Qed.
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
  rw_cells usegs m A (C4 v :: cs) -> rw_cells usegs m A (CB 4 (le4 v) :: cs).
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01Hh11Ah21Bh31Rh41Wh52csh61mh71vp;1p;4p;2p;3g001:j11Tg001_j1ATg002=j1?Tg002`j1BTg003Bj1HTg003bj49Tg004Xj4=Tg005Oj13Tg006Hj12Tg006hj45Tg00@aj14Tg00Kej17Tg00Ycj2>Tg007Zj16Tg008Qj1:Tg009ej4<Tg00ZXj2GTg009Kj3FTg00[8j1ETg00[oj3DTg00:Zj48Tg00LUj1CTg00YCj3@Tg00<8R0f1R1#Cf0R23@p=0A@012p=;g00;5#1#1#1R3#1#1#1#A#?R4%A3#?R3#B[g00;Z%H0g00<mR0f3R5f2R61012C9g00=bR7P0f4R8P51061R9C=P0P8P5%39#2C5P0f5R9P8g00N?#4#4#4#4R:%75'>/;6C9P2P0f6R;P91085C=P71098R8#6P0f7R7P;%:8C<P0f8R8P710;9#3#2C5P0f9R9P8%77,>:/;;C9[P2107;#6P0f:R;P91087#:C<P0f;R7P;1098#3#2C5P0f<R8P7%7;R5,>:/;9R<C=P0P8P7%3<#2C5%6<R=P0P8P7%:<C<g00>=1G35;F:%69R9%E;g00\J?D96C8P=eP1C8P2C8W3W2W4P1P2O2n2001000000120000000W0P1P2O2n2001000000120000000W0W5X74W1W6o"). Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01vp;1p;2g001:j10Tg001_j12Tg002=j11Tg003Bj13Tg00\fj15Tg00B=j24Tg00;5#0#0#0R0#0#0#0#2#1%20#1#3f0#5'4W0o"). Qed.

Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01zh11Hh27__arithh34__ffh48__varmaph55__with65flagsp;1p;2p;6p;4p;7p;3g001:j11Tg001_j1MTg002=j1ATg00>\j29Tg00?Fj15Tg00]Vj20Tg00^4j1@Tg00?dj2?Tg00@Aj24Tg00B=j26Tg000\j62Tg00BWj1=Tg003Bj1LTg00C7j1KTg00CUj1JTg00D3j1ITg00D^j2;Tg00Edj4HTg00FOj7GTg00G3j2FTg00GUj2BTg009Kj3:Tg00HAj3CTg00H`j4DTg00Ioj2ETg00^Rj37Tg00_5j28Tg00_Xj3>Tg00KIj6<Tg00;ZR0f0R1g00S0R23:p=3g00;5#1R3#1#1R4#1#1#1R5#MR6#A1961%55R5'0#3P0f1R7,96R6%54R4#@R8'0R91015#3X00R:P01086R;P:P01065R:,08R<%31X00R=P010:8R>P=P0%53/?4R3,4:P=P0P21413#3X001602P:P1E2P>g00N^R>#=%L>%K0%J0%I0R>g00OJg00OiR=P=g00PIR=P01;02g00Pi1;04CHg00QPFG1F>=P1f2R=g00R0R>g00RPR?'61B1==:>?dAC027CDb3b4b51E24P1b2R197:4E2P<188:E210;5A>865E<P91868E21463A7641E<W1W6o"). Qed.

Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells usegs m A (CB 4 (le4 v) :: cs) -> rw_cells usegs m A (C4 v :: cs).
Proof.
ltac2:(KReplay.run1 (kr_t_F_stdout_write ()) [] "h01Hh11Ah21Bh31Rh41Wh52csh61mh71vp;1p;4p;2p;3g001:j11Tg001_j1ATg002=j1>Tg002`j1BTg003Bj1GTg00@aj16Tg003bj4:Tg004Xj48Tg005Oj14Tg006Hj12Tg006hj43Tg00LUj17Tg007Zj15Tg008Qj19Tg009ej4;Tg00Kej1@Tg00ZXj2FTg009Kj3ETg00[oj3DTg00:Zj4<Tg00Ycj2CTg00YCj3?Tg00<8R0f2R1f1R2#@'Cf0R33?p=0A?023p==g00;5#1#1#1R4#1#1#1#A#>R5%A4#>R4#B[g00;Z%G0g00<mR0f3R6P1g00N?#6#6#6#6R7?023C:g00=bR8P0f4R9P6A0712R:C8P0P9P6%4:#2C3P0f5R:P9%76/=1C:P3P0f6R;P:A0796C8P8A07:9R9#5P0f7R8P;%99C;P0f8R9P8A07;:#4#2C3P0f9R:P9%78/=;C:[P3A078;#5P0f:R;P:A0798#9C;P0f;R8P;A07:9#4#2C3P0f<R9P8%7;/=:R6C8P0P9P8%46#2C3%56R<P0P9P8%96C;g00\J%5:R:g00`<g00>=%@;,F4;E7?D:1C<P<eP2C<P3C<W3W2W4P2P3O2n2001000000120000000W0P2P3O2n2001000000120000000W0W5X75W1W6o"). Qed.

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
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  Lemma stdout_writefn_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells usegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at usegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at usegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (0x5d000 <= lo) ->
      ssp_cells m canary -> mem_inv usegs m ->
      (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (bv_unsigned sp < 2^47) -> (S + zlength s <= 2^47) ->          (* [comment removed for export] *)
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      implM usegs (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom usegs)).
  Proof.
    intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI S0 Shi SP47 S47 SEPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
    assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
    unfold stdout_writefn. apply implM_rdso.
    unfold stdout_cells, wfn_of, lbf_of in *.
    destruct (so_first (get_so st)) eqn:FIRST.
    -
      apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      pose proof (wmono_refl usegs m) as WM.
      apply implM_sysk.
      change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
      change (bytes_at usegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at usegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
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
      unfold stdout_stdio_write. apply (implM_rdso usegs get_so). rewrite get_set. cbn [so_buf].
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
      replace (ret_pc (Z_to_bv 64 0x240cc)) with (Z_to_bv 64 0x240cc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct SSP2 as [GOT2 GUARD2]. change usegs with usegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport usegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
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
      apply (implM_retb usegs). unfold stdout_stdio_write. apply (implM_rdso usegs get_so).
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
