(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the string-end bound below USTACK_TOP; STACK_SPAN, the stack span the start state guarantees writable below sp; the recorded proofs of to_open_walk, failed_walk1, failed_walk2, z8_unsigned, map_z8_unsigned, oc_fail and 16 more replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_usage D_libiface D_clx.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_D_open () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List7map_extK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53Lib3Mem3mrdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z3addK4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool>negb_false_iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53Lib3Arr;u64arr_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState=Z_to_bv_plus0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K56Common8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec7b_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andK47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib3Arr<u64arr_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K53B236D_defs8RET_OPENC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237D_iface6e_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7MAIN_RAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv3Sem2w1C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout6a_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs<stderr_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC56Stdlib6ZArith6BinInt1Z3ltbC69OSSVerify5KrLib2K53Lib4Step@ro_cells_read_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_transMRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9e_fprintfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:GOT_STDERRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:STDERR_VARC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface;STDERR_FILEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface?FMT_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03C69OSSVerify5KrLib2K53B237D_iface6e_exitC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List6map_idc69OSSVerify5KrLib2K53B236D_open;z8_unsignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon:open_classC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3lebC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupK69OSSVerify5KrLib2K54Spec5Canon6oclass03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open?map_z8_unsignedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2K53Lib6NodesA8open_entC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbI69OSSVerify5KrLib2K54Spec5Canon6oclass00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K54Spec5Canon6oclass01C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathC4ELinuxProcessSemantics?LinuxProcessSem5State8path_maxK69OSSVerify5KrLib2K54Spec5Canon6oclass02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C69OSSVerify5KrLib2K54Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdC69OSSVerify5KrLib2K53B236D_defs4fds0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupc69OSSVerify5KrLib2K53B236D_open=alloc_fd_fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8argv_repC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3minC69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr<u64arr_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr05I47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib2K53B235D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit<u64arr_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC69OSSVerify5KrLib2K53B235D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib2K53B238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List6nth_okC69OSSVerify5KrLib2K53B236D_defs:path_slackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs6path_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs5STARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs4OPENC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs9sigma0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open<to_open_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53B238RT_iface8af_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx9CLX_munchC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open:argv_munchC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=nth_error_nthC69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7MAINCTXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:CREDIT_DRVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC46Stdlib5Lists4List2InC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC46Stdlib5Lists4List2tlC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib2K53B238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:errno_cellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs6FAILEDC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237D_iface:musl_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx?CLX_munch_errnoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open@main_frame_munchC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc69OSSVerify5KrLib2K53B236D_open@path_slack_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:drv_constsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7drv_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237D_iface9ssp_cellsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open<path_b_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open;nth1_argv_ZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open7oc_failC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityK47Corelib4Init5Logic2or02c69OSSVerify5KrLib2K53B236D_open<failed_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout<g_read_stageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237D_iface7GOT_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs<GOT_LLVMINITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7S_SHORTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs6S_OVERC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderC69OSSVerify5KrLib2K53B236D_defs6OPENEDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertc69OSSVerify5KrLib2K53B236D_open:oc_notfailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open<opened_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cps2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosC69OSSVerify5KrLib2K53B236D_defs4EXITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib2K54Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib2K53B236D_open<failed_walk1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B238RT_iface7fp_case02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6fp_fmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6fp_argC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6fp_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface;checked_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rng_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface<af_acc_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C69OSSVerify5KrLib2K53B238RT_iface7call_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx6CLX_ioC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236D_open<failed_walk2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib2K53B238RT_iface8so_linesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8drv_cellC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53B235D_clxIoutside_of_not_in_ranges'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx>io_ssp_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:t_emit_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS4cpsEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6fp_msgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53B238RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:D_libiface6LIB_FPC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma to_open_walk : forall (usp ap : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z) (ptrs : list word) (p1 : word),
  stk asegs m lo usp -> SEGTOP_A <= lo -> lo + 0x100000 <= usp -> usp mod 16 = 0 -> usp < 2^47 ->
  u64arr asegs m ap ptrs -> nth_error ptrs 1 = Some p1 -> usp < ap -> ap + 16 <= 2^47 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists m', ms' = entry_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 2) s1 p1 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                    p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_open m'
       /\ munch [(usp - 80, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ (exists junk, rw_cells asegs m' (usp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 MAIN_RA)])
       /\ stk asegs m' lo (usp - 80))
    (entry_st (Z_to_bv 64 MAIN_RA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 ap)
       a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a_main m).
Proof.
  intros until p1. intros ST SL LO U16 UT ARR Hp1 UA AT MI.
  unfold entry_st, a_main. pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 80%nat ST.
  do 12 step.
  if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    pose proof (u64arr_read asegs mf ap ptrs 1 p1 (wa (ap + 8)) ARR Hp1 ltac:(lia) ltac:(f_equal; lia)) as RD end.
  step. clear RD.
  do 3 step.
  apply evt_done. eexists. split.
  { unfold entry_st, RET_OPEN. reflexivity. }
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eexists; exact FR| exact ST].
Qed.

(* [comment removed for export] *)
Lemma failed_walk1 : forall (usp : Z) (gp s1 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  stderr_cells m -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xf9d74) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                          (Z_to_bv 64 2) s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_cannot_open) p1 a3 a4 a5 a6 a7
                          p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m))
    (MS (mkR (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 (-1))
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RET_OPEN) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros [SC1 SC2] MI. unfold GOT_STDERR, STDERR_VAR in SC1, SC2. unfold RET_OPEN.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. if_true.
  do 9 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma failed_walk2 : forall (usp : Z) (gp s1 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xf9da4) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                          (Z_to_bv 64 2) s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                          p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_exit m))
    (MS (mkR (Z_to_bv 64 0xf9d74) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 v
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf9d74) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma z8_unsigned : forall x : byte, Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma map_z8_unsigned : forall b : list byte, map (Z_to_bv 8) (map bv_unsigned b) = b.
Proof. intros b. rewrite map_map. erewrite map_ext; [apply map_id|]. intros x. apply z8_unsigned. Qed.

Lemma oc_fail : forall b fs, open_class (map bv_unsigned b) fs = OCFail -> open_ent b fs = None.
Proof.
  intros b fs H. unfold open_class in H. rewrite map_z8_unsigned in H. unfold open_ent.
  destruct (path_max <=? length b)%nat; [reflexivity|]. destruct b as [|x b]; [reflexivity|].
  destruct (path_eqb (x :: b) dot_path); [discriminate|]. destruct (fs_lookup fs (x :: b)); [discriminate| reflexivity].
Qed.

Lemma oc_notfail : forall b fs, open_class (map bv_unsigned b) fs <> OCFail -> exists ent, open_ent b fs = Some ent.
Proof.
  intros b fs H. unfold open_class in H. rewrite map_z8_unsigned in H. unfold open_ent.
  destruct (path_max <=? length b)%nat; [congruence|]. destruct b as [|x b]; [congruence|].
  destruct (path_eqb (x :: b) dot_path); [eauto|]. destruct (fs_lookup fs (x :: b)); [eauto| congruence].
Qed.

Lemma oc_dir : forall b fs, open_class (map bv_unsigned b) fs = OCDir -> open_ent b fs = Some FdDir.
Proof.
  intros b fs H. unfold open_class in H. rewrite map_z8_unsigned in H. unfold open_ent.
  destruct (path_max <=? length b)%nat; [discriminate|]. destruct b as [|x b]; [discriminate|].
  destruct (path_eqb (x :: b) dot_path); [reflexivity|]. destruct (fs_lookup fs (x :: b)); discriminate.
Qed.

Lemma oc_file : forall b fs data, open_class (map bv_unsigned b) fs = OCFile data ->
  open_ent b fs = Some (FdFile b (Z_to_bv 64 0)) /\ fs_lookup fs b = Some data.
Proof.
  intros b fs data H. unfold open_class in H. rewrite map_z8_unsigned in H. unfold open_ent.
  destruct (path_max <=? length b)%nat; [discriminate|]. destruct b as [|x b]; [discriminate|].
  destruct (path_eqb (x :: b) dot_path); [discriminate|]. destruct (fs_lookup fs (x :: b)) as [d|]; [|discriminate].
  injection H as ->. split; reflexivity.
Qed.

Lemma nth1_argv_Z : forall (argv : list (list byte)), nth 1 (argv_Z argv) [] = map bv_unsigned (nth 1 argv []).
Proof. intros [|x [|y l]]; reflexivity. Qed.

Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.

Lemma fds0_free3 : fd_lookup fds0 (alloc_fd fds0) = None.
Proof. rewrite alloc_fd_fds0. reflexivity. Qed.

(* [comment removed for export] *)

Section Open.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis OPC : open_contract RT.
Hypothesis OPR : open_refused_contract RT.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
Local Notation CLXm := (CLX_munch OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img).
Local Notation CLXe := (CLX_munch_errno OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img).

Lemma argv_munch : forall m m' ap W, argv_rep argvb m ap -> munch W m m' -> wmono asegs m m' ->
  (forall x, ap <= x < USTACK_TOP -> outside W x) -> argv_rep argvb m' ap.
Proof.
  intros m m' ap W (ptrs & ARR & L & STR & SLKS) MU WM HW. exists ptrs. split; [| split; [exact L| split]].
  - apply (u64arr_agree asegs m m' _ _ ARR); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW.
    pose proof (u64arr_bound asegs m ap ptrs ARR). rewrite L in *. split; [lia|].
    destruct (nth_error argvb 0) as [s0|] eqn:E0; [| apply nth_error_None in E0; lia].
    destruct (nth_error ptrs 0) as [p|] eqn:Ep; [| apply nth_error_None in Ep; lia].
    destruct (STR 0%nat s0 p E0 Ep) as (_ & P1 & P2). unfold USTACK_TOP in *. lia.
  - intros i s p Hs Hp. destruct (STR i s p Hs Hp) as (B & P1 & P2). split; [|split; assumption].
    apply (bytes_at_agree asegs m m' _ _ B). apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW.
    rewrite length_app in Hx. cbn in Hx. pose proof (u64arr_bound asegs m ap ptrs ARR). unfold USTACK_TOP in *. lia.
  - intros i s p Hs Hp. destruct (STR i s p Hs Hp) as (B & P1 & P2). destruct (SLKS i s p Hs Hp) as (sl & SL & SLM & SLB).
    exists sl. split; [| split; assumption].
    apply (bytes_at_agree asegs m m' _ _ SL). apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW.
    pose proof (u64arr_bound asegs m ap ptrs ARR). unfold USTACK_TOP in *. lia.
Qed.

Lemma path_slack_munch : forall m m' path W, path_slack argvb m path -> munch W m m' ->
  (forall x, path <= x < USTACK_TOP -> outside W x) -> path_slack argvb m' path.
Proof.
  intros m m' path W (sl & SL & SLM & SLB) MU HW. exists sl. split; [| split; assumption].
  apply (bytes_at_agree asegs m m' _ _ SL). apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW. unfold USTACK_TOP in *. lia.
Qed.

Lemma main_frame_munch : forall m m' usp c0 c1 c2 c3 c4 c5 c6 c7 W, main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 ->
  munch W m m' -> wmono asegs m m' -> (forall x, usp - 80 <= x < usp -> outside W x) -> main_frame m' usp c0 c1 c2 c3 c4 c5 c6 c7.
Proof.
  intros m m' usp c0 c1 c2 c3 c4 c5 c6 c7 W (junk & FR) MU WM HW. exists junk.
  apply (rw_cells_agree asegs m m' _ _ FR); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW.
  cbn [cells_size csize Nat.add] in Hx. lia.
Qed.

Theorem to_open_cps : Z.of_nat (length argvb) = 2 ->
  cps asegs (START RT OUT_rep ERR_rep XENV LIB argvb fs) (OPEN RT OUT_rep ERR_rep XENV LIB argvb fs).
Proof.
  intros HL T c HS Hk.
  destruct HS as (Σ & usp & ap & gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & HA & HART & HMI & HCLX & HARGV & HST & HSIG
                  & U16 & UA & ULO).
  pose proof HARGV as (ptrs & ARR & Lptrs & STR & SLKS).
  destruct (nth_error argvb 1) as [arg1|] eqn:Ha1; [| apply nth_error_None in Ha1; lia].
  destruct (nth_error ptrs 1) as [p1|] eqn:Hp1; [| apply nth_error_None in Hp1; lia].
  destruct (STR 1%nat arg1 p1 Ha1 Hp1) as (B1 & P1lo & P1hi).
  destruct (SLKS 1%nat arg1 p1 Ha1 Hp1) as (sl1 & SL1 & SLM1 & SLB1).
  pose proof (af_sp0_range RT AF Σ m HART) as SP0R.
  pose proof HSIG as (LV & FRS & CR & USP0 & SPW).
  pose proof (u64arr_bound asegs m ap ptrs ARR) as ARB.
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  rewrite HL in HA, P1lo. rewrite Lptrs in ARB. replace (Nat.min 2 (length argvb)) with 2%nat in ARB by lia.
  pose proof (to_open_walk usp ap gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ptrs p1) as W1.
  lazymatch type of W1 with _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms)
      by (intros ms <-; apply W1; try assumption; unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ fds0 fs _ _ W1') HA).
  intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 80) HART); [ul| |exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [|exact I]. intros Hin. apply Ha. left. ul. }
  exists Σ, usp, ap, (bv_unsigned p1), gp, t0, t1, t2, s1, a2, a3, a4, a5, a6, a7, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6.
  exists s0, s1, s2, s3, s4, s5, s6, s7, F, fc, m1.
  split; [rewrite Z_to_bv_bv_unsigned; exact Hc1'|].
  split.
  { split; [exact ART1|]. split; [exact MI1|].
    split; [apply (CLXm _ m m1 _ HCLX MU1 WM1); intros x Hx; cbn; split; [ul| exact I]|].
    split; [apply (argv_munch m m1 ap _ HARGV MU1 WM1); intros x Hx; cbn; split; [ul| exact I]|].
    split; [exact FR1|]. split; [exact ST1|]. ul. }
  split; [exact HSIG|].
  unfold path_slack, path_b. rewrite (nth_error_nth argvb 1 [] Ha1) in *. split; [| split; [ul| split; [ul|]]].
  - apply (bytes_at_agree asegs m m1 _ _ B1). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [| exact I].
    rewrite length_app in Hx. cbn in Hx. ul.
  - exists sl1. split; [| split; assumption].
    apply (bytes_at_agree asegs m m1 _ _ SL1). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [| exact I]. ul.
Qed.

Lemma path_b_facts : Z.of_nat (length argvb) = 2 ->
  ~ In (Z_to_bv 8 0) (path_b argvb) /\ path_has_slash (path_b argvb) = false /\ path_eqb (path_b argvb) dotdot_path = false
  /\ Z.of_nat (length (path_b argvb)) <= 131071.
Proof using VARGV.
  intros HL. destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5). unfold path_b.
  destruct argvb as [|x [|y l]]; cbn in HL; try lia. destruct l; cbn in HL; [|lia]. cbn [nth].
  inversion VA4 as [|? ? _ VA4']; subst. inversion VA4' as [|? ? NZ _]; subst.
  inversion VA3 as [|? ? _ VA3']; subst. inversion VA3' as [|? ? LN _]; subst.
  cbn [tl] in VA5. inversion VA5 as [|? ? (SL & DD) _]; subst. auto.
Qed.

(* [comment removed for export] *)
Lemma failed_intro : forall Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' (e : Z) c,
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m -> sigma0_ok RT Σ usp ->
  bytes_at asegs m path (path_b argvb ++ [Z_to_bv 8 0]) -> ap < path -> path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 9 ->
  path_slack argvb m path ->
  ASTA RT Σ (PMfd fds0 fs) (fun ms => ret_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1
         (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
      /\ musl_after RT Σ (bv_unsigned (Z_to_bv 64 (usp - 80))) (rt_sp0 RT Σ - STACK_SPAN) [(errno_cell (Z_to_bv 64 TP_A), errno_cell (Z_to_bv 64 TP_A) + 4)] m m'
      /\ rw_cells asegs m' (errno_cell (Z_to_bv 64 TP_A)) [C4 (Z_to_bv 64 e)]) c ->
  FAILED RT OUT_rep ERR_rep XENV LIB argvb fs c.
Proof using AF OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' e c
    (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) HSIG HB Hap Hhi HSLK Hc.
  destruct (ASTA_unpack RT Σ _ _ c Hc) as (ms & (RS & (ART1 & MI1 & WM1 & ST1 & MU1) & ER1) & Hc').
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (EE : errno_cell (Z_to_bv 64 TP_A) = ERRNO_A) by (unfold errno_cell, ERRNO_A, TP_A; rewrite unsigned_lit by lia; reflexivity).
  rewrite EU, EE in *.
  exists Σ, usp, ap, path, gp, s1, s3, s4, s5, s6, s7, s8, s9, s10, s11, c0, c1, c2, c3, c4, c5, c6, c7, m'.
  split; [eapply ASTA_conseq; [exact Hc'|]; intros ms1 <-; exact RS|].
  split.
  { split; [exact ART1|]. split; [exact MI1|].
    split; [apply (CLXe _ m m' _ CLX0 MU1 WM1);
            [intros x Hx Hne; cbn; split; [ul| split; [exact Hne| exact I]]| exists (Z_to_bv 64 e); exact ER1]|].
    split; [apply (argv_munch m m' ap _ ARGV0 MU1 WM1); intros x Hx; cbn;
            split; [ul| split; [unfold ERRNO_A, TP_A; ul| exact I]]|].
    split; [apply (main_frame_munch m m' usp _ _ _ _ _ _ _ _ _ FR0 MU1 WM1);
            intros x Hx; cbn; split; [lia| split; [unfold ERRNO_A, TP_A; ul| exact I]]|].
    split; [exact ST1|]. tauto. }
  split; [exact HSIG|]. split; [| split; [assumption| split; [assumption|]]].
  - apply (bytes_at_agree asegs m m' _ _ HB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn.
    rewrite length_app in Hx. cbn [length] in Hx. split; [ul| split; [unfold ERRNO_A, TP_A; ul| exact I]].
  - apply (path_slack_munch m m' path _ HSLK MU1). intros x Hx. cbn. split; [ul| split; [unfold ERRNO_A, TP_A; ul| exact I]].
Qed.

Theorem open_fail_cps : Z.of_nat (length argvb) = 2 -> open_class (nth 1 (argv_Z argvb) []) fs = OCFail ->
  cps asegs (OPEN RT OUT_rep ERR_rep XENV LIB argvb fs) (FAILED RT OUT_rep ERR_rep XENV LIB argvb fs).
Proof using AF AF_DRV OPR VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL HCL T c HO Hk.
  destruct HO as (Σ & usp & ap & path & gp & t0 & t1 & t2 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10
                  & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HCTX & HSIG & HB & Hap & Hhi & HSLK).
  pose proof HCTX as (ART0 & MI0 & (OUT0 & ERR0 & XE0 & LIB0 & (g0 & SG0) & ERRN0 & RS0 & LT0) & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (AF_DRV Σ m ART0) as DC0. pose proof DC0 as (SC0 & _). pose proof (drv_ssp m g0 DC0 SG0) as SSP0.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct (path_b_facts HL) as (NZ & NSL & NDD & LEN).
  rewrite nth1_argv_Z in HCL. apply oc_fail in HCL.
  apply (OPR Σ fds0 fs (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m path (path_b argvb) (rt_sp0 RT Σ - STACK_SPAN)); try reflexivity; try assumption;
    try (match goal with |- _ - STACK_WIN <= _ => unfold STACK_WIN; lia end).
  - rewrite unsigned_lit by ul. exact ST0.
  - rewrite unsigned_lit by ul. ul.
  - right. rewrite unsigned_lit by ul. lia.
  - intros c' (e & m' & He & Hc'). apply Hk.
    exact (failed_intro Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' e c' HCTX HSIG HB Hap Hhi HSLK Hc').
Qed.

(* [comment removed for export] *)
Lemma opened_intro : forall Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' ent c,
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m -> sigma0_ok RT Σ usp ->
  bytes_at asegs m path (path_b argvb ++ [Z_to_bv 8 0]) -> ap < path -> path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 9 ->
  open_ent (path_b argvb) fs = Some ent -> path_slack argvb m path ->
  ASTA RT Σ (PMfd (fd_insert fds0 (alloc_fd fds0) ent) fs)
    (fun ms => ret_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1
         (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 (alloc_fd fds0) m' ms
      /\ musl_after RT Σ (bv_unsigned (Z_to_bv 64 (usp - 80))) (rt_sp0 RT Σ - STACK_SPAN) [] m m') c ->
  OPENED RT OUT_rep ERR_rep XENV LIB argvb fs c.
Proof using AF OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' ent c
    (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) HSIG HB Hap Hhi HENT HSLK Hc.
  rewrite alloc_fd_fds0 in Hc.
  destruct (ASTA_unpack RT Σ _ _ c Hc) as (ms & (RS & (ART1 & MI1 & WM1 & ST1 & MU1)) & Hc').
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  rewrite EU in *.
  exists Σ, usp, ap, path, gp, s1, s3, s4, s5, s6, s7, s8, s9, s10, s11, c0, c1, c2, c3, c4, c5, c6, c7, m', ent.
  split; [eapply ASTA_conseq; [exact Hc'|]; intros ms1 <-; exact RS|].
  split.
  { split; [exact ART1|]. split; [exact MI1|].
    split; [apply (CLXm _ m m' _ CLX0 MU1 WM1);
            intros x Hx; cbn; split; [ul| exact I]|].
    split; [apply (argv_munch m m' ap _ ARGV0 MU1 WM1); intros x Hx; cbn; split; [ul| exact I]|].
    split; [apply (main_frame_munch m m' usp _ _ _ _ _ _ _ _ _ FR0 MU1 WM1); intros x Hx; cbn; split; [lia| exact I]|].
    split; [exact ST1|]. tauto. }
  split; [exact HSIG|]. split; [| split; [assumption| split; [assumption| split; [assumption|]]]].
  - apply (bytes_at_agree asegs m m' _ _ HB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn.
    rewrite length_app in Hx. cbn [length] in Hx. split; [ul| exact I].
  - apply (path_slack_munch m m' path _ HSLK MU1). intros x Hx. cbn. split; [ul| exact I].
Qed.

Theorem open_cps2 : Z.of_nat (length argvb) = 2 -> open_class (nth 1 (argv_Z argvb) []) fs <> OCFail ->
  cps2 asegs (OPEN RT OUT_rep ERR_rep XENV LIB argvb fs) (FAILED RT OUT_rep ERR_rep XENV LIB argvb fs) (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs).
Proof using AF AF_DRV OPC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL HCL T1 T2 c HO Hk1 Hk2.
  destruct HO as (Σ & usp & ap & path & gp & t0 & t1 & t2 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10
                  & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HCTX & HSIG & HB & Hap & Hhi & HSLK).
  pose proof HCTX as (ART0 & MI0 & (OUT0 & ERR0 & XE0 & LIB0 & (g0 & SG0) & ERRN0 & RS0 & LT0) & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (AF_DRV Σ m ART0) as DC0. pose proof DC0 as (SC0 & _). pose proof (drv_ssp m g0 DC0 SG0) as SSP0.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct (path_b_facts HL) as (NZ & NSL & NDD & LEN).
  rewrite nth1_argv_Z in HCL. destruct (oc_notfail _ _ HCL) as (ent & HENT).
  apply (OPC Σ fds0 fs (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m path (path_b argvb) (rt_sp0 RT Σ - STACK_SPAN) ent); try reflexivity; try assumption;
    try (match goal with |- _ - STACK_WIN <= _ => unfold STACK_WIN; lia end).
  - rewrite unsigned_lit by ul. exact ST0.
  - rewrite unsigned_lit by ul. ul.
  - right. exact ERRN0.
  - right. rewrite unsigned_lit by ul. lia.
  - intros c' (e & m' & He & Hc'). apply Hk1.
    exact (failed_intro Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' e c' HCTX HSIG HB Hap Hhi HSLK Hc').
  - intros c' (m' & Hc'). apply Hk2.
    exact (opened_intro Σ usp ap path gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c1 c2 c3 c4 c5 c6 c7 m m' ent c' HCTX HSIG HB Hap Hhi HENT HSLK Hc').
Qed.

(* [comment removed for export] *)
Theorem failed_cpsE : Z.of_nat (length argvb) = 2 ->
  cpsE asegs (FAILED RT OUT_rep ERR_rep XENV LIB argvb fs) (evw 2 (msg_cannot_open (nth 1 (argv_Z argvb) []))) (EXIT fs 2).
Proof using AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL T c HF Hk.
  destruct HF as (Σ & usp & ap & path & gp & s1 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & m & HA & HCTX & HSIG & HB & Hap & Hhi & HSLK).
  pose proof HCTX as (ART0 & MI0 & (OUT0 & ERR0 & XE0 & LIB0 & (g0 & SG0) & ERRN0 & RS0 & LT0) & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (AF_DRV Σ m ART0) as DC0. pose proof DC0 as (SC0 & _). pose proof (drv_ssp m g0 DC0 SG0) as SSP0.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct (path_b_facts HL) as (NZ & NSL & NDD & LEN).
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  rewrite nth1_argv_Z.
  replace (evw 2 (msg_cannot_open (map bv_unsigned (nth 1 argvb []))))
    with (evw 2 (fp_msg (FPcannot_open path (path_b argvb))) ++ evw 1 (so_buf stdout_init))
    by (cbn [fp_msg so_buf stdout_init]; rewrite app_nil_r; reflexivity).
  (* [comment removed for export] *)
  destruct (ASTA_unpack RT Σ _ _ c HA) as (ms0 & RS0' & HA').
  destruct RS0' as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & ->).
  rewrite (ret_pc_even RET_OPEN) in HA' by (unfold RET_OPEN; lia).
  pose proof (failed_walk1 usp gp s1 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
                F fc m SC0 MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ fds0 fs _ _ W1') HA').
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & <- & Hc1').
  eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
  apply (FPR Σ fds0 fs (Z_to_bv 64 0xf9d74) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_cannot_open) (Z_to_bv 64 path) a3 a4 a5 a6 a7 (Z_to_bv 64 path)
           s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (FPcannot_open path (path_b argvb)) STDERR_FILE lo);
    try reflexivity; try assumption.
  - intros a s Hs. cbn [fp_str] in Hs. injection Hs as <- <-. split; [exact HB|]. split; [exact NZ|].
    split; [lia|]. split; [split|].
    + intros _. split.
      * apply (af_acc_stack RT AF Σ m _ _ ART0); ul.
      * right. right. left. ul.
    + right. rewrite unsigned_lit by ul. lia.
    + split; [rewrite unsigned_lit by ul; lia| exact HSLK].
  - unfold call_ok. rewrite unsigned_lit by ul. split; [exact ST0|]. ul.
  - intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & (v & m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES2 & ERR2 & OUTP2) & Hc2').
    destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite unsigned_lit in ST2, PRES2 by ul.
    pose proof (OUTP2 stdout_init OUT0) as OUT2.
    assert (XE2 : XENV m2).
    { pose proof HCTX as (_ & _ & CLX0 & _).
      pose proof (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ _ m m2 _ _ _ CLX0 PRES2 WM2 OUT2 ERR2) as (_ & _ & XE2 & _). exact XE2. }
    (* [comment removed for export] *)
    pose proof (failed_walk2 usp gp s1 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7'
                  t3' t4' t5' t6' F' fc' m2 MI2) as W2.
    rewrite (ret_pc_even 0xf9d74) in Hc2' by lia.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ fds0 fs _ _ W2') Hc2').
    intros cf3 Hc3.
    destruct (ASTA_unpack RT Σ _ _ cf3 Hc3) as (ms3 & <- & Hc3').
    apply (EXC Σ fds0 fs (Z_to_bv 64 0xf9da4) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 2) s1
             (Z_to_bv 64 2) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc'
             m2 stdout_init 2 lo); try reflexivity; try assumption.
    + lia.
    + left. reflexivity.
    + unfold call_ok. rewrite unsigned_lit by ul. split; [exact ST2|]. ul.
    + pose proof HCTX as (_ & _ & CLX0 & _).
      eapply (io_ssp_pres_fp IO_FP _ _ _ m m2); [| io_ssp_tac AF_DRV| exact (AF_DRV _ _ ART2)| exact PRES2].
      intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). unfold drv_cell. right; left; exact Hx.
Qed.

End Open.
