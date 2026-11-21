(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of zal_ex, divu_lit, pfa_mid_spec replaced by plain proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk SysStep ITree.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_small R_m2s R_thread R_cache_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_classid R_prim_defs R_mmapfixed R_ensurefa R_ensurefa_B R_popfree.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_popfree_B () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z03C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_divuC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@bv_divu_unsignedC4ELinuxProcessSemantics5Riscv3Sem7mul_divK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5mulop06K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A23<R_cache_defs5SB_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs6RIS_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs5rinfoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass9ClassSizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239R_popfree9umap_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs4tsepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs6cstatsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs2rbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239R_popfree:pfa_cells1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs7ri_coreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238R_thread<thread_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs4T_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;R_popfree_B<pfa_mid_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_mmapfixed9rmap_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A23;R_mmapfixed:rmap_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239R_popfree9pfa_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs9mm_gcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG;R_sizeclass?ClassSize_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZBmul_le_mono_nonnegC69OSSVerify5KrLib2K53A23;R_prim_defs;round_fa_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs8round_faC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs@round_fa_alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53A23;R_prim_defs:shad_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;R_popfree_B6pfa_W1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs3boxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs5boxedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs5unboxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_mmapfixed;rmap_B_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_mmapfixed;rmap_B_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53A23;R_popfree_B6zal_exC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C69OSSVerify5KrLib2K53Lib8StepFast7sf_btgtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast:sf_transMRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;R_popfree_B3zalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs;poison_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238R_thread9tsd_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238R_thread:frame_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_prim_defs9gcts_specC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepFunsigned_Z_to_bv_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8load_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstc69OSSVerify5KrLib2K53A23;R_popfree_B8pfa_newcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06c69OSSVerify5KrLib2K53A23;R_popfree_B8divu_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2K53Lib5ITree4nretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr06C47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7amo_valC69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;img_hull_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs;img_hull_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235R_m2s>kHighShadowEndC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C69OSSVerify5KrLib2K53A238R_thread@g_tsd_key_initedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238R_thread9g_tsd_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238R_thread7pth_tsdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238R_threadBg_pthread_tsd_mainC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5amoop02C69OSSVerify5KrLib2K53A238R_thread3tpAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239R_popfree9pfa_retB1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239R_popfree>str_regiondataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<R_cache_defs4INSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_mmapfixed=mmap_ecall_pcC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr6awidth02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib2K53A23;R_popfree_B8pfa_retEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:R_ensurefa9efs_entryC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).

Definition pfa_retE : Z := 0xa6208.

(* [comment removed for export] *)
Definition pfa_newc (auser muser msz size : Z) : Z := ((muser + msz - auser) / size)%Z.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia. replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, (unsigned_lit b), unsigned_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Section PFAB.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition pfa_W1 (sp : word) (SB c R muser msz sa sn T : Z) : list (Z * Z) :=
  [(rb SB c + muser, rb SB c + muser + msz); (sa, sa + sn); (T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
   (bv_unsigned sp - 464, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Definition pfa_mid_post (ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R nfree mfa auser muser msz sa sn T TCX : Z) (mm0 md0 : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 pfa_retE) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1' t2' (Z_to_bv 64 R)
                  (Z_to_bv 64 (nfree + pfa_newc auser muser msz (ClassSize c))) (Z_to_bv 64 INST) (Z_to_bv 64 R)
                  (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 (nfree + pfa_newc auser muser msz (ClassSize c))) a4' a5' a6' a7'
                  (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 (pfa_newc auser muser msz (ClassSize c))) (Z_to_bv 64 (muser + msz - auser))
                  (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3' t4' t5' t6') F
             (Z_to_bv 64 efs_entry) fc None m' (seg_rom asegs)
    /\ munch (pfa_W1 sp SB c R muser msz sa sn T) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ pfa_frame m' sp ra s0o s1o s2o s3o s4o s5o s6o
    /\ rw_cells asegs m' (rb SB c + muser) [CB (Z.to_nat msz) (repeat (Z_to_bv 8 0) (Z.to_nat msz))]
    /\ rw_cells asegs m' sa [CB (Z.to_nat sn) (repeat (Z_to_bv 8 250) (Z.to_nat sn))]
    /\ ri_core m' R nfree mfa auser (muser + msz)
    /\ rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm0 + 1)); C8 (Z_to_bv 64 (bv_unsigned md0 + msz))]
    /\ (exists w, rw_cells asegs m' (T + 2792) [C8 w])
    /\ mm_gcells m' /\ thread_cells TCX T m' /\ PC m'
    /\ stk asegs m' lo (bv_unsigned sp - 64).

Lemma pfa_mid_spec : forall ra sp gp t0 t1 t2 a6 s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R k nfree mfa auser muser msz sa sn T TCX : Z)
    (mm0 md0 w0 : word) (shj : list byte) (lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (0 <= auser <= muser)%Z -> (muser < auser + k * ClassSize c)%Z -> (1 <= k <= 64)%Z -> (muser mod 2^18 = 0)%Z ->
  msz = umap_size auser muser k (ClassSize c) -> (muser + msz <= 0xE0000000)%Z ->
  (0 <= nfree < 2^32)%Z -> (0 <= mfa <= 2^29)%Z ->
  sa = shad (rb SB c + muser) -> sn = (msz / 8)%Z ->
  tsep ACEIL SB T TCX ->
  pfa_cells1 m sp ra s0o s1o s2o s3o s4o s5o s6o R (cstats T) (rb SB c) muser msz lo ->
  ri_core m R nfree mfa auser muser ->
  thread_cells TCX T m ->
  rw_cells asegs m (T + 2792) [C8 w0] ->
  rw_cells asegs m (T + 2872) [C8 mm0; C8 md0] ->
  rw_cells asegs m sa [CB (Z.to_nat sn) shj] ->
  PC m ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (pfa_mid_post ra sp gp (Z_to_bv 64 tpA) s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc SB c R nfree mfa
               auser muser msz sa sn T TCX mm0 md0 lo m)
    (nret (MSsvc (rmap_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned sp - 64)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6
                           (rb SB c + muser) msz (Z_to_bv 64 str_regiondata) (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST)
                           s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom asegs))
          (mkEffect (Z_to_bv 64 (rb SB c + muser)) [] [(Z_to_bv 64 (rb SB c + muser), Z_to_bv 64 msz)])).
Proof.
  intros until lo. intros HSB Hc ER Hau Htot Hk Hmual Emsz Hcap Hnf Hmfa Esa Esn HTS
    AC RC TC SAM ST8 SH PCm HLO HLOH HLO2 HSP MI.
  destruct HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  destruct AC as (FM & FR & ST & GC). unfold pfa_frame in FR.
  unfold ri_core in RC. unfold kHighShadowEnd, img_hull_lo, img_hull_hi, cstats in *. unfold rinfo, RIS_of in ER.
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hks : (k * ClassSize c <= 2^22)%Z).
  { assert (H1 : (k * ClassSize c <= 64 * 65536)%Z) by (apply Z.mul_le_mono_nonneg; lia). lia. }
  pose proof (round_fa_ge (auser + k * ClassSize c - muser) ltac:(lia)) as RG.
  pose proof (round_fa_aligned (auser + k * ClassSize c - muser)) as RA.
  unfold umap_size in Emsz. rewrite <- Emsz in RG, RA.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = (bv_unsigned sp - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  rewrite Esp in ST.
  assert (UM : (SB + 2^32 <= rb SB c + muser /\ rb SB c + muser + msz <= SB + 2^37)%Z) by (unfold rb; lia).
  assert (Hn8 : ((rb SB c + muser) mod 8 = 0 /\ msz mod 8 = 0)%Z).
  { unfold rb. split; Z.div_mod_to_equations; lia. }
  destruct (shad_range (rb SB c + muser) msz ltac:(lia) ltac:(lia) (proj1 Hn8) (proj2 Hn8) ltac:(lia)) as (SH1 & SH2 & SH3).
  rewrite <- Esa in SH1, SH2. rewrite <- Esn in SH2, SH3. unfold kHighShadowEnd in SH2.
  assert (Hmsz0 : (0 < msz)%Z) by lia. assert (Hsn : (0 < sn)%Z) by lia.
  pose proof (munch_refl (pfa_W1 sp SB c R muser msz sa sn T) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pfa_W1 in MU.
  pose proof GC as GC0. apply box in TC, GC0, PCm.
  apply box in Emsz, Esa, Esn, Hmual, HSB2, HT2, Hn8, HT5, HTCXI, SEPTT, OUTT, OUTTCX, SEPTCX, SEPT, SH3, RA, RG, Hks, Htot, Hk.
  (* [comment removed for export] *)
  pose proof (unbox _ SEPT) as SEPT'.
  eapply evt_cut; [eapply (rmap_B_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ _ _ _ _ (rb SB c + muser) msz _ lo) |
                   post_call asegs m].
  1:{ unfold img_hull_hi. lia. }
  1:{ lia. }
  1:{ lia. }
  1:{ exact FM. }
  1:{ exact GC. }
  all: rewrite ?Esp; try lia; try assumption.
  clear POST SEPT'.
  lazymatch type of MU with munch _ _ ?mc =>
    pose proof (munch_refl [(sa, sa + sn); (T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
                            (bv_unsigned sp - 464, bv_unsigned sp)]%Z mc) as MU2;
    pose proof (wmono_refl asegs mc) as WM2; rename mc into m1 end.
  apply box in PC0.
  unfold pfa_retB1.
  replace (ret_pc (Z_to_bv 64 680340)) with (Z_to_bv 64 680340) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  zhide.
  zstep. ifF.
  zstep.
  zstep. ifF.
  do 3 zstep.
  zstep.
  (* [comment removed for export] *)
  pose proof (unbox _ Esa) as Esa'. pose proof (unbox _ Esn) as Esn'. pose proof (unbox _ Hn8) as Hn8'.
  rewrite Esa', Esn' in SH.
  assert (PCm1 : PC m1).
  { pose proof (unbox _ HT5). apply (HPF m m1 _ (unbox _ PCm) MU WM). unfold img_hull_lo, img_hull_hi. cbn [disjoint_from]. lia. }
  pose proof (unbox _ OUTT) as OUTT'.
  eapply evt_cut; [eapply (HPS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (rb SB c + muser)%Z msz lo shj) | ].
  1-3: try unfold zal in *; lia. 1: unfold kHighShadowEnd; lia. 1: lia. 1: exact SH. 1: exact PCm1. 1: exact PC1.
  1-3: unfold kHighShadowEnd; rewrite ?Esp; lia. 1: assumption.
  intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
  rewrite <- Esa', <- Esn' in MUc, PO. clear Esa' Esn' Hn8' SH PCm1.
  lazymatch type of MUc with munch _ _ ?mc => transport_after_call asegs m1 mc MUc WMc; rename mc into m2 end.
  clear MUc WMc MI0 OUTT'.
  destruct PO as (SHN & ST1 & PCm2). clear PCm2.
  pose proof (munch_refl [(T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
                          (bv_unsigned sp - 464, bv_unsigned sp)]%Z m2) as MU3.
  pose proof (wmono_refl asegs m2) as WM3.
  apply box in SHN.
  replace (ret_pc (Z_to_bv 64 680368)) with (Z_to_bv 64 680368) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  zstep.
  destruct (unbox _ TC) as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  pose proof (unbox _ HT5) as HT5'.
  tr_from m MU WM KI. tr_from m MU WM K. tr_from m MU WM TS. tr_from m MU WM T0.
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ OUTTCX) as OUTTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from m MU WM TT.
  clear SEPTCX' OUTTCX' SEPTT'.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
  all: rewrite ?Esp in *; try lia; try assumption.
  clear KI K TS T0 TT.
  (* [comment removed for export] *)
  pose proof (unbox _ SEPT) as SEPT'.
  do 6 zstep.
  do 2 zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2792)) = true).
  { try unfold zal in *. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. pose proof (unbox _ HT2). lia. }
  amo_step AMO.
  do 4 zstep.
  do 8 zstep.
  rewrite divu_lit by lia. rewrite unsigned_lit by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace ((muser + msz + - auser) / ClassSize c)%Z with (pfa_newc auser muser msz (ClassSize c)) by (unfold pfa_newc; f_equal; lia).
  (* [comment removed for export] *)
  pose proof (unbox _ OUTT) as OUTT'.
  apply unbox in PC0, SHN.
  tr_from m1 MU2 WM2 PC0. tr_from m2 MU3 WM3 SHN.
  clear OUTT'.
  destruct (unbox _ TC) as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  destruct (unbox _ GC0) as (G1 & G2 & G3 & G4 & G5).
  pose proof (unbox _ HT5) as HT5'.
  tr_from m MU WM KI. tr_from m MU WM K. tr_from m MU WM TS. tr_from m MU WM T0.
  tr_from m MU WM G1. tr_from m MU WM G2. tr_from m MU WM G3. tr_from m MU WM G4. tr_from m MU WM G5.
  lazymatch type of MU with munch _ _ ?mc =>
    assert (PCf : PC mc) by (apply (HPF m mc _ (unbox _ PCm) MU WM); unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia) end.
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ OUTTCX) as OUTTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from m MU WM TT.
  unfold efs_entry, pfa_retE.
  finish.
  1:{ eexists. eassumption. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
Qed.
End PFAB.
