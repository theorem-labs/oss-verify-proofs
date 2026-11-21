(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; addresses and numbers. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_G.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_am_G () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_head_cellsC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;c_init_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_free_meta_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<c_avail_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_meta_alloc_shiftC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBc_avail_meta_areasC13~~~K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~K47Corelib4Init9Datatypes3nat02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5zerosC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~C45stdpp9bitvector;definitions;bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~I47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>ctx_tail_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~K47Corelib7Numbers7BinNums8positive03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums1Z01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RSSP_GUARDC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RMLOCKC13~~~K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z6moduloC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_sllC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_sllC13~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z;mul_pos_posC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2K4ELinuxProcessSemantics5Riscv5Instr5instr0BC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_mulC13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5m_mulC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmmap_entryC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5mulop01I47Corelib4Init5Logic4True00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_A9ram_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_A<ram_ret_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:canary_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C56Stdlib6ZArith6BinInt1Z9add_assocC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_foldC13~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6W_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepDrmrep_transport_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;stk_releaseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_A6ram_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_A<ram_fp_stackC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BIrpres_except_of_munch_covC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeBrpres_except_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_transC13~~~K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;RNEED_LOCKSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RPAGE_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep8RGOT_SSPC13~~~K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv3Sem2w1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w1_litC13~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC4ELinuxProcessSemantics5Riscv7Prelude4zextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_G8mm_ok_stC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_C4pgalC13~~~C47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep<conc_region'C13~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B@rmrep_ctx_frameWC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeArpres_except_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_am_A:ram_fp_ctxC13~~~K46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~K46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK4ELinuxProcessSemantics5Riscv5Instr5aluop07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e87c) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in C6.

  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.

  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
  let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x9e958) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
                                   (Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR SH n.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.

  st1. st1. st1.
  rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
  assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
  { rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
    change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }

  st1. st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv rsegs m ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e958) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
  (pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *).

  st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; pose_ceil; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
  rmrep st m -> mem_inv rsegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
  (s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
  0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
                      (Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ea1c) fc None m' (seg_rom rsegs)
        /\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
        /\ stk rsegs m' lo (bv_unsigned sp + -64)
        /\ rmrep (mm_ok_st st rid n) m')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e958) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  assert (AL : Z.land (x + 4096) 4095 = 0).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
  change (x mod 4096 = 0) with (pgal x) in XAL.
  (pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *).

  st1.
  assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.

  st1. st1. st1. st1. st1. st1.
  replace ((n + -1) * 1) with (n - 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.

  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
  { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
      rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
      lazymatch goal with H : rw_cells rsegs ?mX 963664 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.

  st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    - intros y Hy. apply ram_fp_stack. lia.
    - intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.
End CEIL_WRAP_1.

