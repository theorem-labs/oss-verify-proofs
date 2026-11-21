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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_free_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := (pose_ceil; unfold UNIT, IB in *); lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_free_A () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6LookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I35stdpp4gmap4gmap00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions;bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4zx32C13~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B35mw_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~K47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9land_onesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep@land_ldiff_distrC13~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~K47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4wr16C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8ticks_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~I47Corelib4Init9Datatypes4prod00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableK47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=rmrep_globalsC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A;rfhead_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepBrreserved_disjointC13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BArmeta_slot_boundsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=bytes_at_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_subC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_subC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C56Stdlib6ZArith6BinInt1Z3ltbK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge6zr_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridgeBinr64_unsigned_litC13~~~C46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K4ELinuxProcessSemantics5Riscv5Instr5instr06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3zxbC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAzext_extract_byteC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics5Riscv5Instr5instr08C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_sllwC13~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6w_sllwC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem>wr_at_store_okC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le1C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_1'C13~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep9rmrep_wr8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3wr8C13~~~C35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=mem_inv_storeC13~~~C46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemDbytes_at_write_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wr_at_writeC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C46Stdlib9micromega;ZifyClasses9and_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep<ticks_ok_wr8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le2C13~~~C45stdpp9bitvector;definitions:bv_extractC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_2'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:rmrep_wr16C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le2C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C45stdpp9bitvector;definitions8bv_swrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_addiwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7w_addiwC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_B8rfree_fpC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_BIrpres_except_of_munch_covC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MStateCZ_to_bv_bv_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTreeBrpres_except_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free8all_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RF_get_meta;sllw1_word'C13~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6zxb_b8C13~~~C46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z2geK47Corelib4Init9Datatypes4prod01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free3sxvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~I47Corelib7Numbers7BinNums1N00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:F_syscalls5rsegsC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<ref_reservedC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop03C46Stdlib9micromega8ZifyInst7Inj_Z_ZC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free8le1_neg1C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep4RCTXC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~C56Stdlib6ZArith6BinInt1Z3lebC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep<conc_region'C13~~~C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_mulC13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5m_mulC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_addC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A;rfree_head3C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le4C13~~~C46Stdlib5Lists4List;firstn_all2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@zext_extract_le4C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A7zx32_wzC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2IBC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5msize03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6g_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7area_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C56Stdlib6ZArith6BinInt1Z7testbitC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepArmrep_shadow_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_carveC13~~~C56Stdlib6ZArith6BinInt1Z9add_assocC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_8'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6W_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepDrmrep_transport_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RF_get_meta>rget_meta_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RF_get_meta>rget_meta_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_evenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3?meta_word_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3@meta_word_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3Bmeta_word_last_idxC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A=meta_word_sc2C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A<meta_word_pgC13~~~K46Stdlib9micromega5Tauto8GFormula01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame=disjoint_fromC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_B>rfree_fp_stackC13~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5FrameBbytes_at_transportC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt9RF_free_A;rfree_head2C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_andiC13~~~C45stdpp9bitvector;definitions7bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_andiC13~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool<andb_false_rC47Corelib4Init5Logic5proj2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRepBrsize_classes_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep@size_class_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4zx16C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@zext_extract_le2C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_slliC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_slliC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7zx16_wzC13~~~K47Corelib4Init5Logic2or01K4ELinuxProcessSemantics5Riscv5Instr5instr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5b_luiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_andC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7alu_andC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;land_pgmaskC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec7evt_cutC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cb_split_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_cb_splitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rfree_entryC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=RSIZE_CLASSESC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02".

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
  intros (LI & FB & SCR & ML).
  assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
  replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof.
  intros (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
  fun ms' => exists x1 x5 x6 x7 junk m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
                  (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0xecd3c) x5 x6 x7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9fd40) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rmrep st1 m'.

(* [comment removed for export] *)
Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
  stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 ->
  r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  0 <= rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fcf0) fc None m0 (seg_rom rsegs)).
Proof.
  intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
  pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (pose_ceil; unfold UNIT, IB in *).
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read rsegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.

  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }

  st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

  change (Z_to_bv 64 E) with (wa E).
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }

  st1. st1. st1. st1. st1. st1.
  rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).

  pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (SOK3 : store_ok rsegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
      by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
  st1.
  pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
  cbn [aadd snd] in MR2. fold po in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
      by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
  store_done.
  pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
    assert (SOK2 : store_ok rsegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
      by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
  st1.
  pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
  cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
      by (f_equal; unfold wa; f_equal; lia) end.
  store_done. clear MR2 TK2 HWr HWr2.

  st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
  replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
  st1.

  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact I].
      intros x Hx. right. right. exists (fst p), r.
      assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
      destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
  apply evt_done. unfold rfhead_post.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
  do 6 eexists.
  split; [reflexivity|].
  split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.

(* [comment removed for export] *)
Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
  stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 -> idx <= m_last_idx mr ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m0 (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fca8) fc None m0 (seg_rom rsegs)).
Proof.
  intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
         AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  (pose_ceil; unfold UNIT, IB in *).
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.

  st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
  replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
  fold rsv0.

  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  -
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| pose_ceil; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
  -
    destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read rsegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
    pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).

    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

    st1.
    rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| pose_ceil; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.

(* [comment removed for export] *)
Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo8 + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m -> mem_inv rsegs m -> ticks_ok st ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  (* [comment removed for export] *)
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
         AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl rsegs m) as WM.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (FB : fst base = fst p) by reflexivity.
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).

  revert BIG RB0r RE0.
  (pose_ceil; unfold rfree_entry, UNIT, IB in *). intros BIG RB0r RE0.

  st1. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 48%nat ST.
  st1. st1. st1. st1. st1. st1. st1.

  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; pose_ceil; lia) end.
  eapply evt_cut.
  { eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
    all: try eassumption. all: try lia. }
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0x9fc60)) with (Z_to_bv 64 0x9fc60) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
    destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (MW : mw_ok mr) by (unfold mw_ok; lia).
  pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
  pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (K2 : forall a4v a5v a6v, evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0x9fc60) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fca8) fc None mX (seg_rom rsegs))) end.
  { intros a4v a5v a6v.
    lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
    lazymatch type of MUs with munch ?W m ?mY =>
      assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
        by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
            cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
    subst rsv rsv0 E stride mr.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
      [exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
      | exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
      | intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
          (eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
      | ulia
      | exact RB0r
      | exact RE0
      | exact HCLR]. }

  st1. st1. st1. st1. fold idx. rewrite MW12.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0x9fc60) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
                a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fc8c) fc None mX (seg_rom rsegs))) end.
  { intros a2v a4v COND. specialize (SC48 COND).
    assert (STR : stride = 16 * size_class (m_sizeclass mr)).
    { unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }

    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
    replace (110528 + m_sizeclass mr * 2) with (110528 + 2 * m_sizeclass mr) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (RS' : ov_read_bytes rsegs mX (Z_to_bv 64 (110528 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
    { replace (Z_to_bv 64 (110528 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
      apply rsize_classes_read; [assumption| lia]. }
    pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    rewrite Egw. apply K2. }

  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply KS. left. exact Km.
  -
    st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + apply KS. right. exact Kl.
    +
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
      rewrite Egw. apply K2.
Qed.
End CEIL_WRAP_1.

