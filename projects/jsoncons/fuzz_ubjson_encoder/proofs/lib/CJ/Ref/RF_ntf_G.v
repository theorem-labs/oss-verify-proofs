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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B MallocKit_A3 MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_ntf_A RF_ntf_E.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_ntf_G () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4landC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B35mw_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval02C13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K47Corelib4Init9Datatypes4list01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6g_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7area_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~K47Corelib4Init9Datatypes3nat02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3?meta_word_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_wordC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B7grp_delC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_G?rnest_call_postC13~~~C45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B3@meta_word_maplenC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BArmeta_slot_boundsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rgroup_concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>round_up_pg_geC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepBrreserved_disjointC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp4base7is_SomeK47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9conc_aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep<conc_region'C13~~~K46Stdlib9micromega7EnvRing5PExpr01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free<area_of_slotC13~~~C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free<page_off_modC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free:base16_modC13~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z2geC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_srliC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_srliC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep@rmrep_meta_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5oconcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C56Stdlib6ZArith6BinInt1Z7add_0_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep@rmrep_group_readC13~~~K47Corelib4Init9Datatypes4list02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepErmrep_area_check_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepErmrep_ctx_secret_readC13~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=bytes_at_readC13~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le2C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8le2_lohiC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RF_get_meta>rget_meta_postC13~~~K46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepBrsize_classes_readC13~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RF_get_meta>rget_meta_walkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_evenC13~~~C47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3zxbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAzext_extract_byteC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv3Sem4core01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMallocKit_B3Drmrep_group_hdr_zeroC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9del_groupC13~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms<PER_morphismC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsFtrans_co_impl_morphismC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C46Stdlib9micromega;ZifyClasses9and_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=mem_inv_storeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMallocKit_B3@rmrep_grp_del_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_andiC13~~~C45stdpp9bitvector;definitions7bv_wrapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_andiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rfree_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B>rfree_fp_stackC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B>rfree_fp_groupC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BIrpres_except_of_munch_covC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6zxb_b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec7evt_cutC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<g_active_idxC13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~I47Corelib4Init9Datatypes3nat00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~K47Corelib4Init9Datatypes4bool01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9META_SIZEC13~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~I47Corelib4Init5Logic4True00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsDiff_impl_subrelationI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_B8fm_factsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_A:rntf_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B5fm_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B=rntf_ret_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref8RF_ntf_A7rntf_fmC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RSSP_GUARDC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x9e624) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e39c) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
  let mr := get_meta_rec st g in
  let mr1 := get_meta_rec st g1 in
  let idx1 := Z.land b3 31 in
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
  (s_groups st) !! p = Some ghp ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  bytes_at rsegs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
  0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
  base1 = aadd p (- (UNIT * off16) - UNIT) ->
  (s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
  0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
  0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
  (s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
  idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
  (m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
  (48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
  (m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e5f8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
         AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B. pose_ceil.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
  pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).

  destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
  assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
  { rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
  rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
  pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
  destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
  assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hao : area_of g1 = a).
  { rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
  assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
  { rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
  assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
  (pose_ceil; unfold RCTX, AREA_HDR, META_SIZE, NSLOTS in *).
  assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.

  change (frozen (conc st p mod 16 = 0)) in P16m.
  change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
  clear HGm AAL RBAL RgBAL SpA BbA.
  destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.

  st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

  rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
    pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
    pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
    pose proof (rmrep_ctx_secret_read st mX MR) as RC;
    pose proof (bytes_at_read rsegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
    pose proof (bytes_at_read rsegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
    pose proof (bytes_at_read rsegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
  end.
  rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
  unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
  rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
  change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
  change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
  change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
  replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
  replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
  replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
  rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.

  st1.
  eapply evt_cut.
  { eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
            (m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
            (m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (c_secret (ctx st))).
    all: lazymatch goal with
         | |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
         | |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
         | |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
         | |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
         | |- ov_read_bytes _ _ (wa 963664) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
         | |- rw_cells _ _ (conc _ _) _ => exact MM
         | |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
         | |- _ => idtac
         end.
    all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
               | lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0x9e610)) with (Z_to_bv 64 0x9e610) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

  st1.
  unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
  st1.

  clear CH MM RG RA RC R4 R2.
  pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rw_cells_store_ok_at rsegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
  clear RWp.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) MR Hp UNK (length_le8 _)) as MR2
  end.
  rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
  apply (rmrep_grp_del_eq st _ g p) in MR2.

  st1. st1.
  apply evt_done. unfold rnest_call_post. do 14 eexists.
  split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
           cbv delta [mkR]. unfold RCTX. reflexivity. }
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + eapply rfree_fp_group; [exact Hp | lia]. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> fm_facts st g ->
  conc st g = conc st0 g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
      (MS (mkR (Z_to_bv 64 0x9e624) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e624) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose_ceil.
  st1. st1. st1.
  rewrite <- Hcg.
  eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
    first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | pose_ceil; lia].
Qed.
End CEIL_WRAP_1.

