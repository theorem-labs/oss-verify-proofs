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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_free_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_free_C () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~K47Corelib4Init9Datatypes4list01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:munch_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame:wmono_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_C:rffin_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell04C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:canary_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8alu_addiC13~~~C47Corelib4Init5Logic8eq_ind_rI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7v_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepFunsigned_Z_to_bv_add_rC13~~~C45stdpp9bitvector;definitions9bv_concatC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7b_auipcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RF_get_meta<runlock_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RF_get_meta<runlock_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_evenC13~~~C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells6cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8load_u64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells5csizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step=wa_of_Z_to_bvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@rw_cells_read_atC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_foldC13~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6W_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepDrmrep_transport_highC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;stk_releaseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic9False_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec7evt_cutC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem4core01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;RNEED_LOCKSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RPAGE_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep8RGOT_SSPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RSSP_GUARDC13~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RATPC13~~~K47Corelib4Init9Datatypes3nat01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RMLOCKC13~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses>impl_ReflexiveK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv3Sem2w1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w1_litC13~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_C:rfmun_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem4sx32C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le4C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem@sext_extract_le4C13~~~K46Stdlib9micromega5Tauto8GFormula03K4ELinuxProcessSemantics5Riscv5Instr5msize03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmunmap_entryC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rrepfootC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:rarea_concC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepBrreserved_disjointC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>round_up_pg_geC13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rgroup_concC13~~~C35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K46Stdlib9micromega5Tauto8GFormula06I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I47Corelib7Numbers7BinNums1N00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~K47Corelib4Init5Logic4True01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_CErerrno_avoids_repfootC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B=ivs_avoid_nilC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B>ivs_avoid_consC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_BGrmrep_transport_unownedC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDrw_cells_store_ok_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>store_bytes_4'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_boundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepArw_cells_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDmem_inv_store_cbytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cell_updC13~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem:length_le4C13~~~C46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step>rw_cells_frameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame9stk_writeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref9RF_free_CKrmrep_transport_frame_errnoC13~~~C47Corelib4Init9Datatypes3appC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free>rw_cells_congrC13~~~". Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

#[using="Type"] Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt rsegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e234) fc None m (seg_rom rsegs)).
Proof.
  intros until errv. intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  (pose_ceil; unfold RMLOCK, RNEED_LOCKS, RATP in *). subst tp.
  rewrite (unsigned_lit 831552) in ERR by lia. change (831552 + -164) with 831388 in ERR.

  st1. st1. st1. st1.

  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x9e248)) with (Z_to_bv 64 0x9e248) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 831552) by lia. change (831552 + -164) with 831388. exact ERR.
Qed.

(* [comment removed for export] *)
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x9e264) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

#[using="Type"] Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv rsegs m -> 0 < len < 2^64 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt rsegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e234) fc None m (seg_rom rsegs)).
Proof.
  intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  (pose_ceil; unfold RMLOCK, RNEED_LOCKS, RATP in *). subst tp.
  rewrite (unsigned_lit 831552) in ERR by lia. change (831552 + -164) with 831388 in ERR.

  st1. st1. st1. st1.

  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x9e248)) with (Z_to_bv 64 0x9e248) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }

  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x9e250)) with (Z_to_bv 64 0x9e250) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 831552) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [rewrite (unsigned_lit 831552) by lia; change (831552 + -164) with 831388; exact ERR| exact MR2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 831388 <= a < 831392 -> ~ rrepfoot st a.
Proof.
  intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct C as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

#[using="Type"] Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (831388, 831392)]%Z m m' -> wmono rsegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof.
  intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). pose_ceil. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). pose_ceil. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells rsegs m (errno_addr tp) [C4 e'] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt rsegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (831388, 831392)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e264) fc None m (seg_rom rsegs)).
Proof.
  intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (831388, 831392)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (pose_ceil; unfold RATP in *). subst tp.
  rewrite (unsigned_lit 831552) in ERR by lia. change (831552 + -164) with 831388 in ERR.
  rewrite (unsigned_lit 831552) by lia. change (831552 + -164) with 831388.

  st1.

  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | pose_ceil; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 831552) by lia. change (831552 + -164) with 831388.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End CEIL_WRAP_1.

