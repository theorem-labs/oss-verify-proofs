(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_MallocKit_B () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B9ivs_avoidC13~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2or00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B=avoid_outsideC13~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wa_unsignedC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B8agree_onC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3ivlC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Peano2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:F_syscalls5asegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B>bytes_at_agreeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame?wr_at_transportC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr6u64arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr4u64sC13~~~C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr;u64s_lengthC13~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op201C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6insertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C35stdpp8fin_maps@insert_insert_eqI35stdpp4gmap4gmap00C35stdpp8fin_maps@lookup_insert_neC47Corelib4Init9Datatypes2idC35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_specC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9set_metasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC35stdpp4base6lookupC35stdpp6option;from_optionI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I47Corelib7Numbers7BinNums1N00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5meta0C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK47Corelib4Init9Datatypes4bool02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9del_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9set_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9META_SIZEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3seqC47Corelib4Init3Nat3addK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes7nat_indC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z6to_natC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BAnth_error_map_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep7activesC13~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5usageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep6usagesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7bouncesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8bouncessC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9unmap_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:unmap_seqsC13~~~C46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapC47Corelib4Init9Datatypes3appC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem<bytes_at_appC13~~~C47Corelib4Init5Logic7and_indC47Corelib7Classes?RelationClasses>iff_TransitiveK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6s_tickC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_secretC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~C47Corelib4Init5Logic8eq_transC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6NArith6BinNat1N6eqb_eqC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib7Classes?RelationClasses=iff_ReflexiveC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep=aptr_eqb_reflC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B@get_meta_rec_putC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B<aptr_eqb_neqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BDmeta_slot_same_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep:meta_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5queueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<undef_reason01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev06C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B8queue_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead00C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B8queue_eqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9free_metaC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BEget_meta_rec_put_sameC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B5fm_stC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead02C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B@outside_of_coverC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTreeDpres_except_of_munchC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B;ivs_coveredC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B>ivs_covered_InC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_BEpres_except_of_munch'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6sub_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame<munch_weakenC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv5Instr6awidth01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free3sxvC13~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC45stdpp9bitvector;definitions8bv_swrapC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9sxv_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;wz_unsignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9sextw_sxvC13~~~C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free:sextw_sxv'C13~~~C56Stdlib6ZArith6BinInt1Z3lorC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free;lor_range64C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;Z_lor_rangeC13~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec>Z_testbit_highC13~~~C56Stdlib6ZArith6BinInt1Z8lor_specC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecAZ_bounded_by_bitsC13~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z8lor_commC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free=lor_sxv_mod32C13~~~C56Stdlib6ZArith6BinInt1Z;lt_le_transC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9le4_congrC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
  forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01Hh11Ph21ah32hih42lop;2p;4p;1p;3p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0g001iR0p4p710p8g002@j28Tg002`j47Tg003@j10TP0j31Tg003`j26Tg004<j22Tg004Xj23Tg0053j14Tg005Lj25Tg006eR0p-0[1800R1P0P0f2R2f1C7%01R131g007Cf4/62f3R3,22'3f6P3O1#4[f0R3n010000000W0X20X30X401513eW1o"). Qed.

Lemma ivs_avoid_cons : forall lo hi W P,
  (forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01ah11Eh22H1h31Hh42H0h52H3h62Hah71eh82hih92loh:1zi001zh;2H2h<2H4h=3Hinh>1Ph?1Wh@3hi'hA3lo'hB1pi011phC1xp;2p;1p;3p;6p;8p;4g002@R0j2?Tg007`j1>Tg003`j23Tg004<j24Tg004Xj25Tg0053j12Tg005Lj2:Tg008@j38Tg001ij36Tg008`R1j31Tg009:j67Tg009Wj89j6;Tg00:5j2=Tg002`j4<Tg006eR2P2f1R3f0R4C<p=01?22R5#>p-0^C2f4R6/34f3R7,44'5f2R8P3O1#2[^021:831083f8R9f7R:'0R;f6R<585565g00:Of9R=/09R>1078R?515A65?:13681487'5P9P7O1#2[P4f:R?/0=1067R@515f5RA/371476'5RBP1P5f<R1f;RC'0RDA153;P1P:O1#2[P310<ARE915Df=RD/0110:<RF515P5P2P0P2P2P2P4P4n2001101000120100100X75f>RG/0DP;P4E7A12D:P5P2P0P2P2P2P4P3n2001101000120100100X75f?R0/0GR;P>P3E7A120=f@R>=12?P4fAR?=12CRHP2P1fBRI=121RJP?P1O1#2[X:2P4PJP2PDPIPDO1#2X:2P2PG1334fERG,44'5fDRDP3O1#2[^02103G10>0515PDP0O1#2]1]2X921304144D'5fCRJP3O1#2[^02100D=15;P2P013I41443'5fFR0P3O1#2[^0210I310I?515P0P?O1#2]1]2X8213?4144>'5PGP3O1#2[^0210?>R?=15?P3P>P1O2W1W2PGP7P3P4G9W1W2PDP7P>P=G9PJP4E;b<X5HPIP4E;b5W4P4O1b4P4O1b4W3P4O1W3n2002101000000101A154FPCP<O1#2[XB5PEO1P41=5FO1b3W6W1P4O1A65@9P:P<PAP6P3P4O5X6BW=P4O1n200100000021100010000W3X02X@2XA210A6=857/:8eW;W2W>W?X82X92o"). Qed.

Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01Ph11xh21Wh32HPh42HWh51ah62Hah73Hinh82Hxh92IHh:2hih;3hi'h<1lh=2loh>3lo'i001pi011zp;2p;1p;3p;4p;5g002@R0j2BTg007`j1ATg005Lj22Tg00:ij21Tg003@j1@Tg008@j33Tg003`j25Tg004<j26Tg004Xj27Tg0053j19Tg008`j38Tg001ij34Tg00:5j2?Tg00<8j3<Tg00<Rj3;Tg00<lj4:Tg00=Gj5=Tg002`j4>Tg006eR1P1f1R2f0R3C>p=01B11R4#AR5P4p-0\1R6f2R7/22P7P2O1R8f4R9/17[[^11]0R:X25%@4R;/22g00=i11;7eX38W4X11X06P0P1P1f3R09349/22f6R;f5R<534/17\8[^11^06\:^<5P310<9=340/22f7R=/57167;'7R>#9R?11<7P7f8R@P=P010@=RA=84AA44A;1?4A3<P3P2O6X8>P?eP9P0P71072=44@15021627'7P;P9P0P7f<f;'01090R9584f:9449;;2P3O5W6W7X51X;1X>112<0eP3O4C:10=;=34</17eX38W4X11X06X9:X25X:1X=1P2P3O2n2001100000120101101X54P3D=W2o"). Qed.

(* [comment removed for export] *)
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma munch_agree : forall W m m' P A n,
  munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
  agree_on m m' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h02Hah16__sat1h24__x1h34__x2h44__x3h51ah61Ah72HAh82HBh92HPh:2HWh;2MUh<1Ph=1Wh>7__arithh?4__ffh@6__sat0hA8__varmaphB5__withC1mhD2m'hE1nhF1zp;1p;3p;2p;5p;4p;6p;7p;8g007`j1FTg00>Ej11Tg00>jj1>Tg00?Hj1BTg00?kj1dTg00@Mj3TTg005Lj2OTg003`j20Tg00AZj25Tg004<j23Tg004Xj29Tg00B7j1CTg00BUj2GTg00C2j1cTg00:ij2VTg00D:j5UTg00EWj2STg00FAj2QTg00Fij3PTg00GMj2NTg00:5j2ATg00Gnj18Tg00HMj24Tg00I6j36Tg00I_j2@Tg003@j1MTg008@j3=Tg00JKj2?Tg00Jij4LTg00KGj1KTg00Kej1JTg00LPj2:Tg00M3j1ITg00MXj3HTg00N;j4;Tg00Nfj1RTg00OHj2ETg00Okj3bTg00PNj2aTg00Q0j2WTg008`j3XTg00Q\j3YTg00R;j4ZTg00Rmj2[Tg009Wj6\Tg00T>j4]Tg00UVj7^Tg00V:j7_Tg00V^j8`Tg006eR0f1R1g00WBf0R2C;p=7P1g00WiR3g00XHR4P4g00XhR5P2g00YHF^p=2f2R6P3P4P4P5P1P2F_p=Df3R7P3P4P4P5P6P1P2G`p=<g00Yh#Fg00[3R3#1R8#1#1R9#1#1#1R:#>R;#B%>9#B#d[R9p-0\0f5R<f4R=;T7f6R>/O710=215=7,32'9P>P1O1[^50g00[XR?/0=15<=%C8R@%C:R:'GRA'0f7RB/0215B>,32'9P>%c1RCP0P1f=/V2XF0f<RDf9REP1P<P=P1P2O2DU1S;C1Q@:13?@RC10?:13?A[RF[10?@RGg00\6RHAP@:1UW010?A\H^0GP1g00\R1N?@'APCeO1PFg00]8RFg00]dRC#8RG#8RH#8R:,40140H140CRC560560g00^CRH'@%8:,40140G=60C560/@H%MF5=F3=%FFP01?06P11?07CL%K0%J0RF1:08R81:03RH'7,2FP0PHg00^oRC%I3,:09H08R3C;,2F5DF%R4R4PF1E0@=b0;R;,73,2FP4PF1E0?R3/78,2FP4173H,2FP0PHPCP;C;,2F5DFC<C<C<1aF5P2P6g00_VRFg00`6R5'A1W26=XF5dAY0?1CZb?bAbBX20X30X4010121516,32'91567/0A10?7R?137A,9?[[[^20^30^40P2f;PDP<P=P>PBO6b>b1b@b1,[1E\O2W0X50PEf8P>P<C]eW8W7W9W:W;XE0X60W<XD9WCW=o"). Qed.

Lemma bytes_at_agree : forall m m' A bs,
  bytes_at asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01ih11Hh22Hah36__sat3h44__x1h54__x2h64__x3h71Ah82AGh92H0h:2H1h;2HBh<2Hih=3Hi0h>7__arithh?4__ffh@6__sat2hA8__varmaphB5__withC2bshD4cstrhE5cstr0hF1mhG2m'hH1oi001bi011xp;1p;4p;2p;3p;7p;6p;<p;8g00>Ej18Tg00>jj1KTg00?Hj1FTg00?kR0j1RTg007`j1ITg00`Vj4BTg00adj22Tg00bDR1j10Tg00AZj21Tg00B7j1CTg00BUj2MTg003`j25Tg00bdR2j27Tg00C2j16Tg00c<j3;Tg00dEj39Tg008`j34Tg004XR3j2?Tg00T>j4ATg00dcj2ZTg00eEj2YTg004<R4j2:Tg00:5j2>Tg00fPj4WTg00g7j1ETg00FAj2VTg00Fij3UTg00GMj2TTg003@j1STg00JKj2DTg00Jij4QTg00KGj1PTg00Kej1NTg00OHj2OTg00LPj2@Tg00N;j4<Tg00Nfj1LTg00M3j1dTg00MXj3JTg00V:j7cTg00PNj2bTg00Q0j2aTg00Q\j3`Tg00R;j4_Tg009Wj6^Tg00<lj4GTg00g\l<]Tg00UVj7\Tg00V^j8[Tg00[XR5f0R6'5p=3g00hAR7g006eR8P2P1P4g00h`f5R4f4R1f3R2f2R9f1R:P6M<]p=XP:g00WiR;g00XHR<P<g00XhR=P6g00YHF\p==P2P;P<P<P=P9P:P6G[p=Hg00[3R>#8R?#8#8R@#8#8#8RA#K#F%K@#FR@#RRB[RC%I@g00iBRDP2P:P6CBP3%3912@:#0,19%C?RE%CARA'MRF'512@9RG,76f6RH%0:RI,11#65;DA9@2:54B[^07'?P4P1P2%0GCAPDP4P1P2CB[P6%3112@1#0,14/5F12@4RG,76f9RJf7RK/1I#65;DA9@H:54B[^07'?P3%0G,1H/5F12@HRG,76f:R3f8RL/1I#65;DA9@K:54B[^07PJPLPK%0GCAPDPJPLPKCB[P612@K#0,1L/5F12@JRJ,76f=RKf;RG/1I#65;DA9@3:54B[^07f<RMPGP3%0JCA%3G12@3#0,1G/5FR312@G,76RGf>RJ11KIRN#6RO5;DA9@M:54BRP[^07RQ'?PHP3PQP9PBf?POO1P0P@PBP61Z@6%09R0,1J#6,YDn10110100021010000A9@K954BXHBP2P:P6O2PJPOO1P9PN12@MRM,7:%0MRN,:IROP:PI1>8IPMPN1>8NEXP6CWPO%E9%3012@JRJ#E%0J#31VEA1:5ERJ%3A1:5F[R0[%3EROg00\6RNAUEA:UW2%3F\N^2OP:g00\R1T5E'>PJeO1P0g00]8R0#S%I0P81D89P:1D82CQ%P8%N8R0P81O85g00WBRJ1@8?R?C<,=0%L<REP0P8P?g00^oRO%d>,@8RNC<,=0PEP0P;P<P<P=P81@8>R>PJAJ8>?R?C<,=0P8P?POAJ8>NC<,=0FcCHCH1b0=P6P9g00_VR0g00`6R='>1a69=40=dA`85:C_b?bAbBX48X58X68%3:1:921192R2,591191,:2'?[[^48^58^68P6fC,2@#0%0LfDP4PHO5b>b3b@b3bEbDb=O2E^PPeX<GX07CGCGW8W;W:P:P6O2n2001000000121000000W1W9P:P6O2n2001000000121000000W1WCX78XGCWFo"). Qed.

Lemma rw_cells_agree : forall m m' A cs,
  rw_cells asegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono asegs m m' -> rw_cells asegs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01Hh11Ah22AGh32HBh42HWh53Hwfh62WMh72csh81mh92m'h:1np;1p;4p;3p;2p;6p;7g00>Ej12Tg00>jj1=Tg00?Hj1;Tg00?kj1>Tg007`j1DTg00jVj49Tg00kej47Tg00m5j11Tg00bDj10Tg00nGj43Tg00T>j44Tg00oRj35Tg010_j16Tg011oj1:Tg00`Vj48Tg00adj2CTg013Bj2BTg009Wj6ATg014\j6@Tg00<lj4<Tg016:j7?Tg00[3#2#2#2R0#2#2#2#=#;%=0#;R0#>[R1g006eg017Q#Dg00iBR2f3R3f1R4f0R5C9g004XR6P2f4R7f2R8P4C7P2P7P8%14#0C3f5R9P7P3%18#0C4f6R:=529P2P:P9P7C9[[P5P2P:P7P3C7P6%67P2f7R6P9%:7C8P2f8R;P:%19#0C3f9R9P;P6%1:#0C4f:R<=529P2P<P9P;C9[[[P5%6:P2P<P;%:6C8P2f;R6P9%1;#0C3f<R;P6P<%19#0C4f=R9=52;P2P9P;P6C7P2P9P;%16R<#0R:C3%66P2P9P;%:6R=C8P7f>R>P9P;P=P3g00hAR3P<f?P>P9%05C4X:3P41C0=1B67EAE@C<P2P>P9P;P:P8P5F?C<W6W2W4W3W5P4P5O2n2001000000120000000W0P4P5O2n2001000000120000000W0W7W1X91W8o"). Qed.

Lemma u64arr_agree : forall m m' A ws,
  u64arr asegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono asegs m m' -> u64arr asegs m' A ws.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01xh11Hh24__x1h31Ah42AGh52HBh62HWh72WMh87__arithh94__ffh:8__varmaph;5__with<4cstrh=1mh>2m'h?1nh@2wshA1yhB1zp;1p;4p;2p;3p;<p;7p;6p;Bg00>Ej14Tg00>jj1?Tg00?Hj1<Tg00?kj1DTg007`j1@Tg018_j4;Tg019kj1:Tg00`Vj49Tg00B7j1ITg00adj21Tg00bDR0j10Tg01;5R1j23Tg00nGj48Tg00T>j47Tg00oRj3>Tg00Gnj12Tg01;Rj2=Tg008`j36j1WTg01;ij1VTg00:5j25Tg00g\l<OTg00g7j1NTg003`j2HTg003@j1FTg00JKj2GTg00KGj1ETg00Kej1JTg00OHj2KTg00LPj2CTg01<Gj3LTg00N;j4MTg00UVj7BTg00PNj2QTg00Q0j2RTg00Q\j3ATg00R;j4STg01<jj4TTg01=Uj6_Tg01>1j1^Tg009Wj6]Tg014\j6\Tg016:j7[Tg00<lj4YTg01?BlBXTg01?hl<ZTg00hAR2P2P2g006eR3P3P3g01@MP0P0P0P1g01@mf5R1f4R4f3R5f2R6f1R7f0R8MBXp=UP2P3P3P3P0P0P1P4P5P6P7P8M<Zp=Pg00[3R0#4#4#4R9#4#4#4#?#<R:%?9#<R;#D[R<%@:g00iBR=P5P7P8C;g004XP=P4P6%:7C9P=P4P6%I9R911:7#0'3C8P1P4P511:6#0,39C7f6R>=>=1P=P>P1P4C;[[P8P=P>P4%:5C9P=f7R?P111:4#0,39C8f8R4P?P>11:1#0,39C7f9R1=>=4P=P1P4%:?R>C9P=P1P411:?R@#0RA,39RBC8f:RCP1P4P>P5P2g00]d#2#2#2#2#2#2#2#2R5/=@RDf;REPCP1%08RFC7X?2%0DRG963BRHA63BBP3P3%W3RIP8X03RJPIA6378#VXA3X03PBPB153BPGPBPJPJ153FX02PDPBP5P91539P@PA153AEUEPM<O%N@g00[XR@/HAg00]8RA#F%@A1G37%E3%J3RAg00Wig00XHRDPDg00XhRDP31K391C305L3R0g01APP0CMg00YHFB1QADP8P6g00_VRDg00`6RA'51R86=6DAdAA3@7CSb9b:b;X231398R@=63@^23P811:1#0O1b8b<CTPHP311:4R:#0,39f<PEPCP8C7XB3P61=5:#0P8E_b111;>%^?E]E\P=PCP1P4PBP6P8F[CYW7W4W6W5P7P8O2n2001000000121000000W1W@X33X><W=o"). Qed.

Lemma u8arr_agree : forall m m' A bs,
  u8arr asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono asegs m m' -> u8arr asegs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01Ah12AGh21Hh32HBh42HWh52WMh62bsh71mh82m'p;1p;4p;2p;3p;6p;7g00>Ej10Tg00>jj19Tg00?Hj16Tg00?kj1;Tg007`j1>Tg01B7j48Tg00`Vj43Tg00adj21Tg00bDj12Tg00nGj44Tg00T>j45Tg00oRj37Tg014\j6:Tg016:j7=Tg00<lj4<Tg00[3#0#0#0R0#0#0#0#9#6%90#6R0#;[R1g006e%>0g00iBR2f3R3f1R4f0R5C8g004XP2f4R6f2R7P4C3P2P6P71104#2C4f5R8P6P31107#2C5f6R9=728P2P9P8P6C8[[P5P2P9P6P3C3P2f7R:P81106#2C4f8R6P:P91108#2C5f9R8=726P2P8P6P:C3P2P8P6110:#2R0C4f:R9P8P6P:P3P4E:P2P9P8P6P0P7P5F=C<W5W1W4W3P4P5O2n2001000000120000000W2W6W0X81W7o"). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : forall st g mr g',
  get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01oh11Hh23Heqh31bi001bh43go'h53gr'h61ri011rh71ei021eh81ni031nh91th:2e0h;1gh<2g'h=2goh>2grh?2mrh@2n0hA2sti041pi051zp;1p;4p;6p;2p;3p;?p;7p;5p;Ag01CBR0p4p70R1p101DPp4p710R2p8P1p101DnR3p4p710R4p8P1P3p4p7210R3p8P1g01EKR5p4p710p8P1p101EgR6p4p710R7p8P1P6p4p7210R6p8P1g01F@R8p4p710p8P1g01FYR9p4p710p8P1g01G1R:p4p710p8P1g01GQR;p4p710p8P1g01GhR<p4p710p8P1g01H?R=p4p710p8P1g01HWR>p4p710p8P1g01HnR?p4p710p8P1g01IPR@p4p710p8P1p101Iip4p73110RAp8P1g01J;R1p4p710p8p101JOp4p70RBP4p8PBP3p8PBP5p4p7210p8PBP5p4p73110p8PBP:p4p741110R3p8PBP1p4p7210p8PBP1p4p73110p8PBp101K]p4p7<111111111110p8g01L?RBp4p710R4P2p8P4P7p8P4P6p8P4PAp8PBp4p741110RAP?p4p73101p8P?p4p7<111111111110g009WR4p4p710R6p8g01LSR7p4p7<111111111110P6p8P8p4p741110R6P?p4p7511100R2p8P2P6p8P9p4p741110R6P?p4p76111100R2p8P2P6p8P3P?p4p771111100R6p8P6P3p8P>p4p741110R3P?p4p7:1111111100R6p8P6P3p8P?p4p73100R3PAp8PAP3p8g01M5j1fTg01MQj4eTg01Moj6VTPBj4Kj3RTP8j4dj3NTP:j4[j3LTP5j4XTg01NPj15Tg01Oaj2;Tg01P>j2:Tg01P[j24Tg01Q9j20Tg01ROj2YTg008`j33Tg01S1R5j2FTg01STj2WTg00?kj1TTg00dcj2STg00:5j2?TP;j3QTP9j3JTP<j3MTP=j3ITP>j3OTP@j3PTP?l?HTP4j67Tg0053j1>Tg002@R4j2cTg01T6j4DTg009:j6ATg01TRj2GTg01U1j2`Tg01VCj2_Tg01WVj3^TP1j7\Tg01Xhj3ZTg01YEj3]Tg01Ybj6CTg01Z6j5@Tg002`j4aTP7lAbTP0g01ZQR7f4R1f3R?f2R@f1R>f0R=F\p=8g01[aR<g006eR9;Z=p=<A]<9=p==P7P7f5R;g01\?R:P0P7P1P?P@P>ECD@=37=p=6P<P9P>P=Cap=1P0P7P?P@P>P=ECp=9P7P7P>P:P=D@p=EA37>=p=2P7P7P1P:P0P7P?P@P>P=ECD@p=UP0P=P>P@P?P1P;f6R:f7R8f8RBf9R3P7f:RAf;R6f<R2f=RCf>RDMAbp=Bg01]NP4P<P9%f7REP0P<g01^`RFP9g01_9RGCeRHP<PFg01_RP9PGg01`0EVRGP7CKRFP0PHPGP7CdRIP>PFP0P7PFP0PHPGP7C[CXRJP=P@%51D8g00_VRKP7%<>%<=RL';%=>%==RM':'4P@101>n0100000020000E6P@P4P<P9PEPFPIP=PFPJ11@>RNP:%5BD8PKP7%<N,;L%=N,:M'4P:10B=n0100000020000E6P11Y>;A3<>;1;>;'F1;@:PKP5A3<?8PEPFPI11;1RMPFPJ113BRNPCf?RL#5D8PKP71:1BRO,4>PC10LMn0100000020000E6P>A3<1BRL1W1BRPA391B/FORO1:;3R;PKP5A39:ARQPFPIPNPFPJ11C2RRfARSfCRT#5RUD8RVC9RW,EERXPKP7g00`6RY/4>PS10TNRZn0100000020000'2P>A3986R8P<PCPEPFPI11=3R[PFPJ11DCR\fBR]fDR^#5D8R_DUR`/2]X5<P9P2PEPFPI11D=P_P]E6X49%T7Ra1S7S1EE=Rb/2]X0a1?7SPFPIPRPVC9P0AR0HGR]AQ0HGRcAN0HGRdAJ0HGReAL0HGRfAM0HGRgAI0HGRhAO0HGRiPHAP0HGRGP7PUPRPSM?HE7PBP=E7P3P1E7PKP714YYPSPZn0100000020000,2XeW:P=O1%>8RjP<PC10^[,2`X5<PaPFPI11CBR`PUC911D3R[,0^,2bX0a10T`,?7PFPIP`PVC9P]PcPdPePfPgPhPiPHPGPUPRP`PSA30R`R`1c<9RkP9P4P<P9P9P=P=n2001104000120000000X9kP[P\PkP\P[P=CDEAA393Cg007CR[P@P=O1'Gb2W1%>`eM?BE7P3P1E7PKP7g01`NR1,4YPSPZn0100000020000,2XeW8P=O1n10210010100021110211103b3b6W7P=O1%>LPPPOP;PKP5PQPKP7141>PSPZn0100000020000,2XP>P9P2PEPFPI11A=RQP_10^QE6X49PaPFPI1132R2PUC911ACRC,0^,2bX0a10T2,?7PFPIP2PVC9P]PcPdPePfPgPhPiPHPGPUPRP2PSA30R2R2PkP<P4P<P9P<P=P>n2001104000120000000X9kR4PCP\PkP\PCP=CDEAA3<ADRDP:P=O1,G[R[b2W1%>2eM?BE7PBP=E7PKP7141YPSPZn0100000020000,2XeX78P=O1PaPFPIPNPUC911A3RA,0^,2bX0a1?7ZPWP]PcPdPePfPgPhPiPHPGPUPRPNPSA30RNRRPkP<P4PAP\PkP\PAP=CDEAPDP[b2W1%>ReM?BE7PKP71411PSPZn0100000020000,2XeX@jP=O1n10210010100021110211103b3b6W8P=O1n10210010100021110211103b3b6PEPFPI11>=RjPFPJPMP3%56D8PKP7%<j%<M';%=j%=M':'4P3106jn0100000020000E6eX49X5<P>P=O2n2001104000121103105X=9X><P>P=O2n2001104000121103105PEPFPIP=PFPJP@P>%5?D8RJPKP71`=@P>10?=n0100000020000RKE6ePEPFPIP=1_J?#5PKE6ePEPFPIP=A^@>?R>#5PKE6e10>=/2KeX<0X?7X;0WAo"). Qed.

Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01fh11gh22stp;2p;3g01Q9j22Tg01WVj31Tg00:5j20Tg01]NR0g01CBg01ZQR1P1[f1R1f0f2R2/21O1;12,00W0W1W2o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01ch11ph21sh32stp;4p;1p;2g01`nj43Tg01bAj12Tg01cRj20Tg00:5j21Tg01CBg006eR0g01]NR1f3f2f1f0R2C3#2/02,11W3X00W2W1o"). Qed.
(* [comment removed for export] *)

Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01kh12arh21Hh31ah41gh51Eh62Egh72Hah82Hkh92sth:3st'i001xp;4p;6p;1p;3p;2g01MQj4PTg01Moj6OTg01L?j4MTg01dej13Tg008`j32Tg01f6j2:Tg00?kj1NTg01F@j4LTg004XR0j20Tg01gMj2<Tg01h[R1j2=Tg00<lj4CTg009Wj6ITg01i5j4@Tg00dcj2HTg003`j2GTg004<j2JTg01;5j2KTg00AZj2FTg01Ybj6>Tg01iOR2f0R3'Hp=6g00[X/G3p=4g01j_,J3p=7g01ko/K3p=8g01mB/F3p=9f2R4g01CBR5f1R6;23'0p=Bf6R7P5P2f5R8f4R9f3R:%34E>;26/03p=1g006eR;/=3p=;1<639254,0:p=5P5P2P9P:P4P6E>=283p=A1<639254p=?P5P2P:P4P6P3E>p=EA289:A2563,04'0p=Dg01]NR<P5g01[aR=g01^`R>P;g01_9R?CPR@P=P>g01_RP;P?g01`0EOR?P2CMR>%36%34321::6P1P5%N2R=P>P5P@P?P2CLR?P4f7R@%66RA%43%73'0RB%83#9RC,<4RD7B8F1X0;#;X12,=2X351:9:P3P=P>P?P4f9REPAABB@DF1X0;#;X12,=2P1P2P=P>P?P:f:RFPAPBf8RGP:PCC5F1X0;#;X121:G@P3P=P>P?P8f<R:PAPBPFP8PCC5F1X0;#;P1P;P=P>P?P7f=R1%64PBf;RHP7PCC5F1X0;1::HP3P=P>P?PGf?R7%69PBP1PGPCC5F1P0P=P>P?PEf@RI#3%68EA%46%76'0f>RJPE%86#9C51:I7P3P=P>P?PHfBRH#3%6@EA%49%79'0fAR7P:%89#9C5P0%48%78'0%88#99?H1fDfCR0':P3%4@%7@'0fER@%8G#97?IP5P=P>P?P4fJPAfIR4=BBDF1X0;#;X12,=2X35P7P2P=P>P?P0P4PAPBfHRAP0PCC5F1X0;#;X12P1P;P=P>P?PH%3ARACE%6JRJPBfGRB1<HCEDX0;PEP>PAP=P>P?PHP3CEPJ%4F%7F'0PB%8F#9,<HEDX4>P=P>P?P7PA%61EA%4E%7E'0R1fF%8E#97?7R7'0P8P1P7P6P3CCCC%3BP@EIC@C@C@W6W8P6P3O2n2001000000121000000W2W7P6P3O2n2001000000121000000W2X0;P6P3O2n2001000000121100000W2X12P6P3O2n2001000000121100000W2X35P6P3O2n2001000000121100000W2W5X45X:<W9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h04__x1h12Hih23Hi0h37__arithh44__ffh58__varmaph65__with74__x2h84cstrh91ih:5cstr0h;1ni001nh<1sh=4__p1h>1xh?2IHh@1XhA5cstr1hB1fhC1ohD1yp;2p;1p;3p;4p;6p;8p;<p;7p;Bp200R0g01nTR1p4p7210p8P0g01DnR2p4p710p8P0P2p4p7210p8P0g009WR3p4p710p8P0g00dER4p4p710p8g00bdR5j23Tg00?kj1=Tg01o0j2;TP4j39Tg01oLj28Tg00dcj25j1KTg008`j30j1JTg00bDR4j11Tg004<R6j27Tg00:5j24Tg00fPj4DTg00g7j1?Tg003@j1jTg007`j1hTg00JKj2OTg00KGj1_Tg00Kej1^Tg00OHj2MTg00LPj2LTg00N;j4BTg00Nfj1\Tg01ocj6[Tg00PNj2ZTg00Q0j2YTg00Q\j3XTg00R;j4WTg00GnR7j16Tg008@j3ETg00AZR8j22Tg020Gj2UTg020jj3TTg00B7j1lTg00MXj3@Tg01<jj4HTP2j8ATg021Gj1gTg00Jij4fTg00>Ej1eTP3j6`Tg021ej4aTP1j4bTg00g\l<CTg003`j2cTg00UVj7dTg00V^j8]Tg01?BlBQTg01?hl<iTg00hAR1f2R3f1R2f0R9Cbp=>P1g006eR:P5P4P6g00h`R;f3R<P3P2g00]dR=g00[XR>P9M<Cp=V1c>9p=<P2g00WiR?g00XHR@P@g00XhRAP9g00YHFdp=:P:P2g00^oP9CBp=GP<P?P@P@PAP3P2P9G]p=FP1P1P1P:P:P:g022FRBP4P4P4P8g022fRCP<P3P2P=P>P9MBQp=SP1P:P9P4P2P3P<f4RDf5REf6RFf7RGf8RHM<Cp=RP1P1P:P:P7P4P4P<g023IP3P2P9M<ip=IP1P:P5P4P6P;P=P>P<P3P2P9M<Cp=kP1P1P1P:P:P:PBP4P4P4P8PCPEPDP<P3P2P9MBQp=PP1P:P5P4P6P;PEPDP<P3P2P9M<Cp=NP2\11393%=F1;3<9>FE=9F2PE1832R;O1,5F30[^91^<1R6X;1139=132=%12R4/7>R5P2P414:4RC14:>R8CVP9CDP5%?3R5%13#<RBp-0R7g00]8RI#jRJ%hIRI1O:2RK%_:RL%^:RMP:1M:>RNg00WBg00[3RO,L:RPCB,:M%\@RQPM1GPN,:MPQPMP?P@P@PAP<E[CFCF1ZMARAP9P3g00_VR@g00`6R?'41Y93=0@?dAX:>2CWR?b4b5b6X0:W=%<9172>P<[[^0:^=7P9%=HR71;E=9>HG=9HDPG18EDO1,5H30%1DP2P3O4b3b8b2W1X91X<1%6<R@,39P1%6ERR,39f9RS#=RTPHPDO1%6DRU/;F9>SH5ES=9S2PH18D2O1,5S30]1P213=UPHP7%KHRDPDPGP<O1RVPG18<=RWO1RXPT\H/4DP1PHPGPGP<PWPS\1/4GA01<W%1<RD12D>RT50:%J1RY%J:RZ%1990:4A01291U293TXD1X>1R[P<PD14:DR\PWPTP<PDP\P8CSM9R13=R%1ER\%lORD'2RT,7>RWP8PR129DR8X>:R]P\O1P]PEP\14:\R^CIR_CkP9CDPW%?F%1FRW#<%?E%<\PJPIPKPLP:PPg01APRKA@:PNCB,:MPAP?b4b5b6X0:129>90:9^0:P9%1GR>O1b3b:b8b2CHGAGA1;@E9>HG9EHV=9H=15HX507eW1%69%6F'3f:R7#=RXPS18R2R=O1RV,57f;R@#=RNP7%63,8FO1,5@709XCXP7PX%K7R`P`PVPS%62RV,8ERaO1RbPN\7/4`P1P7PSPSP=PaP@\1/4SA01=a12T4R`124DRN,2\Rc50:PYPZP[P=P`PRPTP_P2P4PCEPPaPcPEP\P^PVPNP]P2P4PCCIR^EPM9R%6GRc,3V12>D,7NRNPVP]P4O1P^PcP]P>O1P]PGP>14:>R]CIENP9CDRcPNP5PB%?SR^%1S#<Ra%?H%1H#<PJPIP:1O:3P2%g:CfRHPLP:1M:DR_9@:PRT%eO,L:RO5@:PKA@:O_R_9@:PCB,:MPAP?b4b5b6X0:X7:1282122DRD,2950:^0:^7:P9PW%17O2b3bAb:b8b2CHGAGA1;RG9>7SRW=972PFPRP2132G174>P2P4PCPGP>P]ENPcPNP5PBP^PaPJPIPHPLPM1GT_,:MPQ1GPO,:MCFPAP?b4b5b6X0:X7:178D1723[^0:^7:P9%1@P\P<O3b3b:b8b2CHO3E`PSPEO1=E7W=97V157b50XeW1X91P9O1n0110000020111100P9O1%=G1;3U9>GF=9G2PFP;O1,5G30eW1X91X<1X?6X;1P9CaX;1WBX@0o"). Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;2z0h<1Hh=1ih>1oh?2sch@2sthA1yp&0p;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2;Tg00M3k100Tg00>Ej11Tg00B7j1WTg004<R0j26Tg004Xj23Tg00>jj1fTg00?Hj1bTg00?kj1]Tg023mR1j1YTg01oLj2VTg00bDR2j1ITg024Mj2@j1eTg025]j2Aj1lTg00dcj2Cj1nTg008`j37j1_Tg00:5j22Tg026mj2HTg00AZR3j2PTg01;ij1^Tg00g\l<JTg027Jj2XTg00:Oj2FTg00Gnj10Tg00HMj2=Tg00I6j3?Tg00I_j2BTg027lj1UTg028Jj2TTg028kj3RTg003@j1STg008@j3<Tg007`j1~Tg00JKj2}Tg021Gj1|Tg00Jij4uTg00KGj1tTg00Kej1pTg00LPj2NTg00OHj2MTg00N;j4:Tg00Nfj1mTg00MXj3kTg00PNj2jTg00Q0j2gTg00Q\j3hTg00R;j4iTg01<jj4KTg01Dnj8GTg01o0j2cTg01nTj4oTg00dEj3OTg00bdR4j2aTg029Tj6qTg009Wj6rTg02;5j1sTg01?hl<QTg01?BlBvTg01ocj6wTg00UVj7xTg00V:j7yTg02<Jj7zTg00V^j8{Tg006eR5f1R6f0R737p=5P5g00hAR8P5P5P1f4R1P2f3R9g02<nf2R:P6P7M<Qp=\P8P8P8P5P5P5g022FP2P2P2P3g022fg00]dR3g00[XR;P9P:P6P7MBvp=[P8P5P5P5P2P2f5R<P1P9P:P6P7M<Qp=ZP6g00WiR=g00XHR>P>g00XhR?P7Ewp=DP5P6g01APP7C:p=EP6P=P>P>P?P7g00YHFxp=4P:P=P>P>P?P6P7Fyp=9P:P=P>P>P?P6P7Fzp=LP9P=P>P>P?P:P6P7G{p=>%07#0#0#0p=d%07#0#0#0#0#0#0#0p=8P8P5P4P2P0g00h`P<P1P9P:P6P7M<Jp=`g01]N1;;7g00[3R0$00#1#1#1#1#WR2,67'3%10R4#1#1#1#1#1#f#bR=#]R@%Y6RA,V3RB#IRC,@:RD,A:RE,C=1@9:,A9,C=97@7X>@P=P@%n=RFPFPE1@:6RE,A:RGP@\=/2Fg01JORFP=%l:RHPHPDPEP=\F/2HP5PF%e:RHPHPCP6PF\5/2H15C61H;6RH,P;RF/56P5P5%_5REP7X45RDPE1567#^XA5X45PCPFPDPD%I7RC,25X48PBPF125;PAPHPD1H;7X45P6P61256RDD\RFC[EZP6P6PDM<J1X;6RD16;615H6'31;6;RBA75H;'3'FRE1H;:RIP5p-0RJg00]8RK%03RL#0RM,=5RN1=5L1=53RL5?55?5g00^CRO'BRP%0MRM,=5%U0,T5=R5N=?5LRL5?5/BO1BLO%SKRL5<K5<K3<%~KROP51}5:P6%|5CuRN%t5RQ%p5RR1DR11N50R01N54R4'E,4R59RRSP5P4g00WBRT1M5;RUC:,4R1E0U,4RRV59R5LR%m>R>PRP5PUPTP4C:,4R1DR<RT59RP>Ak5U0/E4,4RC>C>1jR?R?P7P:g00_VRUg00`6RW'21g7:=7UWdAh5;6CiRWb7b9b:X25X35X0JW11576,3:RUA757;RX,3B'F1;;:/311P;:/59[[^25^35^0J^1JP7161216;1RBP1P6P:P9O6b6b;b5CKGGGGGGP8P=1@9C,A9X=8R8%0M#d#8#8#8#8#8RM,c3Co=O=AP=P8PMP3PA1aAM16H2PAPHPFPMP21252E`PDPEPIP5A<KPLPOPNPQPRA9RTV9LRSP>PRf6,DRP5P4g00^oR41M52RSC:,4R59RP>P5P0P4PSC:,4RC>C>P?PWb7b9b:X25X35X0JX1JX8J139X,FU16:2R2,3<P2[[^25^35^0J^1J^8JP71;;11;1;PBP1P6P:P9O7b6b;b5CKEqEr%s:=O=A1C=G57@eW<X?5W@o"). Qed.

Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;2z0h<1Hh=1ih>1oh?2sch@2sthA1yp;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2:Tg00M3j1~Tg00>Ej11Tg00B7j1XTg004<R0j27Tg004Xj22Tg00>jj1fTg00?Hj1bTg00?kj1]Tg023mR1j1ZTg01oLj2WTg00bDR2j1ITg02=[j2=j1jTg02>jR3j1@Tg00dcj2Gj1mTg008`j35j1aTg00:5j23Tg026mj2HTg00AZR4j2PTg01;ij1_Tg00g\l<JTg027Jj2YTg00:Oj2CTg00Gnj10Tg00HMj2?Tg00I6j3ATg00I_j2BTg027lj1VTg028Jj2UTg028kj3TTg003@j1RTg008@j3<Tg007`j1STg00JKj2}Tg021Gj1|Tg00Jij4{Tg00KGj1tTg00Kej1sTg00LPj2NTg00OHj2MTg00N;j49Tg00Nfj1lTg00MXj3kTg00PNj2iTg00Q0j2hTg00Q\j3eTg00R;j4gTg01<jj4KTg01Dnj8FTg01o0j2cTg01nTj4nTg00dEj3OTg00bdR5j2`Tg029Tj6pTg009Wj6qTg02@:j1rTg01?hl<QTg01?BlBuTg01ocj6vTg00UVj7wTg00V:j7xTg02<Jj7yTg00V^j8zTg006eR6f1R7f0R835p=6P6g00hAR9P6P6P1f4R1P2f3R:g02<nf2R;P7P8M<Qp=^P9P9P9P6P6P6g022FP2P2P2P4g022fg00]dR4g00[XR<P:P;P7P8MBup=\P9P6P6P6P2P2f5R=P1P:P;P7P8M<Qp=[P7g00WiR>g00XHR?P?g00XhR@P8Evp=DP6P7g01APP8C9p=EP7P>P?P?P@P8g00YHFwp=4P;P>P?P?P@P7P8Fxp=;P;P>P?P?P@P7P8Fyp=LP:P>P?P?P@P;P7P8Gzp=>%08#0#0#0p=d%08#0#0#0#0#0#0#0p=8P9P6P5P2P0g00h`P=P1P:P;P7P8M<Jp=og01]N1:<8g00[3R0#~#1#1#1#1#XR2,78'2%10R5#1#1#1#1#1#f#bR>#]RA%Z7RB,W4RC#IRD,=;RE#@RF,G>1=:;#@,G>95A8X>AP>PA%m>RGPGPF1=;7RF#@RHPA\>/3GP6P>P3P3PEPFP>\6/33P6P6%j;R3P3PDP7P6\6/3316D71H<7R3,P<RF/67P6P6%a6REP8X46RGPE1678#_XA6X46PDPFPGPG%I8RD,36X49PCPF136<PBP3PG1H<8X46P7P71367RGD^RFC\E[P7P7PGM<J1Y<7RG17<71637'21:7<RCA563<'2'CRE1H<;RIP6p-0RJg00]8RK%04RL#0RM,?6RN1?6L1?64RL5A65A6g00^CRO'BRP%0MRM,?6%V0,U6=T6N=A6LRL5A6/BO1BLO%RKRL5<K5<K3<%SKROP61}6;P7%|6C{RN%t6RQ%s6RR1DR11N60R01N65R5'E,4R5;RRSP6P5g00WBRT1M6<RUC9,4R1E0U,4RRV5;R5LR%l?R?PRP6PUPTP5C9,4R1DR=RT5;RP?Ak6U0/E5,4RC>C>1iR@R@P8P;g00_VRUg00`6RW'31h8;=5UWdAe6<7CgRWb7b9b:X26X36X0JW11687,2;RUA568<RX,2C'C1:<;/211P<;/6:[[^26^36^0J^1JP8171217<1RCP1P7P;P:O6b6b;b5CKGFGFGFP9P>1=:D#@X=9R9%0M#d#8#8#8#8#8RM,c4Cn=O>BP>P9PMP4PB1`BM1732PBP3PFPMP21362EoPGPEPIP6A<KPLPOPNPQPRA;RTV9LRSP?PRf6,DRP6P5g00^oR51M62RSC9,4R5;RP?P6P0P5PSC9,4RC>C>P@PWb7b9b:X26X36X0JX1JX8J12:X,CU17;2R2,2=P2[[^26^36^0J^1J^8JP81:<11:1<PCP1P7P;P:O7b6b;b5CKEpEq%r;=O>B1G>H55AeW<X?6W@o"). Qed.

Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
  nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;1ih<2z0h=1Hh>1oh?2sth@1yp;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2;Tg00>Ej1:Tg00B7j1`Tg004<R0j27Tg004Xj22Tg00>jj1kTg00?Hj1dTg00?kj1_Tg023mR1j1[Tg01oLj2XTg00bDR2j1ITg02ANj2=j1jTg02B_R3j1<Tg00dcj2Hj1rTg008`j35j1aTg00:5j20Tg026mj2GTg00AZR4j2OTg01;ij1^Tg00g\l<JTg027Jj2YTg00:Oj2CTg00Gnj11Tg00HMj2?Tg00I6j3@Tg00I_j2BTg027lj1WTg028Jj2VTg028kj3UTg003@j1TTg008@j3ATg007`j1RTg00JKj2STg021Gj1|Tg00Jij4{Tg00KGj1zTg00Kej1yTg00LPj2QTg00OHj2MTg00N;j49Tg00Nfj1iTg00MXj3hTg00PNj2gTg00Q0j2fTg00Q\j3eTg00R;j4cTg01<jj4KTg01Dnj8FTg01o0j2bTg01nTj4lTg00dEj3NTg00bdR5j2mTg029Tj6oTg009Wj6pTg02Coj1qTg01?hl<PTg01?BlBsTg01ocj6tTg00UVj7uTg00V:j7vTg02<Jj7wTg00V^j8xTg006eR6f1R7f0R835p=6P6g00hAR9P6P6P1f4R1P2f3R:g02<nf2R;P7P8M<Pp=]P9P9P9P6P6P6g022FP2P2P2P4g022fg00]dR4g00[XR<P:P;P7P8MBsp=\P9P6P6P6P2P2f5R=P1P:P;P7P8M<Pp=ZP7g00WiR>g00XHR?P?g00XhR@P8Etp=DP6P7g01APP8C9p=EP7P>P?P?P@P8g00YHFup=4P;P>P?P?P@P7P8Fvp=8P;P>P?P?P@P7P8Fwp=LP:P>P?P?P@P;P7P8Gxp=>%18#1#1#1p=3P9P6P5P2P0g00h`P=P1P:P;P7P8M<Jp=ng01]N1;<8g00[3R0#:R2#:#:R5#:#:#`R>,78'2%k5#dR5#_RA%[7RB,X4RC#IRD,=;RE#<RF,H51=:;#<,H595A8X>AP5PA%r5RGPGPF1=;7RF#<RHPA\5/0GP6P5P3P3PEPFP5\6/03P6P6%j;R3P3PDP7P6\6/0316D71G<7R3,O<RF/67P6P6%a6REP8X46RGPE1678#^X@6X46PDPFPGPG%I8RD,06X49PCPF106<PBP3PG1G<8X46P7P71067RGD]RFC\EZP7P7PGM<J1Y<7RG17<71637'21;7<RCA563<'2'CRE1G<;RIP6p-0RJg00]8RK%14RL#1RM,?6RN1?6L1?64RL5@65@6g00^CRO'BRP%1MRM,?6%W0,V6=U6N=@6LRL5@6/BO1BLO%TKRL5AK5AK3A%RKROP61S6;P7%|6C{RN%z6RQ%y6RR1DR11Q60R01Q62R2'E,4R58RRSP6P2g00WBRT1M6<RUC9,4R1E0U,4RRV58R5LR%i?R?PRP6PUPTP2C9,4R1DR=RT58RP?Ah6U0/E2,4RC>C>1gR@R@P8P;g00_VRUg00`6RW'01f8;=5UWdAe6<7CcRWb7b9b:X26X36X0JW11687,2;RUA568<RX,2C'C1;<;/211O<;/6:[[^26^36^0J^1JP8171>17<1RCP1P7P;P:O6b6b<b5CKGFGFGFP9P51=:D#<X;9R9%1M#3#3#3#3#3#3#3RM,b4Cl=N5BP5P9PMP4PB1mBM173>PBP3PFPMP>106>EnPGPEPIP6AAKPLPOPNPQPRA8RTV9LRSP?PRf6,DRP6P2g00^oR21M6>RSC9,4R58RP?P6P0P2PSC9,4RC>C>P@PWb7b9b:X26X36X0JX1JX8J12:X,CU17;>R>,2=P>[[^26^36^0J^1J^8JP81;<11;1<PCP1P7P;P:O7b6b<b5CKEoEp%q;=N5B1H5H55AeW=X;6W?o"). Qed.

Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
  nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;1ih<2z0h=1Hh>1oh?2sth@1yp;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2;Tg00>Ej1:Tg00B7j1`Tg004<R0j27Tg004Xj22Tg00>jj1kTg00?Hj1dTg00?kj1_Tg023mR1j1[Tg01oLj2XTg00bDR2j1ITg02EEj2=j1jTg02B_R3j1<Tg00dcj2Hj1rTg008`j35j1aTg00:5j20Tg026mj2GTg00AZR4j2OTg01;ij1^Tg00g\l<JTg027Jj2YTg00:Oj2CTg00Gnj11Tg00HMj2?Tg00I6j3@Tg00I_j2BTg027lj1WTg028Jj2VTg028kj3UTg003@j1TTg008@j3ATg007`j1RTg00JKj2STg021Gj1|Tg00Jij4{Tg00KGj1zTg00Kej1yTg00LPj2QTg00OHj2MTg00N;j49Tg00Nfj1iTg00MXj3hTg00PNj2gTg00Q0j2fTg00Q\j3eTg00R;j4cTg01<jj4KTg01Dnj8FTg01o0j2bTg01nTj4lTg00dEj3NTg00bdR5j2mTg029Tj6oTg009Wj6pTg02FXj1qTg01?hl<PTg01?BlBsTg01ocj6tTg00UVj7uTg00V:j7vTg02<Jj7wTg00V^j8xTg006eR6f1R7f0R835p=6P6g00hAR9P6P6P1f4R1P2f3R:g02<nf2R;P7P8M<Pp=]P9P9P9P6P6P6g022FP2P2P2P4g022fg00]dR4g00[XR<P:P;P7P8MBsp=\P9P6P6P6P2P2f5R=P1P:P;P7P8M<Pp=ZP7g00WiR>g00XHR?P?g00XhR@P8Etp=DP6P7g01APP8C9p=EP7P>P?P?P@P8g00YHFup=4P;P>P?P?P@P7P8Fvp=8P;P>P?P?P@P7P8Fwp=LP:P>P?P?P@P;P7P8Gxp=>%18#1#1#1p=3P9P6P5P2P0g00h`P=P1P:P;P7P8M<Jp=ng01]N1;<8g00[3R0#:R2#:#:R5#:#:#`R>,78'2%k5#dR5#_RA%[7RB,X4RC#IRD,=;RE#<RF,H51=:;#<,H595A8X>AP5PA%r5RGPGPF1=;7RF#<RHPA\5/0GP6P5P3P3PEPFP5\6/03P6P6%j;R3P3PDP7P6\6/0316D71G<7R3,O<RF/67P6P6%a6REP8X46RGPE1678#^X@6X46PDPFPGPG%I8RD,06X49PCPF106<PBP3PG1G<8X46P7P71067RGD]RFC\EZP7P7PGM<J1Y<7RG17<71637'21;7<RCA563<'2'CRE1G<;RIP6p-0RJg00]8RK%14RL#1RM,?6RN1?6L1?64RL5@65@6g00^CRO'BRP%1MRM,?6%W0,V6=U6N=@6LRL5@6/BO1BLO%TKRL5AK5AK3A%RKROP61S6;P7%|6C{RN%z6RQ%y6RR1DR11Q60R01Q62R2'E,4R58RRSP6P2g00WBRT1M6<RUC9,4R1E0U,4RRV58R5LR%i?R?PRP6PUPTP2C9,4R1DR=RT58RP?Ah6U0/E2,4RC>C>1gR@R@P8P;g00_VRUg00`6RW'01f8;=5UWdAe6<7CcRWb7b9b:X26X36X0JW11687,2;RUA568<RX,2C'C1;<;/211O<;/6:[[^26^36^0J^1JP8171>17<1RCP1P7P;P:O6b6b<b5CKGFGFGFP9P51=:D#<X;9R9%1M#3#3#3#3#3#3#3RM,b4Cl=N5BP5P9PMP4PB1mBM173>PBP3PFPMP>106>EnPGPEPIP6AAKPLPOPNPQPRA8RTV9LRSP?PRf6,DRP6P2g00^oR21M6>RSC9,4R58RP?P6P0P2PSC9,4RC>C>P@PWb7b9b:X26X36X0JX1JX8J12:X,CU17;>R>,2=P>[[^26^36^0J^1J^8JP81;<11;1<PCP1P7P;P:O7b6b<b5CKEoEp%q;=N5B1H5H55AeW=X;6W?o"). Qed.

Lemma actives_length st : length (actives st) = 48%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h02sth11ih21np;2p;3p;6p;1p;4g01o0j2@Tg00adj23Tg008`j34Tg00:5j2?Tg02H0j2;Tg009Wj65Tg00>Ej11Tg00>jj18Tg00?Hj17Tg00bDj16Tg024Mj29Tg025]j2:Tg01nTj4>Tg02HOj4=Tg02;5j1<Tg00Gnj10Tf0R0#0#0#0#0#0#0#0#0p=2g01]NR1g00hAR2g00]dR3%23#2#2#2#2#2R4'@R5,32R6A4204X22R7P2P4P71?24P61;43E5g00[3#1#1#1#1#1#1#8#7R3P2P3f1R6%60,96':X12R6P5C>'3P2P3P6P5C=E5%<0,33=424eX01P0O1W0o"). Qed.
Lemma usages_length st : length (usages st) = 48%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h02sth11ih21np;2p;3p;6p;1p;4g01o0j2@Tg00adj23Tg008`j34Tg00:5j2?Tg02H0j2;Tg009Wj65Tg00>Ej11Tg00>jj18Tg00?Hj17Tg00bDj16Tg02=[j29Tg02>jj1:Tg01nTj4>Tg02HOj4=Tg02@:j1<Tg00Gnj10Tf0R0#0#0#0#0#0#0#0#0p=2g01]NR1g00hAR2g00]dR3%23#2#2#2#2#2R4'@R5,32R6A4204X22R7P2P4P71?24P61;43E5g00[3#1#1#1#1#1#1#8#7R3P2P3f1%60'9#:X12R6P5C>'3P2P3P6P5C=E5%<0,33=424eX01P0O1W0o"). Qed.
Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h02sth11ih21np;2p;3p;6p;1p;4g01o0j2@Tg00adj22Tg008`j34Tg00:5j2?Tg02H0j2;Tg009Wj65Tg00>Ej13Tg00>jj18Tg00?Hj17Tg00bDj16Tg02ANj29Tg02B_j1:Tg01nTj4>Tg02HOj4=Tg02Coj1<Tg00Gnj11Tf0R0#1#1#1#1p=0g01]NR1g00hAR2g00]dR3%03#0#0#0#0#0#0#0R4'@R5,22R6A4204X22R7P2P4P71?24P61;43E5g00[3#3#3#3#8#7R3P2P3f1%60'9#:X12R6P5C>'2P2P3P6P5C=E5%<0,23=424eX01P0O1W0o"). Qed.
Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h02sth11ih21np;2p;3p;6p;1p;4g01o0j2@Tg00adj22Tg008`j34Tg00:5j2?Tg02H0j2;Tg009Wj65Tg00>Ej13Tg00>jj18Tg00?Hj17Tg00bDj16Tg02EEj29Tg02B_j1:Tg01nTj4>Tg02HOj4=Tg02FXj1<Tg00Gnj11Tf0R0#1#1#1#1p=0g01]NR1g00hAR2g00]dR3%03#0#0#0#0#0#0#0R4'@R5,22R6A4204X22R7P2P4P71?24P61;43E5g00[3#3#3#3#8#7R3P2P3f1%60'9#:X12R6P5C>'2P2P3P6P5C=E5%<0,23=424eX01P0O1W0o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_at_cons : forall m a b bs, bytes_at asegs m a (b :: bs) <-> bytes_at asegs m a [b] /\ bytes_at asegs m (a + 1) bs.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01Hh12H0h22H1h31ah41bh52bsh65lemmah71mp;1p;3p;2p;9p;5p;4g00>Ej12Tg00>jj1;Tg00?Hj18Tg00?kj1>Tg007`j1FTg003@j1CTg008@j36Tg02Hnj3<Tg00adj27Tg00bDj14Tg004Xj21Tg02IKR0j2=Tg00B7j1ETg02Idj2DTg02JPl9BTg02KJj5ATg00Gnj1@Tg00<lj45Tg02L\j59Tg00`Vj4:Tg00AZj2?Tg00iBR1f2R2f1R3f0R4C:p=3P1f3R51?23P4C:p=0g00[3R6#2#2#2R7#2#2#2#;#8%;7#8R7#>[g006e%F7%C7R89673R9=<749352A3529R:P5P21779#4P4C0'1R;'=p-0R<P0g02M9f4R0A6728R==<73735A305=R>P0P5177=#4P3C0'1P4P0P5%E6R6P3C0R=,1>R?P?1D<?M9BW6P1P5P2P9P4DAP5P2g00]d#@#4R9P4C0,1:R1P?[P5P2P6P4C0,1:R:P0P5P9P3C0R<,1>R@[P>P<P?f5R?P0P9P2C0f6R<A670873?R8P<P?P6P5C0P3P4C5W2X1>P4D9X01P>P=P@P?P0P6P2C0P8P<P?P9P5C0P3P4C5W2X1>P4D9X0:C51=;:eO2W5X47W3W7o"). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof.
ltac2:(KReplay.run1_chk (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01ah11bh21gh37s_areasi007s_areash45s_ctxi015s_ctxh58s_groupsi028s_groupsh67s_metasi037s_metash7:s_next_ridi04:s_next_ridh89s_regionsi059s_regionsh9:s_reservedi06:s_reservedh:8s_secreti078s_secreth;8s_shadowi088s_shadowh<7s_slotsi097s_slotsh=6s_ticki0:6s_tickh>2sti0;1mp;3p;4p;6p;2p;1p;:p;9p;8p;7p;5p;@p;;g01WVj32Tg008`j36Tg01L?j43j3VTg01MQj4ITg01Moj6YTg002@j2?Tg007`j1UTg01G1j4Qj3PTg01EKj4MTg02Mjl:7l98j89j7Gj6Ej5Cj4Wl;5Tg00:5j21Tg01GQj3TTg01F@j3STg01FYj3RTg01Ghj3OTg01H?j3NTg01HWj3LTg01IPj3KTg01K]l@JTg01Dnj80Tg02O<j1:Tg02PKj1;Tg02Q^j1<Tg02S0j1DTg01NPj1=Tg01dej1FTg02TDj1@Tg01bAj1BTg02UVj1ATg02Vfj1>Tg02X8j1HTg01J;j7XTg01CBR0g01ZQR1f4R2f3R3f2R4f1R5f0R6FXp=4g01]NR7P7A23569234A2346567P3g02YLg01[aR8g01^`R9g01_RR:g02Z\C3P8P9P:g02[nC3P0P8P9g006eR;g01_9R<CIR=P8P9P:P;P<g01`0EYR<P1C3R:P0P=P<g01iOC3R9P0P=P<g02]@C3R>P0P=P<1?0;C3R?1?;;#UR@P@P7f:RAf9RBf8RCf7RDP:P0P1P:P0P=P<P1CQCMREfHRFfGRGP:PEPFfFRHf6RID4D4RJf5RKP2P3P4P5M:7PAPBPCPDP:PEPFPGPID4RLPKP2P3P4P5M:7P6P6P;P7\@RMPAPBPCPDPJPKP2P3P4M98PAPBPCPDPLPKP2P3P4M98P5P5P8PM\;RMPAPBPCPDPJPKP2P3G9PAPBPCPDPLPKP2P3G9P4P4P?PM\8RMPAPBPCPDPJPKP2FGPAPBPCPDPLPKP2FGP3P3P>PM\?RMPAPBPCPDPJPKEEPAPBPCPDPLPKEEP2P2P9PM\>RMPAPBPCPDPJDCPAPBPCPDPLDCPKPKP:PM\9RMPAPBPCPDCWRNPNPJPLPM\:/1NP0AV0=<AT0=<AS0=<AR0=<AP0=<AO0=<AN0=<AL0=<P=AK0=<P1PIPFPGPHM@JG0119KG011>2G011?3G01184G011;5G011@6G0PAPBPCPDPIPKP2P3P4P5P6M;5R@#:R?%;@R>%<@R9%D@R<P:PEPFPH%=@R=D4%F@RN%@@RM%B@RL%A@RJ%>@RO%H@RPM;5RQ#:%;Q%<Q%DQP:PEPFPG%=QD4%FQ%@Q%BQ%AQ%>Q%HQM;5P?P>P9P<P:PEPFPGP=D4PNPMPLPJPOPPM;5567eA2FH@92FGA2FG@567eW9X:;X=8W<W5W3W6X78W;W8W4PAPBPCPDPIPKP2P3P4P5P6O;n0110;0001;110110510810410310010210910:107106X11X01X20W>o"). Qed.

Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01bi001bh11ri011rh21ei021eh31fh41ni031nh51Hh61ah72a1h82a2h92b1h:2b2h;2e0h<2n0i041pi051zp;3p;1p;2p;6p;4g008`j30Tg0053j13Tg01U1j27Tg01ROj2DTg01Oaj28Tg01S1R0j2:Tg01P>j26Tg01STj2@Tg002@R1j2?Tg002`j39j2Ej4ATg00:5j2>Tg009:j64Tg02^Pj6<Tg01TRj2CTg01Xhj3=Tg01YEj3;Tg01P[j2BTg00_VR2f0R3g01`NR430p=5g01[aR5g006eR6f1R7P3CAp=11B73=024p=2g01CBR8P1P5P6A0873#3f2R9/77#5[^08P3P1P5P6f3R1/19=083#3f4R:/11/77#5[P3f6R;f5R<'11173508#3f7R=/D9A05=918=9':f8R>/81P2P0f9R1=05:f:R?/6<R@,27P7A05?<RA1@?<RBA06?</:@R@f;/6;R<P2P0f<=06=RCg00`6RD/27P7f==06>REA02D4P>1?56R>f?RFf>RG'111?G11?1P>\6RHP>P3PFO1X3HA956FRIA956?RJPHPIPIPJPH\5RIPHP3f@O1X3I1E56RKPK1>IKE4P5PHPKPFP?P:E4E<E4P6P>PJPGP1P3E4E<O1'C12DDeW;P3O1%3ER11>24RG12D4eW4P3O1n10210010100021010210103b0b1W2P3O1%3APBP@P<P2P0PC1247P7PG124DeX2EP3O1PG1244eX<1P3O1n10210010100021010210103b0b1W4P3O1n10210010100021010210103b0b111=;R=9=561197R99=56'8A;56=A;569'6'2e17=9#5eW5X:6X95P7P3O2n2001104000121103105X08X86X75P7P3O2n2001104000121103105W6o"). Qed.

Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01Hh12H0h22H1h35lemmah42H2h51ai001ah62a1h72a2h81bh91eh:1Bh;2H3h<2b1h=2b2h>1ni011nh?1zi021zi031pp;2p;3p;4p;6p;;p;9g01U1j2>Tg02IKR0j26Tg01Oaj2=Tg01P>j2<Tg01P[j2;Tg004XR1j25Tg02Idj2FTg02^nj2DTg02_Oj3MTg02`Ej4CTg02a8R2j6LTg02ajj2KTg02bJj4JTg02c1l;HTg02clj2GTg00:5j27Tg009Wj69Tg009:j6@Tg00<lj4BTg01Xhj3?Tg01YEj3ATg008`R3j38Tg002`j4ETg02JPl9ITg00_Vf0R4g00`638p=2g01CBR5f1R6;84p=4g01[aR7g006eR8P6P4CEp=0p-0R9P0g02M9f5R:f4R;f3R<f2R=P6P4M9Ip=:A8764p=3A8864p=1g002@R>P7P81>64#21464'6^85P4P>P7P810<=R?/>4#214?4'6P4f6R@/=6RA1<:4RB';#2%2ARC%2BRD'5'6f7RE/==RF1<@6RG';#2%2FRF%2GRG'5RHP410E@RI10=6RJ'4RKPK1F9KRLE:W31DAB13@6RB,6CPH13E=R=/5GRHPFP=P4PGPGP9P0g02dL9M90RFPGCCELPKPKPLE:W31K@611:4RC,6DPH11@6RH,5=RDP9P9^:9P0P9P9P0P0CJP1P2P=P9P0PFP=CCPGPHP4M;HPKPKPLE:W31G:415BCRCPK[10@:RB1064RL'4RGPD[P1P=PHf8RH/0E/4?R=P4f9R1/3;RDP7P:f:RF/1:f;R0,06/4I[X67111;R9P8P:10E4/4IX78175BPFP4E9W0PFP4E9W0P6P4O2n2001000000120000000X0CP3P5PI10;<RI,4613F:R3/59[P4P5P8P>P7P8P8P4P4n2001103000120101102X95101HPIP4E@11H<R<P5P7P>P7P8P7P4P6n2001103000120101102X9510F110:;P6E@P3130@P4f<R@/3EP7PHf=R3/1HRH136Ff>R;/11'5[X>711@EP4PHP8P11300114F'5X?813FF1111177F1781CBP;P4E9b;W4P3P4E9b4W2P4O1b2P4O1b2X1=P4O1X1Kn2002100000000100144?15D<[X55PJO1P4175?O1b1X0GCBO2O2O2A?78BA?78L'=AA78BAA78L'<';#2/6Ge1>BL#2/6GeX=8X<7P6P4O2n2001103000121101102X85X78X67P6P4O2n2001103000121101102X55o"). Qed.

Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01bh11gh21mh32mrh42stp;2p;3p;1p;6p;4g01U1j27Tg01Q9j20Tg008`j31Tg00:5j23Tg02e<j16Tg009Wj62Tg01WVj35Tg02fWj44Tg01]Ng01CBg01ZQR0P0g00_VR1P0f1R2/72R3f0R4f2R5/02n0100000020000A1042X20P1g00`6P1P0P4P2f3/05n0100000020000=102X011304P3%62E2A5245/02P5P2P4P2C4E2W3W1W4o"). Qed.
Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01bh11gh21mh32mrh41qh52stp;3p;1p;2p;6p;4g008`j30Tg0053j18Tg01U1j23Tg01Q9j21Tg00:5j27Tg02h7j36Tg009Wj62Tg01WVj34Tg02fWj45Tg01]Ng01CBR0g01ZQR1f0R2f2R3500#8P1g00_VR4P1f1R5f3R6'3R7P3f4R8/15R9n0100000020000f5/13R:9012X21P4g01`NP4P1P2P6P:n0100000020000=01:X041719P7A6562E2A4638/15P8P6P3P5C5E2UX40W3W1W5o"). Qed.

Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01gh12mrh21ph32stp;1p;2g00>Ej10Tg00>jj14Tg00?Hj12Tg025]j21Tg00:5j23Tg01]Ng01CBg01ZQg01JOg00[3#0#0#0#0#0#0#4#2f3f0'1'3W2W1W0W3o"). Qed.
Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01gh12mrh21ph32stp;2g02iSj21Tg00:5j20Tg01]Ng01CBR0g01ZQg006ef3f0'1'0X20W1W0W3o"). Qed.
Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01gh12mrh22stp;1p;2g02jaj11Tg00:5j20Tg01]Ng01CBg01ZQg02YLf2#1'0W1W0W2o"). Qed.
Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01gh12mrh21qh32stp;2p;3p;4p;6p;1p;5g01f6j27Tg01WVj36Tg01MQj40Tg01Moj61Tg01L?j45Tg01dej12Tg00:5j23Tg02knj54Tg01]Ng01CBR0g01ZQf3R1f0R2'7f4R3f2=613f1P0g01[aR1g01^`R4g006eR5g01_9R6C0P1P4g01_RP5P6g01`0E1g01iOC5%23'3P2D4UX20W1W0W3o"). Qed.
Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01gh12mrh21rh32stp;1p;2g007`j12Tg02mRj21Tg00:5j20Tg01]Ng01CBg01ZQR0g017Q#2f3f0'1'0X20W1W0W3o"). Qed.

(* [comment removed for export] *)
Definition fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => fm_link st0 g head
  | None => fm_single st0 h g
  end.

Lemma queue_eq : forall R h g st0 (k : mstate -> M R) bail,
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (queue_st h g st0).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01rh11oi001oh22Hnh32Hph41Rh51ai011ah64bailh71gh81hh91kh:3st0i021ci034headi045hprevi052pvi061xp;1p;2p;3p;6p;5p200R0g02njR1p4p710p8P0g0305R2p4p710p8P1j15Tg01Q9j2<Tg031Dj1?Tg00Nfj1FTg008`j33Tg032Tj2:Tg033fj2BTg0358j19j22Tg036Lj18j26Tg037`j30Tg0392j3;Tg00>Ej1JTg00B7j1ETg03:Dj1DTg03;\j1CTg03<jj3@Tg00:5j2ATg03>Bj1>Tg009Wj6=TP2j6ITg00dcj2HTg03?Rj5GTf1R2f0R1'<#>p=1g01CBR3/H1p=4g03@bg006eR4f2R5P2P1DGp=7g03B0g01]NR6f4R7#5R8\6g01JOR9f3R:,<5#?%F3R;3311:7=39;P9P;f8R<#5R=g00_VR>f9R?#5R@1:1;RAP>P@f5RBf6RC'1/:;g00?kRDP3P@f7RE,BBPB%4ERF#9PDP3P611C1%4<RG#8g01ZQRH11<5%45/61RI'2W0=0<E50111E2%42/61RJ'2X0H=0ECn10110400021010500501O1P7%4CRK16F1,2FX0H=0CB5;EO1RLn10110600021010300RMg00[3RN#J#E#D#CROP7V4RP57<RQn0110200020000%EN#D#CRN=7<PRPn0110200020000P7A@ECBO1RR33X19P9P;P>P@1:;;R;P>P@PAPMPQn0110200020000PPn0110200020000=3=RX191B7CRRP9PDP3PDP3f:#5R9P1PC%9GPDP3P611E1%4?#811?5/2IX0H=0?<50111<2/2JX0H=0<En10110400021010500501R?O1RPPB16G1,2GX0H=0EC9;<FR<O1n10110600021010300PBPDP3P6P1P?P<n10110600021010300O153@P11A9PX53P1O11A=Ln10110000021010100b1%5ERLPDP3P=PRP7%9KPDP3P611B1%8F11E5/2IX0H=0EC50111C2/2JX0H=0CBn10110400021010500501O1P:%4B16K1,2KX0H=0B75;CO1n10110600021010300RHP:A@CB7O1RK33eP>P=P;P>P=P;PHP:V4R497EOn0110200020000A7EN4n0110200020000=3LKe1<7BR4#>P1E=%?4P2E=PEPCPBP7P:P5EI=3LKeW3W2X68W9W:X73W8X40o"). Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01mh11Rh24bailh31gh41kh52stp;1p;3p;2p;6p;8p;5p200R0g02njR1p4p710p8P0g03CAR2p6091000p8P0g03DYR3p4p710p8P1j12Tg01WVj3<Tg031Dj14Tg00Nfj13Tg008`j30Tg00:5j2;Tg01Q9j2:Tg03Elj35Tg009Wj61Tg03>Bj16TP2j87TP3j58Tg03GQj29Tg01]NR3g01CBR2f3R1#2R4\3f4R3g03Hff2R5g01\?R6=<51R7f1R8f0R9g01ZQR:P6g01JOR;%49%32R230X0:1;;2R<1:75R7A5156R=E1P:P6%69=0;2X0:P<P7P=E1G7%23P3P5P1P8P9D8P81915O130eX24W4W3W5X10o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma outside_of_cover : forall (C : Z -> Prop) W a,
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01ah12hih22loh31xh41Wh52HCh62HWh71Ch82Hah93Hinh:2Hxh;2IHh<3hi'h=1lh>3lo'i001pi011zp;2p;1p;3p;4p;5g002@R0j2ATg007`j1@Tg001ij31Tg003`j28Tg004<j27Tg004Xj26Tg0053j10Tg00:ij22Tg003@j1:Tg008@j34Tg008`j35Tg00:5j29Tg00<8j3?Tg00<Rj3>Tg00<lj4<Tg00=Gj5;Tg002`j4=Tg006eR1P1f1R2f0R3C=p=3p-0\11A11R4#@R5P41323R6f3R7514R81873f2R9,73'6R:f8P2O1[^31[^11^21f4R;P2O1#01279R<[[^01X45%:4R=9146f7R>P2O1R?\:^31[^11^21P7P2O1#0g00=i12=9eW5W6X01P0P1P1f:R0P2O1R=\:^31\8^11^21f6R@P2O1#0P<[[^01f5RA=44;RB9146f;RCP2O1\:^31[^11^21%0?12B9[[^01[^=5P3f=P2O1\:^31\8^11^21f9R8P2O1#0P<[[^0113@A=44;R<9146f>P2O1\:^31[^11^21%0=18@9179A'6R=#0RB12;9P2P9P>P@13>@R>=54>A14>A194>3?P7P3O5O1X8=PBeP7P9A146@P@P;P713C013;7R;554A14;8;>9P2P3O5X::X31W9X<1X>1P3O3C<12<9eW5W6X01W;X45X11X21P2P3O2n2001100000121101101X04P3D;W4W7o"). Qed.

Lemma pres_except_of_munch' : forall C W m m',
  munch W m m' -> wmono asegs m m' ->
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
  pres_except C m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01xh11Ch22HCh32HWh42MUh51Wh62WMh72_Hh81ah92hih:2loh;1mh<2m'p;1p;3p;2p;4p;5p;7g007`j1ATg00>Ej10Tg00>jj12Tg00?Hj11Tg00?kj1@Tg00@Mj3;Tg00oRj3:Tg002@j29Tg002`j48Tg001ij37Tg003`j24Tg004<j25Tg004Xj23Tg00B7j16Tg00BUj2?Tg0053j1>Tg03J7j5<Tg03KWj7=Tg006eR0p-0]0g00Yh#Ag00[3#0R1#0#0R2#0#0#0R3#2#1%22#1#@[R2f2R4f1R5f0R63;g00iB?:451900P0P0P5P6C8f6R737f3R8/461564'3f:P5O1[^00[^90^:0P7f5f4P8P4P5g00[X/46%61%63'?,56'3f8R3P5O1#>f9P3P4P8P6D<W2W7X80F=W3W6W4X<2W;W5W1o"). Qed.

(* [comment removed for export] *)
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
  end.

Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h01xh12hih22loh31Eh41Hh52H1h62H0h73Hinh81Wh92H3h:2Hxh;1eh<3hi'h=3lo'h>1zi001zh?1Ch@2H2hA2H4hB2IHhC1ahD1lhE1pi011pp;2p;1p;3p;6p;8p;5p;4g002@R0j2BTg007`j1ATg03M:j22Tg001ij34Tg003@j1;Tg008@j35Tg004XR1j27Tg008`R2j31Tg00:OR3j2:Tg009:j66Tg009Wj88j69Tg00:5j2@Tg00=Gj5?Tg002`j4<Tg003`j2=Tg004<j2>Tg006eR4P4f1R5f0R6C<p=0f3R7f2R8'=1>56'7p=3p-0\41B44R9#AR:P912861056R;=497R<P7P6P6P8C3R=f8R>P5O1[^04[^14^24[X8:g00\6g007CR?P?P>P8O1P8n010000000X:=X04W7X<4X=4W4%;9R?,25A49;?f7R?P5O1\=^04[^14^24[eP0P4P4f4R@/26f:RAP5O1RB\=^04\<^14^24[f5RCA5985'2A59C@949;f;RDP5O1\=^04[^14^24[[^D:P612?6f=REP5O1\=^04\<^14^24[P@P6P6P7C3PB[^0412>5'7f6RB/0CR<=19;A49;@':P1PAP6P6f9R1C3f@RFP5O1[^04f>RG/2?f?RHP8O1PCf<RCP6P6PDC3fBRIP5O1[^04fARJ/2AP310ECR310>?RK519A49KDfCRKPBO1PB10GE101>RL519P2P910HGR210CDRM9195fGRNPAO1[P610A1RO919210FH10DAR2519P9P4P0P4P4P4P6P6n2001101000120100100X;910JFPMP6E6A14FDP9P4P0P4P4P4P6P5n2001101000120100100X;910IJP3P5E6A14IEA14KGP6fDRE=14HR3P4PFfER0=14FRMfLPHO1[X>4P6PMP4PJfMPFO1X>4P4PIP5P6P6fHRFC3fORJP5O1[^04105F10EK519PJPIO1]3]5X24PKP6P6PNC3fNP5O1[^0410KN10KI519P4PKfFRJP6P6P5C3fQRMP5O1[^0410J510J0519PMPEO1]3]5X14P0P6P6PEC3fPP5O1[^04100ERE=19EP5PKPIO2W3W5PFP7P5P6G8W3W5PNP7PDP>G8PJP6E9bAX93P0P6E9b9W6P6O1b6P6O1b6W4P6O1W4n2002101000000101A1962PJP1O1[XE9POO1P61@92O1b4W3P6O1A49LCPCP8PAP1P6P?PBO6W7P6O1n200100000021100010000W@W5P5P6O2n2001000000121000000X:=X04W7X<4X=4W41078=595,2>A59<@949;PGP5O1\=^04[^14^24[eWBX8:X14X24P5P6O2n2001101000121100100XC9P6D?W8W?o"). Qed.

Lemma pres_except_of_munch_cov : forall C W m m',
  munch W m m' -> wmono asegs m m' -> ivs_covered C W -> pres_except C m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "h01Ch11Wh21mh32m'p;1p;3p;2p;7g007`j19Tg00>Ej10Tg00>jj12Tg00?Hj11Tg00?kj18Tg00@Mj37Tg00oRj34Tg03M:j23Tg03NUj35Tg03P3j76Tg006ep-0[g00Yh#9g00[3#0#0#0R0#0#0#0#2#1%20#1#8[R0f2R1f1R2f0R337g00iB?412f5R4f4R5'3f6R6P4P5f3P1P2A5643F6UUUX30W2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_1"] "p'0h02H0h11Hh22H1h32H3h41Wh51mh62m'h72ivh82H2h92H4h:2Hxh;2MUh<1fh=3fhih>3floh?2hih@2lohA1xi001pi011zp;1p;3p;2p;4p;5p;6g007`j1CTg00>Ej17Tg00>jj1<Tg00?Hj1;Tg00?kj1BTg00@Mj38Tg00:ij24Tg003`j22Tg004<j21Tg004Xj23Tg0053j16Tg00<lj4:Tg01TRj2ATg02L\j59Tg03QXj2@Tg03Rfj6?Tg008@j3>Tg002`j4=Tg00YhR0f1R1f0R23>p=0g006eR3P3P1P2C=p=5g002@R4P3P3%C0R5g00[3#7#7#7R6#7#7#7#<#;%<6#;#B[R6f4R7f2R8'0?812f5R9f3R:,07R;'0?881[^66]5]4^70P2P4P3P3f6R4/59R</08?812f7R=/54/0;?881[^66^56^45P2f9R;f8R>'5/08?812f:R?/5;R@/0:RA1597/0:,0@R@P8P1f;RB/5?10<7'0/42f<R</21111B'3#6RC12=11114'3#61491RD'313CD12>8118='3#61448'312;:11:>'3#6RD14=:REf>RF/2:f=RG,1:'3#6/3E14>7f@RE/29R:114EREP9fBRH/2=RIfA,1=RJP1P2C:O1W3W0g007CRK\E\:12<4R411=<R:P712F>11>GP1P2C:O1W3W1PK\:\413IJRJ#6RI14B=fCR=/2>R411>HPK11;=P7P1O1fD,1?PK[P2P1O1PK1AK2b0b2W9X34P2D9X2JPIeP8C:b1b0W8X2DP2D9W0X1CP2D915<B/09/41eW:XA31@A@eP2E?W;X66X56X45X?3X@3P1P2O2n2001100000121101101X70X=3X>3P1P2O2n2001100000121101101X<0o"). Qed.
End CEIL_WRAP_1.


Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_2"] "h02Hah16__sat1h24__x1h31zh42Hmh57__arithh64__ffh76__sat0h86__sat2h98__varmaph:5__with;1ap;1p;2p;3p;6p;4p;7p;8g00>Ej11Tg00B7j15Tg00BUj2ATg004<j24Tg004Xj2<Tg03T:j23Tg008`j39Tg01P>j28Tg00:5j26Tg009Wj6=Tg00>jj1>Tg03TZj2WTg00EWj2VTg03U@j2UTg00FAj2OTg00Fij3NTg00GMj2KTg003@j1HTg007`j1GTg00JKj2FTg00KGj1ETg00Kej1DTg00OHj27Tg00LPj2CTg00N;j4;Tg00Okj3BTg00V:j7ITg00Nfj1JTg00V^j8@Tg00PNj2LTg00Q0j2MTg00Q\j3?Tg00R;j4PTg03V1j2QTg03WFj2RTg003`j2STg00UVj7TTg00[XR0f0R1'Sp=0g00_VR2g00`6R3791p=2f1R4g00WiR5g00XHR6P6g00XhR7P1g00YHFTp=:g006eR8%01g00[3R9#1R:#5R;%1:R:#1#1#1#1R<#5R='AR>,41'<R?%5:R:,34=980P8f2R@131:/80#2X38P8P01810#2X381623R313@:P1E=%><R<1W<@R2'V1U@:%0@%0:f4/3:#0[[1O;=140;R:%0=140>[RA[%0;RBg00\6RCAN;=4UW0%0>\C^0BP4g00\R1K0;'6P:eO1PAg00]8RA#H%GA1F84%E8%D8RAP5P6P6P7PAP5P6P6P7P81780g00WB1C89R9C;,:AP8P9g00^o178;=B8<C;,:AFIR<%J6P<G@1LA7P1P@P31M1@#2dA?804CPb6b9b:X28%04144>'<\?^28P1f7f6O2b5b1b7b1b8,Q@E=g03X4/R2#2eW4W0W;o"). Qed.
End CEIL_WRAP_2.


Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_3"] "p'0h01vh11zh25lemmah31xi001xh41yi011yi022x'i032y'p;1p;2p;3p;4p;6p;;p;7p;9p;@g00>Ej10Tg00>jj1;Tg03Xaj19Tg02>jj18Tg00EWj2?Tg008`j3Sj12Tg00?Hj1OTg03Z6j1DTg00AZj25Tg03ZfR0j26Tg03TZj2<j1RTg02bJj41Tg03[Mj1>Tg03\<j43Tg02_Oj3=Tg00B7j17Tg03]3j2QTg03]Tj2:Tg027lj1NTg03^5j2FTg03^bj4Ej7JTg02Idj24Tg03_Oj1GTg03`>j6HTg02c1l;CTg02JPl9KTg03`ij1BTg03bDj2ATg03c]j1MTg03e8l9@Tg03e`l@PTg006eR1g00[XR2f2R3f1R4g01;5R5g03fKR6g03fhR7f0R8g03gER9M9@p=LP1P2f6f5P5P6P7f4P9g03gnf3P3P4P2P2P8M@Pp=Ig00[3R9#0#0#0#0#0R7#0#;R6%98R5#8'?=S15%O6R:%2:R;%D:%;7R7%94R</52R='6R>,<6%8<R?,?6R@/52RA,67RB,<6P:^11RCP1P:%21RDP;C1REP1P:P;%>:C39=CE%R6P>PBg01[aRBP1^11R>%2BR6P1P1%79R9P1P1P4P8P1P1P4P31Q48RE#71:48n011010003001010310103P1P1P4P31:84%NEn011010003001010310103n011000003001010210102X41X31RE;LD,F1PDC1R4P0P>\BR3PBP>P6P4C1R6PBP>P4P1P1PD%>1C3C39=36P0CEP714B7P=PAP9PEPDP<P@P1PD%G1P@P<P8EH1412FIM;CFJP?P?14:?M9KW2%B8,A5%M8O2X01P8O1X01o"). Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_3"] "h01vh11zh25lemmap;1p;2p;3p;4p;6p;;p;7p;9g00>Ej10Tg00>jj1<Tg03Xaj18Tg02>jj14Tg00EWj25Tg008`j3Hj12Tg00?Hj1CTg03Z6j1=Tg03ZfR0j26Tg03TZj27j1ITg02bJj41Tg03[Mj19Tg03\<j43Tg02_Oj3;Tg03^bj4Gj7ATg02Idj2:Tg03_Oj1FTg03`>j6BTg02c1l;@Tg02JPl9?Tg03`ij1>Tg03bDj2DTg03hUj1ETg006eR1g00[3#0#0#0#0#0R2#0#<R3f0R4#8R5#4'5=H15%C3R6%26R7%=6%<2R2f1#8R8'6R9,73%48R:,53R;,62R<,73P6^11R=P1P6%21R>P7C1R?P1P6P7%96C39;=?%I3P9P<g01[aR<P1^11R9%2<R3P1P1P>P>C1R?P0P9\<R=P<P9P3P?C1R3P<P9P?P1P1P>%91C3C39;=3P0CGP21:<2P8P;P1P>%F1P;P8P4EBM;@FAP:P:1:6:M9?W2%>4,D5%E4O2X01P4O1W0o"). Qed.

(* [comment removed for export] *)
Lemma le4_lor_sxv : forall f s, 0 <= f < 2^32 -> 0 <= s < 2^32 ->
  le4 (Z_to_bv 64 (Z.lor (sxv s) (sxv f))) = le4 (wz (Z.lor f s)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CEIL_WRAP_3"] "h06__sat2h16__sat4h26__sat1h36__sat3h47__arithh54__x1h64__ffh78__varmaph85__with92Hah:1bh;1zh<4__p1h=6__sat0h>1Hh?2H0h@2HfhA2HkhB2HshC1fhD1khE1sp;1p;2p;4p;3p;6p;5p;7p;8g00>Ej17Tg00B7j1ATg00BUj2HTg004<j20Tg004Xj24Tg00>jj1MTg03Xaj15Tg03j1j21Tg03TZj2ITg02>jj1>Tg03`ij1GTg03jNj4PTg00FAj2OTg00Fij3NTg00GMj2kTg00:5j2DTg003@j1^Tg007`j1]Tg00JKj2\Tg00KGj1ZTg00Kej1YTg00OHj2@Tg00LPj2XTg00Okj3JTg00N;j4?Tg00Nfj1WTg00PNj2VTg00Q0j2UTg008`j39Tg00Q\j3STg00R;j4RTg03kkj4QTg03T:j26Tg00EWj2FTg01ocj6TTg021Gj1lTg003`j2=Tg03m:j2<Tg03m[j2CTg03n8j6KTg009Wj63Tg03oJj3jTg03olj5iTg00<lj4LTg041Aj3`Tg01T6j4_Tg041dj2aTg042Fj4bTg043ej5cTg03bDj2dTg03V1j2eTg044Jj3fTg00UVj7[Tg00V:j7gTg00V^j8hTg00[XR0f0R1'=p=2g006eR2f1R3g00WBP1C?p=;P3g00WiR4g00XHR5P5g00XhR6P1g00YHF[p=8f2R7P4P5P5P6P3P1Fgp=Ef3R8P4P5P5P6P7P3P1Ghp=:g00_VR9g01`NR:791p=B%23R;g00[3R<#7R=#AR>%7=#7#7#7R=#AR?'HR@,03'4RA%7=RB#MRC%57RD%58RE'1RF'I1187#>PDPE%G7%G8CP%2F%ABRB,H>RE,0F'4f4RFP81O>?RD100>RG%2?RH100@[RI[RJ%2>RKg00\6RLAN>?3UW9RM%2@\L^9KRN1O>BRO%2B100E[RP\GRQAN>B3VLX9KRB%2E\L^9KRKP3g00\R1k0>'DPGeRGO1RLPPPFPGO1RGPIg00]8RR#^RS%]RRR1\23RT%Z2RU%Y2RV1@20RW1X2<R<';,8VRXP2P<g00^oRY1@2>R>%M=5J2R=C?,8V5EVRZ%W5R[P2P<PYAJ2>CR>C?,8V9EVXRYC:1VV6R\P1P7g00`6R],D91U17=99]dAS203CRR0b6b7b8X52R]%21R^101@'4R_103E,4;R`[^52RaP1f;Rbf9O2Rcb4b3b2b=b2b0b3PDPJPMPNPOPQPBPKPLPPPGPIP]PaP1f:Raf8R]O2b4b3b2b=b2b0b3CQ11F8Rd#210dE'4P2%5Ff5Rd#5Re'1Rf161@Rgf6Rh/1dRi#>,FC/6@592X;2P211dFRj%5h,1e/6@=92gX;2P211FdRg16i@9921X;2RiP2PjPiP216j@Pj%2jRi10j@PDPJPMPNPOPQPBPKPLPPPGPIp-0RePSPRPTPUPVPVP4P5P5P6P8ET9EVXP[PXC:P\P0b6b7b8X52W<14^3P;[^52^<eP1f<Re/1bR;/0EP;f7R;O3b4b1b0b2b0b3b1RXP?PjPDPJPMPNPOPQPBPKPLPPPGPIPSPR%l2R8PU1@2?R6,;W,8VP\P0b6b7b8PHP1b4b1b0b2b0b3b1RHPX1=?1RWP91<;3R51<h3R4'C%B1X:9P9P:1<;7,C1#BX:9P9P:1C:1#BX:91D9:P4P?PhP3PHPDPJPMPNPOPQPBPKPLPPPGPIPSPRPTPUPVPZP[PZC:P\P0b6b7b8X52RZPA\_^52R_P1f=PbO2b4b1b0b2b0b3b1PDPJPMPNPOPQPBPKPLPPPGPIPSPRPTPUPV1;6<,8VR6P[P6C:P\P0b6b7b8X521=?3\W^52P1P]P;O2b4b1b0b2b0b3b1RWEKE3P5P?P;P3PHPDPJPMPNPOPQPBPKPLPPPGPIPZP_P1f>PeO2b4b1b0b2b0b3b1PWEKE311;h/<3Aj;h3E3WAXD2DiR;CL9`j@C_Pg1aFdE316f@PFPdPDPJPMPNPOPQPBPKPLPPPGPIPZP_Pcb4b1b0b2b0b3b1PDPJPMPNPOPQPBPKPLPPPGPIPZP_P1PePaO2b4b1b0b2b0b3b1CbE3%>j,FCPi10jEPXPjP@PEP;PDPJPMPNPOPQPBPKPLPPPGPIPSPRP8PU1;=>,8VP\P0b6b7b81=@EP1b4b1b0b2b0b3b1DcCL,djE31ICf,FCPDPJPMPNPOPQPBPKPLPPPGPIPSPRPTPUPVPYP[PYC:P\P0b6b7b8X52101E,4^P`[^52P1%5b%5e'1P]O2b4b1b0b2b0b3b1,efE3b?b>3fXBAW@XE2XC2o"). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ntf_mid_post (pc : Z) (R : list cell -> word -> Prop (* [comment removed for export] *)) : Prop := True.
End CEIL_WRAP_3.


