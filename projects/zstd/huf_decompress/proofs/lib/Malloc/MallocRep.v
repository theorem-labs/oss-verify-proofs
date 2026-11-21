(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (54 recorded proofs replaced by written proofs (lr_lo_ge, lr_lo_group, lr_lo_nbrk and 51 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocRep () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01C47Corelib4Init5Logic6eq_indI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indK59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01C35stdpp4base6lookupK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib6Malloc9MallocRep;b8_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3zxbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4zx16C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib3Lib7SysStep=swrap32_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9land_onesc59OSSVerify5KrLib6Malloc9MallocRep@land_ldiff_distrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC46Stdlib6ZArith4Zdiv:Zminus_modC56Stdlib6ZArith6BinInt1Z7mod_modc59OSSVerify5KrLib6Malloc9MallocRep=swrap32_mod32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep<mod_mod_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z=testbit_spec'C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedK47Corelib5Lists7ListDef6Forall01I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List:Forall_nthC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib4Spec6Malloc<size_classesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep;conc_regionC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4Zdiv:Z_mod_multC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC59OSSVerify5KrLib3Lib3Mem<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Program6Basics4implc59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib6Malloc9MallocRep:regions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep5wr_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRepAreserved_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib6Malloc9MallocRep:lr_lo_nbrkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep<s_shadow_wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRepAget_shadow_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRepCget_shadow_wr8_sameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6NArith6BinNat1N6ltb_geC46Stdlib4Bool4BoolBnot_true_iff_falseC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib5Lists4List7existsbC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List>existsb_existsC56Stdlib6NArith6BinNat1N2ltC56Stdlib6NArith6BinNat1N6ltb_ltC56Stdlib6NArith6BinNat1N;le_lt_transC56Stdlib6NArith6BinNat1N9lt_irreflC35stdpp4base5emptyC35stdpp8fin_maps<lookup_emptyC47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6NArith6BinNat1N7compareK47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc59OSSVerify5KrLib6Malloc9MallocRep8le2_lohiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_specC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6NArith6BinNat1N8eqb_reflC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:map_ext_inI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib5Lists7ListDef3seqC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init3Nat3addC46Stdlib5Lists4List6in_seqC56Stdlib5Arith8PeanoNat3Nat8eqb_specC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib5Arith8PeanoNat3Nat8eqb_reflC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_active_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRepAactive_set_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep;map_seq_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep9shadow_leC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC45stdpp;list_basics4list;list_filterC45stdpp;list_basics4listClist_elem_of_filterC35stdpp4base7elem_ofC35stdpp4base6filterI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init5Logic7and_indC47Corelib7Classes?RelationClasses=iff_SymmetricC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00c59OSSVerify5KrLib6Malloc9MallocRep>In_filter_boolC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2or01C56Stdlib6NArith6BinNat1N;lt_le_transc59OSSVerify5KrLib6Malloc9MallocRep8sh_ticksC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc59OSSVerify5KrLib6Malloc9MallocRep=stale_hav_addC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3divC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6NArith6BinNat1N8ltb_specC56Stdlib6ZArith6BinInt1Z4iterC56Stdlib6PArith6BinPos3Pos>iter_invariantI47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib6Malloc9MallocRep=hav_unit_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep?shadow_le_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep>shadow_le_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep@Z_iter_invariantC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep=hav_page_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocRep6W_highC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition CTX : Z := 0x1a188.
Definition MLOCK : Z := 0x1a0d0.
Definition LIBC : Z := 0x1a120.
Definition NEED_LOCKS : Z := 0x1a123.     (* [comment removed for export] *)
Definition PAGE_SIZE_A : Z := 0x1a150.    (* [comment removed for export] *)
Definition SIZE_CLASSES : Z := 0x18170.
Definition DEBRUIJN : Z := 0x18130.

Definition get_meta_entry : Z := 0x15970.
Definition malloc_entry : Z := 0x16c7c.      (* [comment removed for export] *)
Definition free_entry : Z := 0x15e70.        (* [comment removed for export] *)
Definition alloc_meta_entry : Z := 0x15fd4.
Definition alloc_slot_entry : Z := 0x162e0.
Definition nontrivial_free_entry : Z := 0x15a6c.
Definition mmap_entry : Z := 0x172d4.
Definition munmap_entry : Z := 0x173e4.
Definition mprotect_entry : Z := 0x1739c.
Definition unlock_entry : Z := 0x17b14.

(* [comment removed for export] *)
Definition agent_reserved : list (Z * Z) := [(0x10000, 0x9000); (0x19000, 0x2000)].

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.
(* [comment removed for export] *)
Definition pw (st : mstate) (p : optr) : word := wz (oconc st p).

(* [comment removed for export] *)
Definition meta_word (mr : meta) : Z :=
  m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.

Definition meta_cells (st : mstate) (mr : meta) : list cell :=
  [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (pw st (m_mem mr));
   C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))].

Definition brk_word (st : mstate) : Z :=
  match c_brk (ctx st) with
  | BrkUntried => 0
  | BrkDead => 2^64 - 1
  | BrkLive rid off => conc st (rid, off)
  end.

Definition ctx_head_cells (st : mstate) : list cell :=
  let c := ctx st in
  [C8 (wz (c_secret c)); C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
   C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
   C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
   C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].

Definition actives (st : mstate) : list word := map (fun i => pw st (active st (Z.of_nat i))) (seq 0 48).
Definition usages (st : mstate) : list word := map (fun i => wz (usage st (Z.of_nat i))) (seq 0 48).
Definition unmap_seqs (st : mstate) : list byte := map (fun i => b8 (unmap_seq st (Z.of_nat i))) (seq 0 32).
Definition bouncess (st : mstate) : list byte := map (fun i => b8 (bounces st (Z.of_nat i))) (seq 0 32).
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition ctx_tail_cells (st : mstate) : list cell :=
  [C1 (b8 (c_seq (ctx st))); CB 7 (zeros 7); C8 (wz (brk_word st))].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lr_lo (r : region) : Z :=
  match r_kind r with RKBrk => r_base r + 4096 | _ => r_base r end.

Lemma lr_lo_ge r : r_base r <= lr_lo r.
Proof. unfold lr_lo. destruct (r_kind r); lia. Qed.
Lemma lr_lo_group r : r_kind r = RKGroup -> lr_lo r = r_base r.
Proof. unfold lr_lo. intros ->. reflexivity. Qed.
Lemma lr_lo_nbrk r : r_kind r <> RKBrk -> lr_lo r = r_base r.
Proof. unfold lr_lo. destruct (r_kind r); congruence. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

(* [comment removed for export] *)
Definition regions_wf : Prop :=
  s_reserved st = agent_reserved
  /\ (forall rid r, (s_regions st) !! rid = Some r ->
        0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
        /\ r_base r + round_up_pg (r_len r) <= ATOP
        /\ ranges_free agent_reserved (r_base r) (round_up_pg (r_len r)) = true)
  /\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
        r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)
  (* [comment removed for export] *)
  /\ (forall a ar, (s_areas st) !! a = Some ar ->
        exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
                  /\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
  /\ (forall b gh, (s_groups st) !! b = Some gh ->
        exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

End MREP.

(* [comment removed for export] *)
Definition mrep_W (st : mstate) : list (Z * Z) :=
  (CTX, CTX + 928)
  :: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

Definition blocks_preserved (L : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, (exists bl, In bl L /\ fst bl <= a < fst bl + snd bl) -> m' (wa a) = m (wa a).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_aadd : forall st p d,
  is_Some ((s_regions st) !! (fst p)) -> conc st (aadd p d) = conc st p + d.
Proof.
  intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.

Lemma conc_region : forall st rid off r,
  (s_regions st) !! rid = Some r -> conc st (rid, off) = r_base r + off.
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.

(* [comment removed for export] *)
Lemma wz_unsigned x : 0 <= x < 2^64 -> bv_unsigned (wz x) = x.
Proof. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned x : 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 x : 0 <= x < 256 -> zxb (b8 x) = wz x.
Proof. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz x : 0 <= x < 65536 -> zx16 (wz x) = wz x.
Proof. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz x : 0 <= x < 2^31 -> sx32 (wz x) = wz x.
Proof. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ldiff_distr x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Lemma mod_mod_pow2 z a b : 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma swrap32_mod32 z : (bv_swrap 32 z) mod 2^32 = z mod 2^32.
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.

Lemma wrap32_sx32_wz a : 0 <= a < 2^32 -> bv_wrap 32 (bv_unsigned (sx32 (wz a))) = a.
Proof.
  intros Ha. unfold sx32, wz. rewrite (unsigned_lit a) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32).
  rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite swrap32_mod32. apply Z.mod_small. lia.
Qed.

Lemma bit_test_form a i : 0 <= a -> 0 <= i ->
  Z.land (bv_swrap 32 (Z.shiftr a i) mod 2^64) 1 = Z.b2z (Z.testbit a i).
Proof.
  intros Ha Hi. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
  rewrite Z.testbit_spec' by lia. rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite (mod_mod_pow2 _ 1 64) by lia.
  rewrite <- (mod_mod_pow2 (bv_swrap 32 (a ≫ i)) 1 32) by lia. rewrite swrap32_mod32.
  rewrite (mod_mod_pow2 _ 1 32) by lia. reflexivity.
Qed.

Lemma signed_wz_small x : 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.

End CANSEC1.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Lemma size_class_range sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
  { unfold size_classes. repeat (constructor; [lia|]). constructor. }
  apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_region' : forall st (q : aptr) r,
  (s_regions st) !! (fst q) = Some r -> conc st q = r_base r + snd q.
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

(* [comment removed for export] *)
Definition meta_slot (st : mstate) (g : aptr) : Prop :=
  exists a ar k, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k).

Lemma le2_lohi : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> le2 (wz (lo + 256 * hi)) = [b8 lo; b8 hi].
Proof.
  intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
  f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ticks_ok (st : mstate) : Prop :=
  (forall rid sh u hl ch, (s_shadow st) !! rid = Some sh -> (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
  /\ (forall rid sh pg t, (s_shadow st) !! rid = Some sh -> (r_havp sh) !! pg = Some t -> (t <= s_tick st)%N).


(* [comment removed for export] *)
Lemma reserved_disjoint : forall b n, ranges_free agent_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x19000 <= b) /\ (b + n <= 0x19000 \/ 0x1b000 <= b).
Proof.
  intros b n H. unfold ranges_free, agent_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

(* [comment removed for export] *)
Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop :=
  exists r, (s_regions st) !! rid = Some r /\ lr_lo r <= a /\ a + len <= r_base r + round_up_pg (r_len r) /\ 0 <= len.

Lemma wr_in_image : forall st rid a len,
  regions_wf st -> wr_in st rid a len ->
  (a + len <= 0x19000 \/ 0x1b000 <= a) /\ 0 <= a /\ a + len <= 2^64.
Proof.
  intros st rid a len (_ & WR & _) (r & Hr & H1 & H2 & H3).
  destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). atop_facts.
  destruct (reserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.

Lemma wr_in_other : forall st rid a len rid' r',
  regions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof.
  intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
  destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

(* [comment removed for export] *)
Lemma area_lr_lo : forall st a ar r, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  lr_lo r <= r_base r + snd a.
Proof.
  intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

(* [comment removed for export] *)
Lemma regions_disjoint_full : forall st rid1 r1 rid2 r2,
  regions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
  r_base r1 + round_up_pg (r_len r1) <= r_base r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. exact X.
Qed.

Lemma regions_disjoint_grp : forall st rid1 r1 rid2 r2,
  regions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 = RKGroup ->
  r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma area_conc : forall st a ar, regions_wf st -> (s_areas st) !! a = Some ar ->
  exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
            /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
            /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

Lemma group_conc : forall st b gh, regions_wf st -> (s_groups st) !! b = Some gh ->
  exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
            /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
            /\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma s_shadow_wr8 : forall st p v,
  s_shadow (wr8 p v st) =
  <[fst p := mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p)))]> (s_shadow st).
Proof. intros. reflexivity. Qed.

Lemma get_shadow_unfold : forall st rid, get_shadow st rid = default shadow0 ((s_shadow st) !! rid).
Proof. reflexivity. Qed.

Lemma get_shadow_wr8_same : forall st p v,
  get_shadow (wr8 p v st) (fst p) =
  mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p))).
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.

Lemma get_shadow_wr8_other : forall st p v rid, rid <> fst p ->
  get_shadow (wr8 p v st) rid = get_shadow st rid.
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_other : forall st p v o, o <> snd p ->
  cell_read (get_shadow (wr8 p v st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_same : forall st p v,
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known v.
Proof.
  intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
  - assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
    { unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
      apply N.ltb_ge. eapply T2; eauto. }
    assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
    { unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([cov t] & Hin & Hb).
      destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
      apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
      pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
    rewrite SP, SU. reflexivity.
  - rewrite lookup_empty. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ticks_ok_wr8 : forall st p v, ticks_ok st -> ticks_ok (wr8 p v st).
Proof.
  intros st p v [T1 T2]. split.
  - intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
      * eapply T1; eauto.
      * rewrite lookup_empty in Hu. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
      * eapply T2; eauto.
      * rewrite lookup_empty in Hp. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma wr8_mod : forall st p v, wr8 p v st = wr8 p (v mod 256) st.
Proof.
  intros. unfold wr8, upd_shadow. cbn beta.
  replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le2_split : forall v, 0 <= v < 65536 -> le2 (wz v) = [b8 (v mod 256); b8 (v / 256)].
Proof.
  intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
  rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.


(* [comment removed for export] *)
Lemma get_meta_rec_upd : forall st g f g',
  get_meta_rec (upd_meta g f st) g' = if aptr_eqb g' g then f (get_meta_rec st g) else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma aptr_eqb_refl : forall g, aptr_eqb g g = true.
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
  (forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
  (s <= j)%nat ->
  map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
  intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
  cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
  - rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
    destruct (Nat.eqb_spec i s); [lia|reflexivity].
  - replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
    + rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
    + apply IH; [intros; apply Hg; lia|lia].
Qed.

Lemma active_set_active : forall st sc v i,
  active (set_active sc v st) i = if Z.eqb i sc then v else active st i.
Proof.
  intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
  destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
  - rewrite lookup_delete_eq. reflexivity.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma actives_set_active : forall st sc v, 0 <= sc < 48 ->
  actives (set_active sc v st) = upd (actives st) (Z.to_nat sc) (pw st v).
Proof.
  intros st sc v Hsc. unfold actives.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite active_set_active.
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Definition sh_ticks (sh : shadow) (t : N) : Prop :=
  (forall u hl ch, (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', (r_havp sh) !! pg = Some t' -> (t' <= t)%N).

Definition shadow_le (sh sh' : shadow) : Prop :=
  r_cells sh' = r_cells sh /\ forall o v, cell_read sh' o = Known v -> cell_read sh o = Known v.

Lemma shadow_le_refl : forall sh, shadow_le sh sh.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocRep ()) ["CANSEC2"] "h01oh11vh21Hh32shp;2p;4p;1p;3g00Ylj27Tg00@]j46Tg02Raj13Tg00K9j30Tg02]1j22Tg02`Tj11Tg00J3j25Tg02ORj44Tg02WLg00RXR0g02Jjg02KCg00`],70C6R1f0R2#3R3;03g02bWR4f2R5f1R6'2%1230R7f3/25%16504[^10^001513P2X27X10X00C4W3o"). Qed.
Lemma shadow_le_trans : forall a b c, shadow_le a b -> shadow_le b c -> shadow_le a c.
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.

Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
  In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
  intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  unfold Is_true. destruct (f x); intuition congruence.
Qed.

Lemma stale_hav_add : forall hl cov t b tc,
  (forall ch, In ch hl -> (snd ch <= t)%N) ->
  stale (hav_add cov t hl) b tc = false -> stale hl b tc = false.
Proof.
  intros hl cov t b tc Ht Hs. unfold stale in *.
  apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
  intros ([c' h'] & Hin & Hb). apply Hs. cbn [fst snd] in Hb.
  apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
  destruct (Z.ltb_spec cov c').
  - exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
    unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
  - exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
    destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
    pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.

Lemma hav_unit_step : forall cells hav havp u cov t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp)
  /\ sh_ticks (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp) t.
Proof.
  intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
  assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
  { intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
  split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 16) u) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|].
      * destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
      * destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [|exact T2].
    intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
    + rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
      apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
    + rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.

Lemma hav_page_step : forall cells hav havp pg t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells hav (<[pg := t]> havp))
  /\ sh_ticks (mkShadow cells hav (<[pg := t]> havp)) t.
Proof.
  intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
      * destruct (N.ltb_spec tc t); [discriminate|].
        destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
        -- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
        -- exact Hc.
      * discriminate.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [exact T1|].
    intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
    + rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
    + rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.

Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
  (forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
  intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.

Lemma havoc_units_le : forall cells hav havp x y t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells (havoc_units x y t hav) havp)
  /\ sh_ticks (mkShadow cells (havoc_units x y t hav) havp) t.
Proof.
  intros cells hav havp x y t T. unfold havoc_units.
  set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
                                         /\ sh_ticks (mkShadow cells (snd acc) havp) t)).
  - intros [u h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma havoc_pages_le : forall cells hav havp p0 p1 t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells hav (havoc_pages p0 p1 t havp))
  /\ sh_ticks (mkShadow cells hav (havoc_pages p0 p1 t havp)) t.
Proof.
  intros cells hav havp p0 p1 t T. unfold havoc_pages.
  set (f := fun acc : Z * gmap Z N => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
                                         /\ sh_ticks (mkShadow cells hav (snd acc)) t)).
  - intros [pg h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma sh_ticks_of_ticks_ok : forall st rid, ticks_ok st -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
  - split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.

(* [comment removed for export] *)
Definition W_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> ATOP <= lo.

Lemma W_high_disjoint : forall W a n, W_high W -> a + n <= ATOP -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
  split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
  apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.

Lemma ticks_ok_set_tick : forall st t, (s_tick st <= t)%N -> ticks_ok st -> ticks_ok (set_tick t st).
Proof.
  intros st t Ht [T1 T2]. split; cbn.
  - intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
  - intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.

(* [comment removed for export] *)
Lemma malloc_impl_spec_statement : True.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocRep ()) ["CANSEC2"] "g01Qao"). Qed.

(* [comment removed for export] *)
Lemma free_trivial_spec_statement : True.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocRep ()) ["CANSEC2"] "g01Qao"). Qed.

(* [comment removed for export] *)
Lemma wrappers_spec_statement : True.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocRep ()) ["CANSEC2"] "g01Qao"). Qed.


End CANSEC2.
