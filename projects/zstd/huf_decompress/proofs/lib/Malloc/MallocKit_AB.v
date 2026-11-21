(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (52 recorded proofs replaced by written proofs (repfoot_area, repfoot_group, repfoot_known and 49 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocKit_AB () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_maps@insert_insert_eqI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z2ltI59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib6Malloc9MallocRep5MLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:NEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;PAGE_SIZE_AC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notc59OSSVerify5KrLib6Malloc<MallocKit_AB9ivs_avoidC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB=avoid_outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_specC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3seqC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib6Malloc<MallocKit_ABAnth_error_map_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapK59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6NArith6BinNat1N6eqb_eqC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib6Malloc9MallocRep=aptr_eqb_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB@get_meta_rec_putC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB<aptr_eqb_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_ABDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB;ivs_coveredC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv5Instr6awidth01C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_specC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses9and_morphc59OSSVerify5KrLib6Malloc<MallocKit_AB?usage_set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;map_seq_updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB=unmap_seq_setC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5oconcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_AB5mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib6Malloc<MallocKit_AB?meta_word_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z5ldiffC47Corelib7Classes?RelationClasses=eq_TransitiveC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC59OSSVerify5KrLib6Malloc9MallocRep@land_ldiff_distrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7land_wdK46Stdlib9micromega5Tauto8GFormula09C59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib6Malloc=F_malloc_free;swrap32_eq'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith8Zbitwise1Z<add_lor_landC56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z<ldiff_nonnegC59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_mod32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9le4_congrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib6Malloc=F_malloc_free8sxv_zeroC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?iff_equivalence".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition repfoot (st : mstate) (a : Z) : Prop :=
  (CTX <= a < CTX + 928) \/ (MLOCK <= a < MLOCK + 4) \/ (NEED_LOCKS <= a < NEED_LOCKS + 1) \/ (PAGE_SIZE_A <= a < PAGE_SIZE_A + 8)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma repfoot_ctx st a : CTX <= a < CTX + 928 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8g002lR0p4p70R1p1003ap4p710p8P1p1004?p4p710R2p8P1p1004]R3p4p710R4p8P1P3p4p7210R3p8P1p1005:R5p4p710R6p8P1P5p4p7210R5p8P1g005SR7p4p710p8P1p1005lR8p4p710p8P1p1006Dp4p710p8P1p1006[p4p710p8P1p10072p4p710p8P1p1007JR9p4p710p8P1p1007aR:p4p710p8P1p1008=p4p710p8P1p1008Vp4p73110R;p8P1g008hR1p4p710R<p8p1009<p4p70R=P4p8P=P3p8P=p100:1p4p710R3p8P=P7p4p741110R4p8P=P1p4p7210p8P=P1p4p73110R>p8P=p100:Op4p7<111111111110R?p8P=p100;1p4p7<111111111110R@p8P=p100;Sp4p7<111111111110p8P2P6p8P2P5p8p100<5R=p4p73101RAp100<ORBp4p73110p8PAp100<hRCp4p73110p8PAp100=Dp4p710p8PAp100=WRDp4p7201p8PAp100=ip4p7201p8PAP>p8PAp100>;R>p4p73110p8PAp100>OREp4p73110p8PAp100>ip4p7201p8P=p4p710RAPBp4p710p8PAPCp4p710p8PAP6p8PAP5p8PAP<p8PAP>p4p710p8PAPEp4p710p8g00?<REp4p710RAP2p8PAP6p8PAP5p8PAP;p8PEp4p741110R;P:p4p73101p8P?P3p8P@P3p8P4P=p4p7511100R3p8P3P4p8P8p4p741110R8P=p4p76111100R4p8P4P8p8p100?Pp4p741110R8P=p4p771111100R4p8P4P8p8P9p4p741110R9P=p4p7:1111111100R=p8P=P9p8PDp4p7200RDP;p8P;PDp8g00@0j24Tg00@Lj1:Tg00A1j16Tg00AVj17Tg00B4j22Tg00BQj1=Tg00C3j4CTg00CQj6BTPEj4<TP7j4;Tg00D2j1@TP1j6?Tg00Djj2>Tg00ELj39Tg00Efj2OTg00F[j25Tg00G6j21Tg00GPj1NTg00HIj1MTg00ICj1LTg00J:j1ETg00K1j1DTg00Kgj1FTg00Lcj2GTg00M^j2HTg00N;j2ITg00O5j1JTg00Ooj28Tg00PIj3KTg00Pcj2ATf0R1#6#6p=3f2R7f1RE/A1'5p=0g00Q?RDg00R8R;g00RVR9/41g00SOR=#:#:#6#:#6#3#3#7,29R8701149E?0E8g00T4R8/4E%3=R9#7,2870Eg00ToR8/4E%7=,2870Eg00UoR8/4E%69R=#7,2870Eg00W0R8%=8P0P8P0g00WgR4g00XER3P;g00X^R@CCR?P4P3g00Y7R:P;P@g00YUEBR@P8C<P0P?P@P8C;PEf4RA#@E?1>81391OAER5f3R6'4R2%6=#3#3#3#3#7,25706'5X38'1X20,10g00Z3R8%=8P0P8P0P?P@P8C<P0P?P@P8C;PE%NAE?1>8139%:9#7,259026'5X58'1X40,10g00ZjR0%=0P4P0P4P3P:P0C<P4P3P:P0C;P7f5R:#ME?1>0E39g00[c%LEg00\[39%EER3/4A%DE#F,2370Ag00]S1G:71HA3'I%J139'5'5'5X8;,1;X60'1X74,14'8'8'8'8'8;K1UX0;X1DPEP1O2W0W1o"). Qed.
Lemma repfoot_mlock st a : MLOCK <= a < MLOCK + 4 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3g00@0j22Tg00AVj16Tg00B4j24Tg00@Lj1:Tg00A1j15Tg00BQj1<Tg00C3j4DTg00CQj6CTg00?<j4=Tg005Sj4;Tg00D2j1@Tg008hj6?Tg00Djj2>Tg00ELj38Tg00Efj2PTg00F[j27Tg00G6j21Tg00GPj1OTg00HIj1NTg00ICj1MTg00J:j1KTg00K1j1JTg00Kgj1ITg00Lcj2ETg00M^j2FTg00N;j2GTg00O5j1HTg00Ooj29Tg00PIj3LTg00^Mj3BTg00Pcj2ATf0R0#5#5p=3f2R1f1R2/A0'7p=0g00Q?R3g00R8R4g00T4R5/20g00SOR6#3R7#6,45R8700g00RVR9/22%:6#:#5#:#5#3#3#6,497021252?028R8g00ToR5/22%66,45702g00UoR5/22%57R6#6,45702g002lR5g00W0R9%<9P5P9P5g00WgR:g00XER;P4g00X^R<CDR=P:P;g00Y7R>P4P<g00YUECR<P9C=P5P=P<P9C;P2f4R?#@E?1>90381P?2R@f3RA'2RB%56#3#3#3#3#6,4@70A'7X39'1X25'1g00Z3R9%<9P5P9P5P=P<P9C=P5P=P<P9C;P2%O?E?1>9038%:7#6,4@90BA'7X59'1X45,15g00ZjR5%<5P:P5P:P;P>P5C=P:P;P>P5C;P1f5R>#NE?1>5238g00[c%M2g00\[38%K2R;/2?%J2#I,4;70?g00]S1E>11F?;'G%H038'7'7'7X84,14X65'1X7:,1:'9'9'9'9R:'9AL8:03BUX04X13P2P0O2W0W1o"). Qed.
Lemma repfoot_nl st a : NEED_LOCKS <= a < NEED_LOCKS + 1 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3g00@0j22Tg00AVj17Tg00B4j23Tg00@Lj1:Tg00A1j16Tg00BQj1<Tg00C3j4DTg00CQj6CTg00?<j4=Tg005Sj4;Tg00D2j1ATg008hj6?Tg00Djj2>Tg00ELj38Tg00Efj2PTg00F[j25Tg00G6j21Tg00GPj1OTg00HIj1NTg00ICj1MTg00J:j1KTg00K1j1JTg00Kgj1ITg00Lcj2ETg00M^j2FTg00N;j2GTg00O5j1HTg00Ooj29Tg00PIj3LTg00^Mj3@Tg00Pcj2BTf2R0f1R1f0R2'B'5p=0%62#6p=4g00Q?R3g00R8R4g00ToR5/22g00SOR6#7,35R7702g00RVR8/21%:6#:#6#:#6#4#4#7,38701g00T4R8/21%46R6#7,38701R81251?017R7g00UoR5/21%66R9#7,35701g002lR5g00W0R:%<:P5P:P5g00WgR;g00XER<P4g00X^R=CDR>P;P<g00Y7R?P4P=g00YUECR=P:C=P5P>P=P:C;P1f4R@#AE?1>:2381P@1RAf3RB'2RC%69#4#4#4#4#7,3A70B'5X3:'1X25'1g00Z3R:%<:P5P:P5P>P=P:C=P5P>P=P:C;P1%O@E?1>:238%:6#7,3A90CB'5X5:'1X45,15g00ZjR5%<5P;P5P;P<P?P5C=P;P<P?P5C;P0f5R?#NE?1>5138g00[c%M1g00\[38%K1R</2@%J1#I,3<70@g00]S1E?01F@<'G%H238'5'5'5X84,14X65'1X7;,1;'9'9'9R;'9R5'9AL7;29@853@UX04X13P1P2O2W0W1o"). Qed.
Lemma repfoot_pgsz st a : PAGE_SIZE_A <= a < PAGE_SIZE_A + 8 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3g00@0j23Tg00A1j15Tg00AVj16Tg00B4j24Tg00@Lj1:Tg00BQj1=Tg00C3j4DTg00CQj6CTg00?<j4>Tg005Sj4;Tg00D2j1ATg008hj6@Tg00Djj2?Tg00ELj38Tg00Efj2PTg00F[j27Tg00G6j21Tg00GPj1OTg00HIj1NTg00ICj1MTg00J:j1KTg00K1j1JTg00Kgj1ITg00Lcj2ETg00M^j2FTg00N;j2GTg00O5j1HTg00Ooj29Tg00PIj3LTg00^Mj3<Tg00Pcj2BTf0R0#5#5p=2f2R1f1R2/B0'7p=0g00Q?R3g00R8R4g00UoR5/30g00SOR6#2R7#5R8#6,45R9700g00RVR:/32%:6#:#5#:#5#2#2#6,4:702g00T4R:/32%67,4:702R:g00ToR;/32%66,4;702R;1352?029R9g002lR5g00W0R6%=6P5P6P5g00WgR<g00XER=P4g00X^R>CDR?P<P=g00Y7R@P4P>g00YUECR>P6C>P5P?P>P6C;P2f4RA#AE@1?60381PA2RBf3RC'3RD%58#2#2#2#2#6,4B70C'7X36'1X25'1g00Z3R6%=6P5P6P5P?P>P6C>P5P?P>P6C;P2%OAE@1?6038%:7#6,4B90DC'7X56'1X45,15g00ZjR5%=5P<P5P<P=P@P5C>P<P=P@P5C;P1f5R@#NE@1?5238g00[c%M2g00\[38%K2R=/3A%J2#I,4=70Ag00]S1E@11FA='G%H038'7'7'7X84,14X65'1X7<,1<'9'9R<'9R5'9R='9AL9<09<;59<:=3<UX04X13P2P0O2W0W1o"). Qed.
Lemma repfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> repfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
Lemma repfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> repfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
Lemma repfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> repfoot st a.
Proof. intros; do 6 right. exists rid, r, v. auto. Qed.

(* [comment removed for export] *)
Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
  forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. intros P lo hi a []. Qed.

Lemma ivs_avoid_cons : forall lo hi W P,
  (forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
  intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
  - inversion E; subst. apply H1. exact Ha.
  - eapply H2; eauto.
Qed.

Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
  - intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
  - apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

(* [comment removed for export] *)
Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma munch_agree : forall W m m' P A n,
  munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
  agree_on m m' A n.
Proof.
  intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : forall st g mr g',
  get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.

Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof. reflexivity. Qed.

Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
  intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
  intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
  nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
  intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
  nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
  intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma actives_length st : length (actives st) = 48%nat.
Proof. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
Lemma usages_length st : length (usages st) = 48%nat.
Proof. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.

Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
  intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
  destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01gh12mrh21ph32stp;1p;2g00A1j10Tg00g6j14Tg00gTj12Tg01bcj21Tg00dhj23Tg00Q?g002lg01KZg009<g00SO#0#0#0#0#0#0#4#2f3f0'1'3W2W1W0W3o"). Qed.
Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01gh12mrh21ph32stp;2g00Efj21Tg00dhj20Tg00Q?g002lR0g01KZg00R8f3f0'1'0X20W1W0W3o"). Qed.
Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01gh12mrh22stp;1p;2g02Glj11Tg00dhj20Tg00Q?g002lg01KZg029mf2#1'0W1W0W2o"). Qed.
Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC1"] "h01gh12mrh21rh32stp;1p;2g00cKj12Tg02Imj21Tg00dhj20Tg00Q?g002lg01KZR0g02Jm#2f3f0'1'0X20W1W0W3o"). Qed.

(* [comment removed for export] *)

Lemma outside_of_cover : forall (C : Z -> Prop) W a,
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
  - intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
  - apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.

(* [comment removed for export] *)
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
  end.

Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
  destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
  intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn in Hx |- *. tauto.
Qed.

End CANSEC1.
Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CANSEC2. Context {rc : runConstT}.
Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MU : munch W m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.

Lemma ctxW_avoid : forall A n, (A + n <= CTX \/ CTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
  0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
  intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - destruct HD as [HD|HD].
    + pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
    + pose proof (HD lo hi ltac:(left; reflexivity)). lia.
  - apply IH.
    + intros lo' hi' Hin. apply WIN. right; exact Hin.
    + destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.
End CTXFRAME.

(* [comment removed for export] *)
Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

End CANSEC2.
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

(* [comment removed for export] *)
Ltac ctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.

Section CANSEC3. Context {rc : runConstT}.
Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
  unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
  destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
  usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
  intros Hsc. unfold usages.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite usage_set_usage.
  destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

Lemma unmap_seq_set st i v j :
  unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
  unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
  unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
  intros Hi. unfold unmap_seqs.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite unmap_seq_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma step_seq_eq st :
  step_seq st = if c_seq (ctx st) =? 255
                then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
                else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma record_seq_eq sc st :
  record_seq sc st = if sc_in_seq_range sc
                     then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
                     else st.
Proof. reflexivity. Qed.


Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma conc_upd_ctx st f q : conc (upd_ctx f st) q = conc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01fh11qh22stp;2g00Efj21Tg00dhj20Tg00Q?R0g029mR1P1[R1g002lR2g00R8f2R3f0R4'1'0X12X01X20P3f1P4O3W1W0W2o"). Qed.
Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01fh11qh22stp;2g01Cfj21Tg00dhj20Tg00Q?R0g029mR1P1[R1g002lR2g01KZf2R3f0R4'1'0X12X01X20P3f1P4O3W1W0W2o"). Qed.
Lemma pw_upd_ctx st f q : pw (upd_ctx f st) q = pw st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "p'0h01fh11qh22sth31ai001ai011op;1p;2p;3g00A1j10Tg00g6j18Tg00gTj14Tg02c:j23Tg01bcj21Tg00ELj37Tg00Djj26Tg00dhj22Tg012:j15Tg00Q?R0g029mR1P1[R1g009<R2g00BQg002lR3g00SO#0#0#0#0#0#0#8#4R4f2R5f3R6'3f0R7'1116737P7f41637'1,24X33P7O1%53,15,24n10110100021010000X12X01X20P5f1P7O3W1W0W2o"). Qed.
Lemma oconc_upd_ctx st f q : oconc (upd_ctx f st) q = oconc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "p'0h01fh11qh22sth31ai001ai011op;2p;3p;1g02c:j25Tg02nKj20Tg00ELj33Tg00Djj22Tg00dhj21Tg012:j14Tg00Q?R0g029mR1P1[R1g009<R2g00BQg002lR3g00R8R4f2R5f3R6'5f0R7'0106733P7f41237'0,14X33P7O1%43,05,14n10110100021010000X12X01X20P5f1P7O3W1W0W2o"). Qed.
Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01qh12sch22sth31vp;2g00Efj21Tg00dhj20Tg00Q?R0g00R8R1g002lR2f3R3f0R4'1,01X02X31X11X20P3f2f1P4O4W0X31W1W2o"). Qed.
Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01qh12sch22sth31vp;2g01Cfj21Tg00dhj20Tg00Q?R0g00R8R1g002lR2g01KZf3R3f0R4'1'0X02X31X11X20P3f2f1P4O4W0X31W1W2o"). Qed.
Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "p'0h01qh12sch22sth31vh41ai001ai011op;3p;2p;1g02WYj35Tg02nKj20Tg00ELj33Tg00Djj22Tg00dhj21Tg012:j14Tg00Q?R0g00R8R1g009<R2g00BQg002lR3f3R4f2R5f4R635f0R7'01067531P7f51237'0,11X43P7O1%43,04,11n10110100021010000X02X31X11X20P4P5f1P7O4W0X31W1W2o"). Qed.
Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01qh12sch22sth31vp;2g00Efj21Tg00dhj20Tg00Q?R0g00R8R1g009<R2g002lR3f3R4f0R5'1,01X03X32X11X20P4f2f1P5O4W0W3W1W2o"). Qed.
Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01qh12sch22sth31vp;2g01Cfj21Tg00dhj20Tg00Q?R0g00R8R1g009<R2g002lR3g01KZf3R4f0R5'1'0X03X32X11X20P4f2f1P5O4W0W3W1W2o"). Qed.
Lemma oconc_set_active st sc v q : oconc (set_active sc v st) q = oconc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "p'0h01qh12sch22sth31vh41ai001ai011op;3p;2p;1g02oAj35Tg02nKj20Tg00ELj33Tg00Djj22Tg00dhj21Tg012:j14Tg00Q?R0g00R8R1g009<R2g00BQg002lR3f3R4f2R5f4R635f0R7'01067531P7f51237'0,11X43P7O1%43,04,11n10110100021010000X02X32X11X20P4P5f1P7O4X02W3W1W2o"). Qed.
Lemma meta_slot_upd_ctx st f q : meta_slot st q -> meta_slot (upd_ctx f st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01fh11qh22sth31Hp;2g01PSj20Tg00Q?R0g029mR1P1[R1g002lR2f2R3f0R4'0P4W3X12X01X20P3f1P4O3W1W0W2o"). Qed.
Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01qh12sch22sth31vh41Hp;2g01PSj20Tg00Q?R0g00R8R1g002lR2f3R3f0R4'0P4W4X02X31X11X20P3f2f1P4O4W0X31W1W2o"). Qed.
Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC3"] "h01qh12sch22sth31vh41Hp;2g01PSj20Tg00Q?R0g00R8R1g009<R2g002lR3f3R4f0R5'0P5W4X03X32X11X20P4f2f1P5O4W0W3W1W2o"). Qed.

End CANSEC3.
Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
                           ?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
  intros (LI & FB & SCR & ML).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
  intros (LI & FB & SCR & ML).
  change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_shr6_range mr : mw_ok mr -> 0 <= Z.shiftr (meta_word mr) 6 < 2^64.
Proof. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
  intros (LI & FB & SCR & ML).
  assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^6) with 64. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
  intros (LI & FB & SCR & ML).
  rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
  intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land. reflexivity.
Qed.



Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
  intros Hf Ha.
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
  intros Hf Ha. split; [apply Z.land_nonneg; lia|].
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
  intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
  rewrite sxv_mod32. reflexivity.
Qed.



Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
  intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
  intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
  rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.

(* [comment removed for export] *)
End CANSEC4.
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).

(* [comment removed for export] *)
Section CANSEC5. Context {rc : runConstT}.
Lemma meta_word_meta0 : meta_word meta0 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) ["CANSEC5"] "p;2g00dhj20Tg00R8g01=>'0o"). Qed.

End CANSEC5.
