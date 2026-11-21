(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (41 recorded proofs replaced by written proofs (repfoot_area, repfoot_group, repfoot_known and 38 more)). *)
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
Ltac2 kr_t_MallocKit_B () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transI35stdpp9countable9Countable00C35stdpp7tactics<f_equal_helpC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_maps@insert_insert_eqI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z2ltI59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib6Malloc9MallocRep5MLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:NEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;PAGE_SIZE_AC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notc59OSSVerify5KrLib6Malloc;MallocKit_B9ivs_avoidC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B=avoid_outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_specC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3seqC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib6Malloc;MallocKit_BAnth_error_map_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapK59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6NArith6BinNat1N6eqb_eqC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib6Malloc9MallocRep=aptr_eqb_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B@get_meta_rec_putC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B<aptr_eqb_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_BDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B8queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B8queue_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_BEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B5fm_stC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B7free_fpC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_B;ivs_coveredC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv5Instr6awidth01C59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC45stdpp9bitvector;definitions8bv_swrapC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sextw_sxvC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC59OSSVerify5KrLib6Malloc=F_malloc_free:sextw_sxv'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib6Malloc=F_malloc_free;lor_range64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib3Lib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_specC59OSSVerify5KrLib3Lib8PropExecAZ_bounded_by_bitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z8lor_commC59OSSVerify5KrLib6Malloc=F_malloc_free=lor_sxv_mod32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_le_transC59OSSVerify5KrLib6Malloc=F_malloc_free9le4_congrC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
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
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001ip4p710p8g002@R0p4p70R1p10035p4p710p8P1p1003Sp4p710R2p8P1p10041R3p4p710R4p8P1P3p4p7210R3p8P1p1004NR5p4p710R6p8P1P5p4p7210R5p8P1g004gR7p4p710p8P1p1005@R8p4p710p8P1p1005Xp4p710p8P1p1005op4p710p8P1p1006Fp4p710p8P1p1006^R9p4p710p8P1p10075R:p4p710p8P1p1007Qp4p710p8P1p1007jp4p73110R;p8P1g008<R1p4p710R<p8p1008Pp4p70R=P4p8P=P3p8P=p1009Ep4p710R3p8P=P7p4p741110R4p8P=P1p4p7210p8P=P1p4p73110R>p8P=p1009cp4p7<111111111110R?p8P=p100:Ep4p7<111111111110R@p8P=p100:gp4p7<111111111110p8P2P6p8P2P5p8p100;IR=p4p73101RAp100;cRBp4p73110p8PAp100<<RCp4p73110p8PAp100<Xp4p710p8PAp100<kRDp4p7201p8PAp100==p4p7201p8PAP>p8PAp100=OR>p4p73110p8PAp100=cREp4p73110p8PAp100>=p4p7201p8P=p4p710RAPBp4p710p8PAPCp4p710p8PAP6p8PAP5p8PAP<p8PAP>p4p710p8PAPEp4p710p8g00>PREp4p710RAP2p8PAP6p8PAP5p8PAP;p8PEp4p741110R;P:p4p73101p8P?P3p8P@P3p8P4P=p4p7511100R3p8P3P4p8P8p4p741110R8P=p4p76111100R4p8P4P8p8p100>dp4p741110R8P=p4p771111100R4p8P4P8p8P9p4p741110R9P=p4p7:1111111100R=p8P=P9p8PDp4p7200RDP;p8P;PDp8g00?Dj24Tg00?`j1:Tg00@Ej16Tg00@jj17Tg00AHj22Tg00Aej1=Tg00BGj4CTg00Bej6BTPEj4<TP7j4;Tg00CFj1@TP1j6?Tg00D>j2>Tg00D`j39Tg00E:j2OTg00Eoj25Tg00FJj21Tg00Fdj1NTg00G]j1MTg00HWj1LTg00INj1ETg00JEj1DTg00K;j1FTg00L7j2GTg00M2j2HTg00MOj2ITg00NIj1JTg00OCj28Tg00O]j3KTg00P7j2ATf0R1#6#6p=3f2R7f1RE/A1'5p=0g00PSRDg00QLR;g00QjR9/41g00RcR=#:#:#6#:#6#3#3#7,29R8701149E?0E8g00SHR8/4E%3=R9#7,2870Eg00TCR8/4E%7=,2870Eg00UCR8/4E%69R=#7,2870Eg00VDR8%=8P0P8P0g00W;R4g00WYR3P;g00X2R@CCR?P4P3g00XKR:P;P@g00XiEBR@P8C<P0P?P@P8C;PEf4RA#@E?1>81391OAER5f3R6'4R2%6=#3#3#3#3#7,25706'5X38'1X20,10g00YGR8%=8P0P8P0P?P@P8C<P0P?P@P8C;PE%NAE?1>8139%:9#7,259026'5X58'1X40,10g00Z>R0%=0P4P0P4P3P:P0C<P4P3P:P0C;P7f5R:#ME?1>0E39g00[7%LEg00[o39%EER3/4A%DE#F,2370Ag00\g1G:71HA3'I%J139'5'5'5X8;,1;X60'1X74,14'8'8'8'8'8;K1UX0;X1DPEP1O2W0W1o"). Qed.
Lemma repfoot_mlock st a : MLOCK <= a < MLOCK + 4 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3g00?Dj22Tg00@jj16Tg00AHj24Tg00?`j1:Tg00@Ej15Tg00Aej1<Tg00BGj4DTg00Bej6CTg00>Pj4=Tg004gj4;Tg00CFj1@Tg008<j6?Tg00D>j2>Tg00D`j38Tg00E:j2PTg00Eoj27Tg00FJj21Tg00Fdj1OTg00G]j1NTg00HWj1MTg00INj1KTg00JEj1JTg00K;j1ITg00L7j2ETg00M2j2FTg00MOj2GTg00NIj1HTg00OCj29Tg00O]j3LTg00]aj3BTg00P7j2ATf0R0#5#5p=3f2R1f1R2/A0'7p=0g00PSR3g00QLR4g00SHR5/20g00RcR6#3R7#6,45R8700g00QjR9/22%:6#:#5#:#5#3#3#6,497021252?028R8g00TCR5/22%66,45702g00UCR5/22%57R6#6,45702g002@R5g00VDR9%<9P5P9P5g00W;R:g00WYR;P4g00X2R<CDR=P:P;g00XKR>P4P<g00XiECR<P9C=P5P=P<P9C;P2f4R?#@E?1>90381P?2R@f3RA'2RB%56#3#3#3#3#6,4@70A'7X39'1X25'1g00YGR9%<9P5P9P5P=P<P9C=P5P=P<P9C;P2%O?E?1>9038%:7#6,4@90BA'7X59'1X45,15g00Z>R5%<5P:P5P:P;P>P5C=P:P;P>P5C;P1f5R>#NE?1>5238g00[7%M2g00[o38%K2R;/2?%J2#I,4;70?g00\g1E>11F?;'G%H038'7'7'7X84,14X65'1X7:,1:'9'9'9'9R:'9AL8:03BUX04X13P2P0O2W0W1o"). Qed.
Lemma repfoot_nl st a : NEED_LOCKS <= a < NEED_LOCKS + 1 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3g00?Dj22Tg00@jj17Tg00AHj23Tg00?`j1:Tg00@Ej16Tg00Aej1<Tg00BGj4DTg00Bej6CTg00>Pj4=Tg004gj4;Tg00CFj1ATg008<j6?Tg00D>j2>Tg00D`j38Tg00E:j2PTg00Eoj25Tg00FJj21Tg00Fdj1OTg00G]j1NTg00HWj1MTg00INj1KTg00JEj1JTg00K;j1ITg00L7j2ETg00M2j2FTg00MOj2GTg00NIj1HTg00OCj29Tg00O]j3LTg00]aj3@Tg00P7j2BTf2R0f1R1f0R2'B'5p=0%62#6p=4g00PSR3g00QLR4g00TCR5/22g00RcR6#7,35R7702g00QjR8/21%:6#:#6#:#6#4#4#7,38701g00SHR8/21%46R6#7,38701R81251?017R7g00UCR5/21%66R9#7,35701g002@R5g00VDR:%<:P5P:P5g00W;R;g00WYR<P4g00X2R=CDR>P;P<g00XKR?P4P=g00XiECR=P:C=P5P>P=P:C;P1f4R@#AE?1>:2381P@1RAf3RB'2RC%69#4#4#4#4#7,3A70B'5X3:'1X25'1g00YGR:%<:P5P:P5P>P=P:C=P5P>P=P:C;P1%O@E?1>:238%:6#7,3A90CB'5X5:'1X45,15g00Z>R5%<5P;P5P;P<P?P5C=P;P<P?P5C;P0f5R?#NE?1>5138g00[7%M1g00[o38%K1R</2@%J1#I,3<70@g00\g1E?01F@<'G%H238'5'5'5X84,14X65'1X7;,1;'9'9'9R;'9R5'9AL7;29@853@UX04X13P1P2O2W0W1o"). Qed.
Lemma repfoot_pgsz st a : PAGE_SIZE_A <= a < PAGE_SIZE_A + 8 -> repfoot st a.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01ah12sth22akh32arh41bh52ghh61rh73ridh81vp;2p;1p;4p;6p;3g00?Dj23Tg00@Ej15Tg00@jj16Tg00AHj24Tg00?`j1:Tg00Aej1=Tg00BGj4DTg00Bej6CTg00>Pj4>Tg004gj4;Tg00CFj1ATg008<j6@Tg00D>j2?Tg00D`j38Tg00E:j2PTg00Eoj27Tg00FJj21Tg00Fdj1OTg00G]j1NTg00HWj1MTg00INj1KTg00JEj1JTg00K;j1ITg00L7j2ETg00M2j2FTg00MOj2GTg00NIj1HTg00OCj29Tg00O]j3LTg00]aj3<Tg00P7j2BTf0R0#5#5p=2f2R1f1R2/B0'7p=0g00PSR3g00QLR4g00UCR5/30g00RcR6#2R7#5R8#6,45R9700g00QjR:/32%:6#:#5#:#5#2#2#6,4:702g00SHR:/32%67,4:702R:g00TCR;/32%66,4;702R;1352?029R9g002@R5g00VDR6%=6P5P6P5g00W;R<g00WYR=P4g00X2R>CDR?P<P=g00XKR@P4P>g00XiECR>P6C>P5P?P>P6C;P2f4RA#AE@1?60381PA2RBf3RC'3RD%58#2#2#2#2#6,4B70C'7X36'1X25'1g00YGR6%=6P5P6P5P?P>P6C>P5P?P>P6C;P2%OAE@1?6038%:7#6,4B90DC'7X56'1X45,15g00Z>R5%=5P<P5P<P=P@P5C>P<P=P@P5C;P1f5R@#NE@1?5238g00[7%M2g00[o38%K2R=/3A%J2#I,4=70Ag00\g1E@11FA='G%H038'7'7'7X84,14X65'1X7<,1<'9'9R<'9R5'9R='9AL9<09<;59<:=3<UX04X13P2P0O2W0W1o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01gh12mrh21ph32stp;1p;2g00@Ej10Tg00fIj14Tg00fgj12Tg01b4j21Tg00d;j23Tg00PSg002@g01Jkg008Pg00Rc#0#0#0#0#0#0#4#2f3f0'1'3W2W1W0W3o"). Qed.
Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01gh12mrh21ph32stp;2g00E:j21Tg00d;j20Tg00PSg002@R0g01Jkg00QLf3f0'1'0X20W1W0W3o"). Qed.
Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01gh12mrh22stp;1p;2g02G:j11Tg00d;j20Tg00PSg002@g01Jkg029=f2#1'0W1W0W2o"). Qed.
Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) ["CANSEC1"] "h01gh12mrh21rh32stp;1p;2g00b^j12Tg02I:j21Tg00d;j20Tg00PSg002@g01JkR0g02J:#2f3f0'1'0X20W1W0W3o"). Qed.

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
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold queue_st, fm_link, fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
  intros. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition free_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  (lo <= a < sp
   \/ CTX <= a < CTX + 928
   \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma free_fp_stack st lo sp a : lo <= a < sp -> free_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
Lemma free_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> free_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
Lemma free_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> free_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
Lemma free_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> free_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

(* [comment removed for export] *)
Lemma free_fp_mono : forall st st' lo sp sp' a,
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
  (forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
  sp' <= sp ->
  free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
  intros st st' lo sp sp' a ER ES HG HS H.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
    right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
  - right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
    rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

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
(* [comment removed for export] *)


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

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

(* [comment removed for export] *)
Lemma le4_lor_sxv : forall f s, 0 <= f < 2^32 -> 0 <= s < 2^32 ->
  le4 (Z_to_bv 64 (Z.lor (sxv s) (sxv f))) = le4 (wz (Z.lor f s)).
Proof.
  intros f s Hf Hs. apply le4_congr. pose proof (lor_range64 (sxv s) (sxv f) (sxv_range _) (sxv_range _)).
  pose proof (Z_lor_range f s ltac:(lia) ltac:(lia)).
  rewrite unsigned_lit by lia. rewrite wz_unsigned.
  2:{ split; [lia|]. apply (Z.lt_le_trans _ (2^32)); [|lia]. apply Z_bounded_by_bits; [lia|lia|].
      intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity. }
  rewrite lor_sxv_mod32 by lia. rewrite Z.lor_comm. symmetry. apply Z.mod_small.
  split; [lia|]. apply Z_bounded_by_bits; [lia|lia|].
  intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ntf_mid_post (pc : Z) (R : list cell -> word -> Prop (* [comment removed for export] *)) : Prop := True.



End CANSEC3.
