(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (24 recorded proofs replaced by written proofs (bf_meta, bf_meta_other, bm_meta and 21 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocFacts_A MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp AllocSlot_iface F_malloc_join F_malloc_core MallocHINV.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_big () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_insertC47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_neI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib6Malloc=F_malloc_bigw8big_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Malloc=F_malloc_bigw9big_metaAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<F_malloc_big6bf_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib6Malloc=F_malloc_bigw6big_mlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc=F_malloc_bigw9big_ml_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<F_malloc_big9big_finalC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Malloc:MallocTree9range_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib6Malloc8ProgDeps9neg_errnoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode6avoidsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib6Malloc<MallocKit_A2Ammap_len_round_upC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=is_errno_formC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsBsubrelation_properC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib5Nodes>wa_unsigned_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C45stdpp;list_basics4list;list_filterC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterC57Corelib7BinNums6IntDef1Z3divC35stdpp8fin_maps<lookup_emptyC59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib6Malloc9Malloc_fp>round_up_pg_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<F_malloc_big@round_up_pg_4115C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<F_malloc_big9bf_strideC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
  let needed := n + IB + UNIT in
  let st4 := upd_meta g (fun mr =>
               m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
  let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

Lemma bf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma bf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma bm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bf_regions : s_regions stF = s_regions st3.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_big ()) ["CANSEC1"; "FINAL"] "p;4p;1p;2g00BAj42Tg00iTj11Tg00O^j20Tg00`Sg00aOg00bAg00jNC2p,3st3#1'0o"). Qed.
Lemma bf_areas : s_areas stF = s_areas st3.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_big ()) ["CANSEC1"; "FINAL"] "p;4p;6p;1p;2g00P8j44Tg00PVj63Tg00BAj40Tg00kGj11Tg00O^j22Tg002:g00`SR0g00aOR1g00a1R2g00ahR3C4P0P1g00bAP2P3g00b_E3g00l?C0p,3st3#1'2o"). Qed.
Lemma bf_reserved : s_reserved stF = s_reserved st3.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_big ()) ["CANSEC1"; "FINAL"] "p;2p;1g00E4j23Tg00m6j12Tg00mVj10Tg00O^j21Tg00a1R0/30#2p,3st3#0'1o"). Qed.
Lemma bf_next : s_next_rid stF = s_next_rid st3.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_big ()) ["CANSEC1"; "FINAL"] "p;1p;2g00nQj11Tg00O^j20Tg00`Sp,3st3#1'0o"). Qed.
Lemma bf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma bm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
Lemma bf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. reflexivity. Qed.
Lemma bf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma bf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma bf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite bf_ctx. reflexivity. Qed.

Lemma ticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma bf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma bf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
  malloc_core full_lay st1 n =
    SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (s_atop st1) (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
      if is_err r then ret (st1, None) else
      let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
      alloc_meta (step_seq st2) (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
        | Some g => ret (big_final st3 g rid n, Some (g, 0))
        end) (ret (st1, None))).
Proof.
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma unk_agree_transfer st st' o m m' :
  unk_agree st o m ->
  (forall rid r, (s_regions st') !! rid = Some r -> r_kind r = RKGroup ->
     ((s_regions st) !! rid = Some r /\ get_shadow st' rid = get_shadow st rid /\
       (forall off, grp_hdr_cov st rid off -> grp_hdr_cov st' rid off) /\
       (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st rid) off = Unknown h ->
          ~ grp_hdr_cov st' rid off -> m' (wa (r_base r + off)) = m (wa (r_base r + off))))
     \/ (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st' rid) off = Unknown h -> grp_hdr_cov st' rid off)) ->
  unk_agree st' o m'.
Proof.
  intros UA H rid r off h Hr Hk Ho Hc NG.
  destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
  - rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
  - exfalso. apply NG. eapply NEW; eauto.
Qed.

Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. intros EG (b & gh & Hb & E & R). exists b, gh. rewrite EG. auto. Qed.

(* [comment removed for export] *)
Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|b]; cbn [range_val]; intros He.
  - unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
    replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (2 ^ 64 - e =? 0); reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_answer_ok_err live len e : 1 <= e <= 4095 -> mmap_answer_ok ATOP live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof.
  intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
  - replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_lt. lia.
Qed.

Lemma mmap_answer_ok_addr live len xa : 0 <= len ->
  mmap_addr_ok ATOP len [] xa = true -> mmap_answer_ok ATOP live len xa = true ->
  0 < xa /\ xa mod 4096 = 0 /\ xa + round_up_pg len <= ATOP /\ ranges_free live xa (round_up_pg len) = true /\ is_err xa = false.
Proof.
  intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
  apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
  change page_size with 4096 in A1.
  unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
  assert (NE : is_errno_form xa = false).
  { unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; atop_facts; lia). reflexivity. }
  destruct B as [B|B]; [rewrite NE in B; discriminate|].
  rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
  repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. atop_facts. lia.
Qed.

Lemma brk_link_ps_ext st st' s :
  c_brk (ctx st') = c_brk (ctx st) ->
  (forall rid off, c_brk (ctx st) = BrkLive rid off -> conc st' (rid, off) = conc st (rid, off)) ->
  brk_link_ps st s -> brk_link_ps st' s.
Proof.
  intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
  rewrite (EC rid off eq_refl). exact BL.
Qed.

Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) :
  0 <= lo -> hi <= 2^64 ->
  (forall a, 0 <= a < 2^64 -> (a < lo \/ hi <= a) -> m' (wa a) = m (wa a)) -> munch [(lo, hi)] m m'.
Proof.
  intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
  cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
  destruct (Z.eq_dec (off / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
    replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
    replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma big_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite bf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMP_BIG (am_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, AREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (s_atop (set_tick t st)) (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  am_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

Section BIG.
Variable am_pre : mstate -> Prop.
Hypothesis AMP : AMP_BIG am_pre.
End BIG.


End CANSEC1.
