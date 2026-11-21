(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (31 recorded proofs replaced by written proofs (pw_extP, get_meta_rec_extP, meta_cells_extP and 28 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require KStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocKit_A2 () := "C47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00C35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib6Malloc:MallocTree7optr_inC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums1Z01C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01c59OSSVerify5KrLib6Malloc<MallocKit_A27pw_extPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_A28agree_onC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib4Spec5KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C35stdpp8fin_maps<lookup_emptyK59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_A2:nr_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00I47Corelib4Init5Logic2or00K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01c59OSSVerify5KrLib6Malloc<MallocKit_A2=nr_lookup_oldC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib6Malloc<MallocKit_A2=nr_lookup_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>In_live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Malloc:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deletec59OSSVerify5KrLib6Malloc<MallocKit_A2:dr_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_A2=dr_lookup_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N7compareK47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_A2Fptrs_in_upd_ctx_scalarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma pw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma get_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma meta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !pw_extP by assumption. reflexivity.
Qed.
End PEXT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (m m' : mem) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma agree_on_sub m m' A n A' n' : agree_on m m' A n -> A <= A' -> A' + n' <= A + n -> agree_on m m' A' n'.
Proof. intros AG H1 H2 a Ha. apply AG. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_round_up l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply KStep.round_up_pg_eq. Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= ATOP.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma nr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
Lemma nr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma nr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite nr_lookup_new in H. inversion H. auto.
  - right. rewrite nr_lookup_old in H by exact NE. auto.
Qed.
Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.
Lemma nr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite nr_lookup_new. reflexivity. Qed.
Lemma nr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
Lemma nr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
Lemma nr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma ticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x408 \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma dr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma dr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
  intros H. rewrite dr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma dr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite dr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma dr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite dr_lookup_old by assumption. reflexivity. Qed.
Lemma dr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma ticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ptrs_in_set_tick P st t : ptrs_in P st -> ptrs_in P (set_tick t st).
Proof. intros H; exact H. Qed.
Lemma ptrs_in_upd_ctx_scalar P st f :
  (forall c, c_free_meta_head (f c) = c_free_meta_head c) -> (forall c, c_avail_meta (f c) = c_avail_meta c) ->
  (forall c, c_meta_area_head (f c) = c_meta_area_head c) -> (forall c, c_meta_area_tail (f c) = c_meta_area_tail c) ->
  (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) -> (forall c, c_active (f c) = c_active c) ->
  (forall c, c_brk (f c) = c_brk c) ->
  ptrs_in P st -> ptrs_in P (upd_ctx f st).
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E1, E2, E3, E4, E5, E6, E7.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.
Lemma ptrs_in_step_seq P st : ptrs_in P st -> ptrs_in P (step_seq st).
Proof. intros H. unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply ptrs_in_upd_ctx_scalar; [..|exact H]; reflexivity). Qed.
Lemma ptrs_in_put_meta P st g mr :
  optr_in P (m_prev mr) -> optr_in P (m_next mr) -> optr_in P (m_mem mr) ->
  ptrs_in P st -> ptrs_in P (put_meta g mr st).
Proof.
  intros Q1 Q2 Q3 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
  destruct (decide (g' = g)) as [->|NE].
  - rewrite lookup_insert_eq. cbn. auto.
  - rewrite lookup_insert_ne by congruence. apply H8.
Qed.
Lemma ptrs_in_put_group P st b mo ai :
  P (fst b) -> optr_in P mo -> ptrs_in P st -> ptrs_in P (put_group b mo ai st).
Proof.
  intros Q1 Q2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx put_group set_groups s_metas s_areas s_groups get_meta_rec] in *.
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [exact H8|]. split; [exact H9|].
  intros b' gh Hb'. destruct (decide (b' = b)) as [->|NE].
  - rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. cbn. auto.
  - rewrite lookup_insert_ne in Hb' by congruence. exact (H10 b' gh Hb').
Qed.
Lemma ptrs_in_hdr_havoc P st b : ptrs_in P st -> ptrs_in P (hdr_havoc b st).
Proof. intros H; exact H. Qed.
Lemma ptrs_in_set_slots P st v : ptrs_in P st -> ptrs_in P (set_slots v st).
Proof. intros H; exact H. Qed.

End CANSEC1.
