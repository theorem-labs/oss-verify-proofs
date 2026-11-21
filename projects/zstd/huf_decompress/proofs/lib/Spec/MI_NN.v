(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (25 recorded proofs replaced by written proofs (nn_ret, nn_sbind, nn_mono and 22 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_NN () := "c59OSSVerify5KrLib4Spec5MI_NN2nnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN6nn_retC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN3okzC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec5MI_NN8nn_undefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00c59OSSVerify5KrLib4Spec5MI_NN=nn_bad_answerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN8nn_guardC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN:nn_vis_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN8nn_queueC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes2idK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN:nn_am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00c59OSSVerify5KrLib4Spec5MI_NN;nn_am_carveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib4Spec5MI_NN<nn_am_finishC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN9land_mapfC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN?nn_am_after_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN9nn_ta_finC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NNAnn_activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc;layout_hook00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN:nn_ag_tailC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec5MI_NN=nn_alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z;log2_nonnegC59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN<ctz32_nonnegC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib4Spec5MI_NN>nn_alloc_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN<nn_try_availC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K59OSSVerify5KrLib4Spec6Malloc<undef_reason02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorc59OSSVerify5KrLib4Spec5MI_NN=nn_alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec5MI_NNDnn_malloc_small_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN>nn_malloc_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MI_NN8nn_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8lay_noneC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition okz (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = false \/ is_err z = false
  | EMprotect _ _ _ => z = 0
  | EUndef _ => False
  | _ => True
  end.

Fixpoint nn {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => forall z, okz e z -> nn P (k z)
  end.

Lemma nn_ret {R} (P : R -> Prop) r : P r -> nn P (ret r).
Proof. intros H. exact H. Qed.

Lemma nn_sbind {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  nn P1 t -> (forall r, P1 r -> nn P (f r)) -> nn P (sbind t f).
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H Hf.
  - apply Hf. exact H.
  - intros z Hz. apply IH; [apply H; exact Hz| exact Hf].
Qed.

Lemma nn_mono {R} (P P' : R -> Prop) (t : M R) : nn P t -> (forall r, P r -> P' r) -> nn P' t.
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H HP.
  - apply HP. exact H.
  - intros z Hz. apply IH; [apply H; exact Hz| exact HP].
Qed.

Lemma nn_undef {R} (P : R -> Prop) w (k : Z -> M R) : nn P (SVis (EUndef w) k).
Proof. intros z []. Qed.

Lemma nn_bad_answer {R} (P : R -> Prop) (bail : M R) : nn P (bad_answer bail).
Proof. apply nn_undef. Qed.

Lemma nn_guard {R} (P : R -> Prop) tag c (k bail : M R) : nn P k -> nn P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H| apply nn_undef]. Qed.

(* [comment removed for export] *)
Lemma nn_vis_any {R} (P : R -> Prop) e (k : Z -> M R) : (forall z, nn P (k z)) -> nn P (SVis e k).
Proof. intros H z _. apply H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Walk.
Context {R : Type} (P : R -> Prop).

Lemma nn_queue h m st (k : mstate -> M R) bail : (forall st', nn P (k st')) -> nn P (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply nn_guard. apply nn_guard. destruct (get_head st h); apply Hk.
Qed.

Lemma nn_free_meta m st (k : mstate -> M R) bail : (forall st', nn P (k st')) -> nn P (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply nn_queue. exact Hk. Qed.

Lemma nn_activate_group m st (k : mstate -> Z -> M R) bail :
  (forall st' z, nn P (k st' z)) -> nn P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply nn_guard. apply Hk. Qed.

Lemma nn_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk| apply nn_undef]. Qed.

Lemma nn_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply nn_am_take. exact Hk. Qed.

Lemma nn_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [| apply nn_undef].
  match goal with |- nn P (if ?c then _ else _) => destruct c end; [| apply nn_am_carve; exact Hk].
  intros z Hz. cbn in Hz. subst z.
  replace (negb (mprotect_answer_ok 0)) with false by reflexivity.
  replace ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true by reflexivity. cbn iota. apply nn_am_carve. exact Hk.
Qed.

Lemma land_mapf : (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) = true.
Proof. reflexivity. Qed.

Lemma nn_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [| apply nn_am_finish; exact Hk].
  intros z Hz. cbn [okz] in Hz. rewrite land_mapf in Hz. destruct Hz as [Hz|Hz]; [discriminate|].
  destruct (negb _); [apply nn_bad_answer|]. rewrite Hz.
  destruct (new_region _ _ _ _) as [st1 rid]. apply nn_am_finish. exact Hk.
Qed.

Lemma nn_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else _). clearbody st0.
  destruct (c_free_meta_head (ctx st0)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply nn_am_take; exact Hk|].
  match goal with |- nn P (if ?c then _ else _) => destruct c end; [| apply nn_am_after_brk; exact Hk].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - apply nn_vis_any. intros cur. destruct (negb (brk0_answer_ok cur)); [apply nn_bad_answer|].
    apply nn_vis_any. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply nn_bad_answer|].
    destruct (negb (r =? _)); [apply nn_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [apply nn_bad_answer|].
    apply nn_vis_any. intros rg. destruct (negb (mmap_fixed_answer_ok _ rg)); [apply nn_bad_answer|].
    destruct (new_region _ _ _ _) as [st1 rid]. apply nn_am_after_brk; exact Hk.
  - apply nn_am_after_brk; exact Hk.
  - apply nn_vis_any. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply nn_bad_answer|].
    destruct (negb (r =? _)); [apply nn_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [apply nn_bad_answer|].
    apply nn_am_after_brk; exact Hk.
Qed.

Lemma nn_ta_fin st m mask (k : mstate -> Z -> M R) : (forall st' z, nn P (k st' z)) -> nn P (ta_fin st m mask k).
Proof. intros Hk. unfold ta_fin. apply Hk. Qed.

Lemma nn_try_avail sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, nn P (k st' z)) -> nn P (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [| apply Hk].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply nn_ta_fin; exact Hk|].
  match goal with |- nn P (match ?s with Some _ => _ | None => _ end) => destruct s as [[st1 m1]|] end.
  2:{ destruct (m_freed _ =? 0); [apply Hk| apply nn_undef]. }
  match goal with |- nn P (let (a, b) := ?x in _) => destruct x as [[st2 m2] mask] end.
  match goal with |- nn P (let (a, b) := ?x in _) => destruct x as [st3 m3] end.
  apply nn_activate_group. intros st4 z. apply nn_guard. apply nn_ta_fin. exact Hk.
Qed.

Lemma nn_ag_tail lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  (forall st', nn P (k st' (Some m))) -> nn P (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma nn_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail :
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1, (forall st' idx, 0 <= idx -> nn P (k1 st' idx)) -> nn P (asr st1 sc1 req1 k1 bail1)) ->
  (forall st' m, nn P (k st' (Some m))) -> nn P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr Hk. unfold alloc_group. apply nn_alloc_meta. intros st1 m. cbv beta iota.
  match goal with |- nn P (if ?c then _ else _) => destruct c end.
  - (* [comment removed for export] *)
    match goal with |- nn P (let (a, b) := ?x in _) => destruct x as [cnt needed] end.
    intros z Hz. cbn [okz] in Hz. rewrite land_mapf in Hz. destruct Hz as [Hz|Hz]; [discriminate|].
    destruct (negb _); [apply nn_bad_answer|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st2 rid]. apply nn_ag_tail. intros st'. apply Hk.
  - (* [comment removed for export] *)
    apply Hasr. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _) as [g|]; [| apply nn_undef]. apply nn_ag_tail. intros st''. apply Hk.
Qed.

Lemma ctz32_nonneg first : 0 <= ctz32 first.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma nn_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  (forall st' idx, 0 <= idx -> nn P (k st' idx)) -> nn P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [apply nn_undef|].
  apply nn_try_avail. intros st1 first. destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply nn_alloc_group; [exact IH|]. intros st2 g. cbv beta iota. apply nn_queue. intros st4. apply Hk. lia.
Qed.

Lemma nn_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  (forall st' g idx, nn P (k st' (Some (g, idx)))) -> nn P (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl.
  match goal with |- nn P (match ?g with Some _ => _ | None => _ end) => destruct g as [gp|] end.
  - destruct (negb _); [apply Hk|].
    apply nn_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk| apply nn_undef].
  - cbn iota. apply nn_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk| apply nn_undef].
Qed.

End Walk.

Lemma nn_malloc_core lay st n : size_overflows n = false ->
  nn (fun r => exists g idx, snd r = Some (g, idx)) (malloc_core lay st n).
Proof.
  intros Hn. unfold malloc_core. rewrite Hn.
  destruct (MMAP_THRESHOLD <=? n).
  - intros z Hz. cbn [okz] in Hz. rewrite land_mapf in Hz. destruct Hz as [Hz|Hz]; [discriminate|].
    destruct (negb _); [apply nn_bad_answer|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st1 rid]. apply nn_alloc_meta. intros st3 g. cbv beta iota.
    apply nn_ret. cbn. eauto.
  - apply nn_malloc_small_ctrl. intros st' g idx. apply nn_ret. cbn. eauto.
Qed.

Theorem cmalloc_nn cs n : size_overflows n = false -> nn (fun r => snd r <> None) (cmalloc cs n).
Proof.
  intros Hn. unfold cmalloc. eapply nn_sbind; [apply nn_malloc_core; exact Hn|].
  intros [st1 r] (g & idx & E). cbn in E. subst r. apply nn_ret. cbn. discriminate.
Qed.
