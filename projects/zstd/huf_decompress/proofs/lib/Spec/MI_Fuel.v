(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (21 recorded proofs replaced by written proofs (tle_refl, tle_trans, follow_tle and 18 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Fuel () := "C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_ri59OSSVerify5KrLib4Spec7MI_Fuel3tle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel7tle_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel8tle_sindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec7MI_Fuel3tle01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec7MI_Fuel3tle03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00k59OSSVerify5KrLib4Spec7MI_Fuel3tle02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec6Malloc<undef_reason02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel3kleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel4kle1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel:guard_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel:queue_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib7Numbers7BinNums1Z03C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel<am_take_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countablec59OSSVerify5KrLib4Spec7MI_Fuel?bad_answer_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel>am_finish_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succK59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_FuelAam_after_brk_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_FuelCactivate_group_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel;ta_fin_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc;layout_hook00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel>free_meta_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel?alloc_meta_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel<ag_tail_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel>try_avail_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel@alloc_group_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib4Spec7MI_Fuel8tle_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel9tle_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel?alloc_slot_monoC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init5Peano6le_indc59OSSVerify5KrLib4Spec7MI_Fuel:follow_tleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Fuel8prun_tleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_FuelBalloc_slot_mono_leC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Inductive tle {R : Type} : M R -> M R -> Prop :=
| tle_ret : forall r, tle (SRet r) (SRet r)
| tle_fuel : forall k t, tle (SVis (EUndef UFuel) k) t
| tle_vis : forall e k1 k2, (forall a, tle (k1 a) (k2 a)) -> tle (SVis e k1) (SVis e k2).

Lemma tle_refl {R} (t : M R) : tle t t.
Proof. induction t; constructor; auto. Qed.

Lemma tle_trans {R} (t1 t2 t3 : M R) : tle t1 t2 -> tle t2 t3 -> tle t1 t3.
Proof.
  intros H1. revert t3. induction H1 as [r|k t|e k1 k2 Hk IH]; intros t3 H2.
  - exact H2.
  - constructor.
  - inversion H2; subst.
    + constructor.
    + constructor. intros a. apply IH. auto.
Qed.

Lemma follow_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall ans r, follow t1 ans = Some r -> follow t2 ans = Some r.
Proof.
  induction 1 as [r0|k t|e k1 k2 Hk IH]; intros ans r H.
  - exact H.
  - cbn [follow] in H. destruct ans; discriminate H.
  - cbn [follow] in H |- *. destruct e; try exact H; destruct ans as [|a ans']; try discriminate H; apply IH; exact H.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

Lemma prun_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall o, tle (prun pans pupd o t1) (prun pans pupd o t2).
Proof.
  unfold prun. induction 1 as [r0|k t|e k1 k2 Hk IH]; intros o; cbn [eruns psel].
  - constructor.
  - constructor.
  - destruct e; cbn [psel]; try (constructor; intros a; apply IH). apply IH.
Qed.
End PRUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kle {X Y R} (k k' : X -> Y -> M R) : Prop := forall x y, tle (k x y) (k' x y).
Definition kle1 {X R} (k k' : X -> M R) : Prop := forall x, tle (k x) (k' x).

Ltac mono_case :=
  lazymatch goal with
  | |- tle (match ?c with _ => _ end) _ => destruct c
  end.

Ltac mono_auto cal :=
  first [ apply tle_refl
        | cal
        | (apply tle_vis; intros ?); mono_auto cal
        | mono_case; mono_auto cal
        | progress (cbv zeta); mono_auto cal ].

Lemma guard_mono {R} tag c (k k' bail bail' : M R) :
  tle k k' -> tle bail bail' -> tle (guard tag c k bail) (guard tag c k' bail').
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. constructor. intros _. exact HB. Qed.

Lemma bad_answer_mono {R} (b b' : M R) : tle b b' -> tle (bad_answer b) (bad_answer b').
Proof. intros HB. unfold bad_answer. constructor. intros _. exact HB. Qed.

Lemma queue_mono {R} h m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (queue h m st k bail) (queue h m st k' bail').
Proof.
  intros HK HB. unfold queue. apply guard_mono; [| exact HB]. apply guard_mono; [| exact HB].
  mono_auto ltac:(first [apply HK | exact HB]).
Qed.

Lemma free_meta_mono {R} m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (free_meta m st k bail) (free_meta m st k' bail').
Proof. intros HK HB. unfold free_meta. apply queue_mono; assumption. Qed.

Lemma activate_group_mono {R} m st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (activate_group m st k bail) (activate_group m st k' bail').
Proof. intros HK HB. unfold activate_group. apply guard_mono; [| exact HB]. cbv zeta. apply HK. Qed.

Lemma am_take_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_take st k bail) (am_take st k' bail').
Proof. intros HK HB. unfold am_take. mono_auto ltac:(first [apply HK | exact HB]). Qed.

Lemma am_carve_mono {R} st p (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_carve st p k bail) (am_carve st p k' bail').
Proof. intros HK HB. unfold am_carve. cbv zeta. apply am_take_mono; assumption. Qed.

Lemma am_finish_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_finish st nu k bail) (am_finish st nu k' bail').
Proof.
  intros HK HB. unfold am_finish.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_carve_mono; assumption]).
Qed.

Lemma am_after_brk_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_after_brk st nu k bail) (am_after_brk st nu k' bail').
Proof.
  intros HK HB. unfold am_after_brk.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_finish_mono; assumption]).
Qed.

Lemma alloc_meta_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (alloc_meta st k bail) (alloc_meta st k' bail').
Proof.
  intros HK HB. unfold alloc_meta.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_take_mono; assumption | apply am_after_brk_mono; assumption]).
Qed.

Lemma ta_fin_mono {R} st m mask (k k' : mstate -> Z -> M R) :
  kle k k' -> tle (ta_fin st m mask k) (ta_fin st m mask k').
Proof. intros HK. unfold ta_fin. cbv zeta. apply HK. Qed.

Lemma try_avail_mono {R} sc st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (try_avail sc st k bail) (try_avail sc st k' bail').
Proof.
  intros HK HB. unfold try_avail.
  destruct (active st sc) as [m|]; [| apply HK]. cbv zeta.
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply ta_fin_mono; exact HK|].
  mono_case.
  - destruct p as [st1 m1]. mono_case. destruct p as [st2 m2]. mono_case.
    apply activate_group_mono; [| exact HB]. intros st4 mask. apply guard_mono; [| exact HB]. apply ta_fin_mono. exact HK.
  - mono_case; [apply HK|]. constructor. intros _. exact HB.
Qed.

Lemma ag_tail_mono {R} lay st sc m p cnt ai (k k' : mstate -> optr -> M R) :
  kle k k' -> tle (ag_tail lay st sc m p cnt ai k) (ag_tail lay st sc m p cnt ai k').
Proof. intros HK. unfold ag_tail. cbv zeta. apply HK. Qed.

Section AG.
Variable R : Type.
Variable lay : layout_hook.
Variables rec rec' : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis rec_mono : forall st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' -> tle (rec st sc req k bail) (rec' st sc req k' bail').

Lemma alloc_group_mono st sc req (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' ->
  tle (alloc_group R lay rec st sc req k bail) (alloc_group R lay rec' st sc req k' bail').
Proof.
  intros HK HB. unfold alloc_group. cbv zeta. apply alloc_meta_mono; [| exact HB].
  intros st' mo. destruct mo as [m|]; [| apply HK].
  mono_case.
  - (* [comment removed for export] *)
    match goal with |- tle (let '(_, _) := ?p in _) _ => destruct p as [cnt' needed] end.
    constructor. intros r. mono_case; [apply bad_answer_mono; exact HB|].
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case. cbv zeta. apply ag_tail_mono. exact HK.
  - (* [comment removed for export] *)
    apply rec_mono; [| exact HB]. intros st1 idx.
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case; [| constructor; intros _; exact HB]. cbv zeta. apply ag_tail_mono. exact HK.
Qed.
End AG.

Lemma alloc_slot_mono lay f : forall R st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' ->
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay (S f) st sc req k' bail').
Proof.
  induction f as [|f IH]; intros R st sc req k k' bail bail' HK HB.
  - cbn [alloc_slot]. apply tle_fuel.
  - change (alloc_slot lay (S (S f)) st sc req k' bail') with
      (try_avail sc st (fun st1 first =>
         if negb (first =? 0) then k' st1 (ctz32 first)
         else alloc_group R lay (alloc_slot lay (S f)) st1 sc req (fun st2 go =>
                match go with
                | None => k' st2 (-1)
                | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                            queue (LActive sc) g st3 (fun st4 => k' st4 0) bail'
                end) bail') bail').
    cbn [alloc_slot]. apply try_avail_mono; [| exact HB]. intros st1 first.
    destruct (negb (first =? 0)); [apply HK|].
    apply (alloc_group_mono lay (alloc_slot lay f) (alloc_slot lay (S f))); [intros; apply IH; assumption| | exact HB].
    intros st2 go. destruct go as [g|]; [| apply HK]. cbv zeta. apply queue_mono; [intros ?; apply HK| exact HB].
Qed.

Lemma alloc_slot_mono_le lay f f' : (f <= f')%nat -> forall R st sc req (k : mstate -> Z -> M R) bail,
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay f' st sc req k bail).
Proof.
  induction 1 as [|f' H IH]; intros R st sc req k bail.
  - apply tle_refl.
  - eapply tle_trans; [apply IH|]. apply alloc_slot_mono; [intros ? ?; apply tle_refl| apply tle_refl].
Qed.

(* [comment removed for export] *)
Section LEAF.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Lemma alloc_slot_follow_mono lay f f' R st sc req (k : mstate -> Z -> M R) bail o ans r :
  (f <= f')%nat ->
  follow (prun pans pupd o (alloc_slot lay f st sc req k bail)) ans = Some r ->
  follow (prun pans pupd o (alloc_slot lay f' st sc req k bail)) ans = Some r.
Proof. intros Hf H. eapply follow_tle; [apply prun_tle; apply alloc_slot_mono_le; exact Hf| exact H]. Qed.
End LEAF.
