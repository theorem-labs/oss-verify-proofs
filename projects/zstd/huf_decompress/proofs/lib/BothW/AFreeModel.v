(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (afree_fast_eq, enq_app_Some, enq_app_None and 15 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeModel () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6lookupC35stdpp4base6deleteI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List7existsbC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec8AsanCtrl8set_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9set_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec8AsanCtrl7recycleC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec8AsanCtrl7enqueueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=recycle_chunkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel7enq_newC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aundef04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec8AsanCtrlAcls_set_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCpopulate_free_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec8AsanCtrl5drainC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List3revK47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib4Spec8AsanCtrl6abatch01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;cache_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aundef03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00K59OSSVerify5KrLib4Spec8AsanCtrl6aundef02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4bool02C35stdpp4base6LookupC35stdpp4base6DeleteI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6astate01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List>rev_involutiveK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC47Corelib4Init9Datatypes2idC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec8AsanCtrl7set_clsC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel<enq_app_SomeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel9same_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel>get_cls_put_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel@get_cls_set_qlocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel>get_cls_put_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib5BothW:AFreeModel>same_core_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<flat_map_appC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List6filterc59OSSVerify5KrLib5BothW:AFreeModel5qfiltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_appc59OSSVerify5KrLib5BothW:AFreeModelCflat_map_app_chunksC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapc59OSSVerify5KrLib5BothW:AFreeModel=enq_app_qfiltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel=enq_new_qfiltC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_commC46Stdlib7Sorting;Permutation@Permutation_reflI46Stdlib7Sorting;Permutation;Permutation00c59OSSVerify5KrLib5BothW:AFreeModel>st_after_qfiltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeModel<st_enq_qfiltC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition enq_app (st1 : astate) (ch : achunk) : option astate :=
  match rev (a_qloc st1) with
  | b :: rl => if b_count b =? Q_BATCH then None
               else Some (set_qloc (rev (mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b) :: rl))
                                   (a_qloc_bytes st1 + chunk_size ch) st1)
  | [] => None
  end.
(* [comment removed for export] *)
Definition enq_new (st1 : astate) (ch : achunk) : astate :=
  let r := get_cls st1 K_BATCH_CLASS in
  let st2 := put_cls K_BATCH_CLASS (cls_set_count (c_count r - 1) r) st1 in
  set_qloc (a_qloc st2 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st2 + chunk_size ch + Q_BATCH_BYTES) st2.
Definition st_enq (st1 : astate) (ch : achunk) : astate :=
  match enq_app st1 ch with Some s => s | None => enq_new st1 ch end.
(* [comment removed for export] *)
Definition st_after (st2 : astate) : astate :=
  if Q_CACHE <? a_qloc_bytes st2
  then set_qglob (a_qglob st2 ++ a_qloc st2) (a_qglob_bytes st2 + a_qloc_bytes st2) (set_qloc [] 0 st2)
  else st2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afree_fast_eq : forall st p ch,
  (a_live st) !! p = Some ch -> chunk_size ch <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  (enq_app st1 ch = None -> 0 < c_count (get_cls st1 K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes (st_enq st1 ch) -> a_qglob_bytes (st_enq st1 ch) + a_qloc_bytes (st_enq st1 ch) <= Q_MAX) ->
  afree st (Some p) = aret (st_after (st_enq st1 ch)).
Proof.
  intros st p ch LIVE SZ st1 CNT NOREC.
  assert (AFTER : forall st2, (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
            (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2) = @aret astate (st_after st2)).
  { intros st2 NR. unfold st_after, drain.
    destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; [|reflexivity].
    cbn [a_qglob_bytes set_qglob].
    destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [LT2|GE2]; [exfalso; specialize (NR LT); lia| reflexivity]. }
  unfold afree. rewrite LIVE. fold st1.
  replace (chunk_size ch <=? Q_MAX) with true by (symmetry; apply Z.leb_le; exact SZ).
  unfold enqueue. unfold st_enq in *. unfold enq_app in *.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - unfold cache_alloc. specialize (CNT eq_refl).
    replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
    cbn [negb]. unfold enq_new in *. apply AFTER. exact NOREC.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [FULL|NF].
    + unfold cache_alloc. specialize (CNT eq_refl).
      replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
      cbn [negb]. unfold enq_new in *. apply AFTER. exact NOREC.
    + apply AFTER. exact NOREC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma enq_app_Some : forall st1 ch s, enq_app st1 ch = Some s ->
  exists l b, a_qloc st1 = l ++ [b] /\ b_count b <> Q_BATCH
    /\ s = set_qloc (l ++ [mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b)]) (a_qloc_bytes st1 + chunk_size ch) st1.
Proof.
  intros st1 ch s E. unfold enq_app in E.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (Z.eqb_spec (b_count b) Q_BATCH) as [F|NF]; [discriminate|].
  injection E as <-. exists (rev rl), b.
  assert (Q : a_qloc st1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc st1)), RV; reflexivity).
  split; [exact Q|]. split; [exact NF|]. cbn [rev]. reflexivity.
Qed.

Lemma enq_app_None : forall st1 ch, enq_app st1 ch = None ->
  a_qloc st1 = [] \/ exists l b, a_qloc st1 = l ++ [b] /\ b_count b = Q_BATCH.
Proof.
  intros st1 ch E. unfold enq_app in E.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - left. rewrite <- (rev_involutive (a_qloc st1)), RV. reflexivity.
  - right. destruct (Z.eqb_spec (b_count b) Q_BATCH) as [F|NF]; [|discriminate].
    exists (rev rl), b. split; [| exact F]. rewrite <- (rev_involutive (a_qloc st1)), RV. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fields.
Variables (st : astate) (p : aptr) (ch : achunk).
Let st1 := set_live (delete p (a_live st)) st.

Lemma st1_fields :
  a_live st1 = delete p (a_live st) /\ a_cls st1 = a_cls st /\ a_next st1 = a_next st /\ a_cinit st1 = a_cinit st
  /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st /\ a_qglob st1 = a_qglob st /\ a_qglob_bytes st1 = a_qglob_bytes st
  /\ a_space_beg st1 = a_space_beg st /\ a_ptr_array st1 = a_ptr_array st /\ a_nres st1 = a_nres st /\ a_nsec st1 = a_nsec st.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition same_core (s s' : astate) : Prop :=
  a_live s' = a_live s /\ a_next s' = a_next s /\ a_cinit s' = a_cinit s
  /\ a_space_beg s' = a_space_beg s /\ a_ptr_array s' = a_ptr_array s /\ a_nres s' = a_nres s /\ a_nsec s' = a_nsec s
  /\ (forall c, c <> K_BATCH_CLASS -> get_cls s' c = get_cls s c)
  /\ c_mapped_user (get_cls s' K_BATCH_CLASS) = c_mapped_user (get_cls s K_BATCH_CLASS)
  /\ c_allocated_user (get_cls s' K_BATCH_CLASS) = c_allocated_user (get_cls s K_BATCH_CLASS)
  /\ c_num_freed (get_cls s' K_BATCH_CLASS) = c_num_freed (get_cls s K_BATCH_CLASS)
  /\ c_mapped_free_array (get_cls s' K_BATCH_CLASS) = c_mapped_free_array (get_cls s K_BATCH_CLASS).

Lemma same_core_refl : forall s, same_core s s.
Proof. intros s. repeat split; intros; reflexivity. Qed.

Lemma get_cls_put_eq : forall c r s, get_cls (put_cls c r s) c = r.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_cls_put_ne : forall c c' r s, c' <> c -> get_cls (put_cls c r s) c' = get_cls s c'.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma enq_app_core : forall s1 s, enq_app s1 ch = Some s -> same_core s1 s /\ a_qglob s = a_qglob s1 /\ a_qglob_bytes s = a_qglob_bytes s1.
Proof.
  intros s1 s E. destruct (enq_app_Some s1 ch s E) as (l & b & Q & NF & ->).
  split; [| split; reflexivity]. repeat split; intros; reflexivity.
Qed.

Lemma get_cls_set_qloc : forall l b s c, get_cls (set_qloc l b s) c = get_cls s c.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeModel ()) ["CANSEC1"; "Fields"] "h01bh11ch21lh31sp;1p;2p10000p4p710p1000Mp4p710R0p8p1000kp4p710R1p1001IR2p4p710R3p8P1P2p4p7210R2p8p1001bp4p70R4p1002Yp4p710p8P4p10035R5p4p710p8P4p1003NR6p4p710p8P4p101G@R7p4p710R8p8P4p101GTp4p710p8p1004VR4p4p73101R9p10050R:p4p73110p8P9p1005IR;p4p73110p8P9p1005ep4p710p8P9p10068R<p4p7201p8P9p1006Jp4p7201p8P9P7p4p73110p8P9p1006\R7p4p73110p8P9p10070R=p4p73110p8P9p1007Jp4p7201p8P4p4p710R9P:p4p710p8P9P;p4p710p8P9P3p8P9P2p8P9P8p8P9P7p4p710p8P9P=p4p710p8p1007]R=p4p710R9P1p8P9P3p8P9P2p8P9p10081p4p73110p8P=p4p741110R=p1008Cp4p73101p8p1008_p4p710P0p8p1009;p4p7<111111111110P0p8p1009]p4p7<111111111110P0p8P5p4p741110R5P4p4p7511100R0p8P0P5p8p100:?p4p741110R5P4p4p76111100R0p8P0P5p8P6p4p741110R6P4p4p771111100R5p8P5P6p8p100:Wp4p741110R6P4p4p7:1111111100R4p8P4P6p8P<p4p7200R<P=p8P=P<p8g00Lej12Tg00i?j21Tg00SKj20Tg017>#2g01>iR<g0189g01THf1f0'1'0X1<W3W0W2o"). Qed.
Lemma get_cls_set_qglob : forall l b s c, get_cls (set_qglob l b s) c = get_cls s c.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeModel ()) ["CANSEC1"; "Fields"] "h01bh11ch21lh31sp;1p;2p10000p4p710p1000Mp4p710R0p8p1000kp4p710R1p1001IR2p4p710R3p8P1P2p4p7210R2p8p1001bp4p70R4p1002Yp4p710p8P4p10035R5p4p710p8P4p1003NR6p4p710p8P4p101G@R7p4p710R8p8P4p101GTp4p710p8p1004VR4p4p73101R9p10050R:p4p73110p8P9p1005IR;p4p73110p8P9p1005ep4p710p8P9p10068R<p4p7201p8P9p1006Jp4p7201p8P9P7p4p73110p8P9p1006\R7p4p73110p8P9p10070R=p4p73110p8P9p1007Jp4p7201p8P4p4p710R9P:p4p710p8P9P;p4p710p8P9P3p8P9P2p8P9P8p8P9P7p4p710p8P9P=p4p710p8p1007]R=p4p710R9P1p8P9P3p8P9P2p8P9p10081p4p73110p8P=p4p741110R=p1008Cp4p73101p8p1008_p4p710P0p8p1009;p4p7<111111111110P0p8p1009]p4p7<111111111110P0p8P5p4p741110R5P4p4p7511100R0p8P0P5p8p100:?p4p741110R5P4p4p76111100R0p8P0P5p8P6p4p741110R6P4p4p771111100R5p8P5P6p8p100:Wp4p741110R6P4p4p7:1111111100R4p8P4P6p8P<p4p7200R<P=p8P=P<p8g00Lej12Tg00i?j21Tg00SKj20Tg017>#2g01>iR<g0189g01THf1f0'1'0X1<W3W0W2o"). Qed.

Lemma enq_new_core : forall s1,
  same_core s1 (enq_new s1 ch) /\ a_qglob (enq_new s1 ch) = a_qglob s1 /\ a_qglob_bytes (enq_new s1 ch) = a_qglob_bytes s1
  /\ c_count (get_cls (enq_new s1 ch) K_BATCH_CLASS) = c_count (get_cls s1 K_BATCH_CLASS) - 1
  /\ a_qloc (enq_new s1 ch) = a_qloc s1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]
  /\ a_qloc_bytes (enq_new s1 ch) = a_qloc_bytes s1 + chunk_size ch + Q_BATCH_BYTES
  /\ a_cls (enq_new s1 ch) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls s1 K_BATCH_CLASS) - 1) (get_cls s1 K_BATCH_CLASS) ]> (a_cls s1).
Proof.
  intros s1. unfold enq_new. cbv zeta. rewrite !get_cls_set_qloc, !get_cls_put_eq.
  split.
  { unfold same_core. rewrite !get_cls_set_qloc, !get_cls_put_eq. repeat split; try reflexivity.
    intros c NE. rewrite get_cls_set_qloc, get_cls_put_ne by exact NE. reflexivity. }
  repeat split; reflexivity.
Qed.

Lemma same_core_trans : forall s1 s2 s3, same_core s1 s2 -> same_core s2 s3 -> same_core s1 s3.
Proof.
  intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  unfold same_core. rewrite B1, B2, B3, B4, B5, B6, B7, B9, B10, B11, B12.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
  split; [intros c NE; rewrite (B8 c NE); exact (A8 c NE)|].
  split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

Lemma st_after_q : forall s2,
  (Q_CACHE < a_qloc_bytes s2 -> a_qloc (st_after s2) = [] /\ a_qloc_bytes (st_after s2) = 0
      /\ a_qglob (st_after s2) = a_qglob s2 ++ a_qloc s2 /\ a_qglob_bytes (st_after s2) = a_qglob_bytes s2 + a_qloc_bytes s2)
  /\ (a_qloc_bytes s2 <= Q_CACHE -> st_after s2 = s2).
Proof.
  intros s2. unfold st_after. split; intros H.
  - replace (Q_CACHE <? a_qloc_bytes s2) with true by (symmetry; apply Z.ltb_lt; exact H). repeat split; reflexivity.
  - replace (Q_CACHE <? a_qloc_bytes s2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma st_after_core : forall s2, same_core s2 (st_after s2) /\ a_cls (st_after s2) = a_cls s2.
Proof.
  intros s2. unfold st_after. destruct (Q_CACHE <? a_qloc_bytes s2); [| split; [apply same_core_refl| reflexivity]].
  split; [| reflexivity]. repeat split; intros; reflexivity.
Qed.
End Fields.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qfilt (f : achunk -> bool) (s : astate) : list achunk :=
  List.filter f (flat_map b_chunks (a_qloc s ++ a_qglob s)).

Lemma flat_map_app_chunks : forall (l1 l2 : list abatch), flat_map b_chunks (l1 ++ l2) = flat_map b_chunks l1 ++ flat_map b_chunks l2.
Proof. intros. apply flat_map_app. Qed.

Lemma enq_app_qfilt : forall f s1 ch s, f ch = false -> enq_app s1 ch = Some s -> qfilt f s = qfilt f s1.
Proof.
  intros f s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. reflexivity.
Qed.

Lemma enq_new_qfilt : forall f s1 ch, f ch = false -> qfilt f (enq_new s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma st_enq_qfilt : forall f s1 ch, f ch = false -> qfilt f (st_enq s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt f s1 ch s Hf E)| exact (enq_new_qfilt f s1 ch Hf)].
Qed.

Lemma st_after_qfilt : forall f s2, Permutation (qfilt f (st_after s2)) (qfilt f s2).
Proof.
  intros f s2. unfold st_after, qfilt. destruct (Q_CACHE <? a_qloc_bytes s2); [| apply Permutation_refl].
  cbn [a_qloc a_qglob set_qglob set_qloc app]. rewrite !flat_map_app_chunks, !List.filter_app. apply Permutation_app_comm.
Qed.

Lemma st_after_enq_qfilt : forall f s1 ch, f ch = false -> Permutation (qfilt f (st_after (st_enq s1 ch))) (qfilt f s1).
Proof.
  intros f s1 ch Hf. rewrite <- (st_enq_qfilt f s1 ch Hf). apply st_after_qfilt.
Qed.
End CANSEC1.
