(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (after_rec_eq, afree_rec_eq, KB_apop_rec_eq)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ARefill_iface AFreeModel AFreeRead AFreeModelR.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeModelC () := "C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6LookupC35stdpp4base6DeleteC59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec8AsanCtrl8set_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9set_qglobC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl5drainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7recycleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp4base6deleteI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib5BothW;AFreeModelC<after_rec_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec8AsanCtrl7enqueueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=recycle_chunkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_newC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K59OSSVerify5KrLib4Spec8AsanCtrl6aundef04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec8AsanCtrlAcls_set_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCpopulate_free_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib4Spec8AsanCtrl6abatch01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;cache_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aundef03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK59OSSVerify5KrLib4Spec8AsanCtrl6aundef02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5BothW9AFreeRead?enq_is_app_specC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5BothW=ARefill_iface4apopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFreeModelR2KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFreeModelR6afterKC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma after_rec_eq : forall st2,
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)
  = recycle (st_after st2) Q_MIN (fun st3 => @aret astate st3)
  /\ a_qloc (st_after st2) = [] /\ a_qloc_bytes (st_after st2) = 0
  /\ a_qglob (st_after st2) = a_qglob st2 ++ a_qloc st2 /\ a_qglob_bytes (st_after st2) = a_qglob_bytes st2 + a_qloc_bytes st2.
Proof.
  intros st2 QC REC. unfold st_after, drain.
  replace (Q_CACHE <? a_qloc_bytes st2) with true by (symmetry; apply Z.ltb_lt; exact QC).
  cbn [a_qglob_bytes a_qloc a_qloc_bytes a_qglob set_qglob set_qloc].
  replace (Q_MAX <? a_qglob_bytes st2 + a_qloc_bytes st2) with true by (symmetry; apply Z.ltb_lt; exact REC).
  repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma afree_rec_eq : forall st p ch,
  (a_live st) !! p = Some ch -> chunk_size ch <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  (enq_app st1 ch = None -> 0 < c_count (get_cls st1 K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  afree st (Some p) = recycle (st_after st2) Q_MIN (fun st3 => aret st3).
Proof.
  intros st p ch LIVE SZ st1 st2 CNT QC REC.
  pose proof (proj1 (after_rec_eq st2 QC REC)) as AFTER.
  unfold afree. rewrite LIVE. fold st1.
  replace (chunk_size ch <=? Q_MAX) with true by (symmetry; apply Z.leb_le; exact SZ).
  unfold enqueue. subst st2. unfold st_enq in *. unfold enq_app in *.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - unfold cache_alloc. specialize (CNT eq_refl).
    replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
    cbn [negb]. unfold enq_new in *. exact AFTER.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [FULL|NF].
    + unfold cache_alloc. specialize (CNT eq_refl).
      replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
      cbn [negb]. unfold enq_new in *. exact AFTER.
    + exact AFTER.
Qed.

(* [comment removed for export] *)
Lemma KB_apop_rec_eq : forall s ch,
  enq_is_app s = false ->
  Q_CACHE < a_qloc_bytes (st_enq s ch) -> Q_MAX < a_qglob_bytes (st_enq s ch) + a_qloc_bytes (st_enq s ch) ->
  KB ch (apop K_BATCH_CLASS s) true = recycle (st_after (st_enq s ch)) Q_MIN (fun st3 => aret st3).
Proof.
  intros s ch EA QC REC.
  assert (EN : st_enq s ch = enq_new s ch).
  { unfold st_enq. destruct (enq_app s ch) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app s = true) by (apply (proj2 (enq_is_app_spec s ch)); eexists; exact E). congruence. }
  rewrite EN in *. unfold KB. cbn [negb].
  change (set_qloc (a_qloc (apop K_BATCH_CLASS s) ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]])
                   (a_qloc_bytes (apop K_BATCH_CLASS s) + chunk_size ch + Q_BATCH_BYTES) (apop K_BATCH_CLASS s)) with (enq_new s ch).
  unfold afterK. exact (proj1 (after_rec_eq _ QC REC)).
Qed.
End CANSEC1.
