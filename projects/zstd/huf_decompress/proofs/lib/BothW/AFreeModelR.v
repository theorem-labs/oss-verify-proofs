(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (afree_refill_eq, KB_apop_eq)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ARefill_iface AFreeModel AFreeRead.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeModelR () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6lookupC35stdpp4base6deleteI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec8AsanCtrl7enqueueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=recycle_chunkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFreeModelR2KBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec8AsanCtrl8set_qlocC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ARefill_ifaceBcache_alloc_unfoldC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5drainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ARefill_ifaceAcache_refill_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;cache_allocC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K59OSSVerify5KrLib4Spec8AsanCtrl6abatch01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K59OSSVerify5KrLib4Spec8AsanCtrl6aundef02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K59OSSVerify5KrLib4Spec8AsanCtrl6aundef03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C35stdpp4base6LookupC35stdpp4base6DeleteC59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_newC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5BothW9AFreeRead?enq_is_app_specC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_transK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib5BothW=ARefill_iface4apopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9set_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7recycleC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib5BothW;AFreeModelR6afterKC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition afterK (s : astate) : AM astate :=
  if Q_CACHE <? a_qloc_bytes s then drain s (fun s3 => aret s3) else aret s.
(* [comment removed for export] *)
Definition KB (ch : achunk) (s : astate) (ok : bool) : AM astate :=
  if negb ok then aundef_ USpin (afterK s)
  else afterK (set_qloc (a_qloc s ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes s + chunk_size ch + Q_BATCH_BYTES) s).

Lemma afree_refill_eq : forall st p ch,
  (a_live st) !! p = Some ch -> chunk_size ch <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  afree st (Some p) = cache_refill_tree st1 K_BATCH_CLASS (KB ch).
Proof.
  intros st p ch LIVE SZ st1 EA CNT0.
  unfold afree. rewrite LIVE. fold st1.
  replace (chunk_size ch <=? Q_MAX) with true by (symmetry; apply Z.leb_le; exact SZ).
  unfold enqueue.
  assert (NB : forall s, cache_alloc s K_BATCH_CLASS (fun (st0 : astate) (ok : bool) =>
      if negb ok then aundef_ USpin ((fun st2 : astate => if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 : astate => aret st3) else aret st2) st0)
      else (fun st2 : astate => if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 : astate => aret st3) else aret st2)
             (set_qloc (a_qloc st0 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st0 + chunk_size ch + Q_BATCH_BYTES) st0))
    = cache_alloc s K_BATCH_CLASS (KB ch)) by (intros s; reflexivity).
  pose proof EA as EA0. unfold enq_is_app in EA0. change (a_qloc st) with (a_qloc st1) in EA0.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - rewrite NB, cache_alloc_unfold. change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS). rewrite CNT0. reflexivity.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [FULL|NF]; [| cbn in EA0; discriminate].
    rewrite NB, cache_alloc_unfold. change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS). rewrite CNT0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma KB_apop_eq : forall s ch,
  enq_is_app s = false ->
  (Q_CACHE < a_qloc_bytes (st_enq s ch) -> a_qglob_bytes (st_enq s ch) + a_qloc_bytes (st_enq s ch) <= Q_MAX) ->
  KB ch (apop K_BATCH_CLASS s) true = aret (st_after (st_enq s ch)).
Proof.
  intros s ch EA NOREC.
  assert (EN : st_enq s ch = enq_new s ch).
  { unfold st_enq. destruct (enq_app s ch) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app s = true) by (apply (proj2 (enq_is_app_spec s ch)); eexists; exact E). congruence. }
  rewrite EN in *. unfold KB. cbn [negb].
  change (set_qloc (a_qloc (apop K_BATCH_CLASS s) ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]])
                   (a_qloc_bytes (apop K_BATCH_CLASS s) + chunk_size ch + Q_BATCH_BYTES) (apop K_BATCH_CLASS s)) with (enq_new s ch).
  unfold afterK, st_after, drain.
  destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes (enq_new s ch))) as [LT|GE]; [| reflexivity].
  cbn [a_qglob_bytes set_qglob].
  destruct (Z.ltb_spec Q_MAX (a_qglob_bytes (enq_new s ch) + a_qloc_bytes (enq_new s ch))) as [LT2|GE2]; [exfalso; specialize (NOREC LT); lia| reflexivity].
Qed.
End CANSEC1.
