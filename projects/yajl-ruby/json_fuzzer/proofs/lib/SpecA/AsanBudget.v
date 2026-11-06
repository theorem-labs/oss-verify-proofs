(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanFrame AsanWf3 AsanWf4 AsanWf8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section BU.
Variable E : aenv.
Local Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition res_ok (s : astate) : Prop :=
  forall sc, In sc (as_sec s) -> incl (residue_pages (sc_map_beg sc) (sc_map_size sc)) (as_residue s).

Lemma res_ok_init : res_ok (astate0 E).
Proof. intros sc []. Qed.

Lemma res_ok_frame : forall s s', (forall sc, In sc (as_sec s') -> In sc (as_sec s)) -> incl (as_residue s) (as_residue s') ->
  res_ok s -> res_ok s'.
Proof. intros s s' HS HR R sc Hsc x Hx. apply HR. apply (R sc (HS sc Hsc) x Hx). Qed.

Ltac res_same := match goal with H : res_ok ?st |- res_ok _ => eapply res_ok_frame; [| | exact H]; [cbn; auto| cbn; apply incl_refl] end.

Lemma ensure_res : forall c nf, presW res_ok (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; res_same. Qed.
Lemma populate_res : forall c r, presW res_ok (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_res; res_same. Qed.
Lemma gfa_res : forall c n, presW res_ok (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_res; res_same. Qed.
Lemma refill_res : forall c, presW res_ok (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_res; res_same. Qed.
Lemma cache_pop_res : forall c, presW res_ok (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_res; res_same. Qed.
Lemma call_mmap_ordie_res : forall l fl, presW res_ok (call_mmap_ordie E l fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_res : forall c, presW res_ok (store_alloc E c).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try apply call_mmap_ordie_res; res_same. Qed.
Lemma depot_put_res : forall k, presW res_ok (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply call_mmap_ordie_res; try apply store_alloc_res; res_same. Qed.
Lemma sec_alloc_res : forall nd, presW res_ok (sec_alloc E nd).
Proof.
  intros; unfold sec_alloc. pw; try apply call_mmap_anon_W; try apply call_mmap_fixed_W; try res_same.
  match goal with H : res_ok ?st |- res_ok _ => rename H into R end.
  intros sc Hsc pg Hpg. cbn in Hsc |- *. apply in_app_iff in Hsc as [Hsc|[<-|[]]].
  - apply in_app_iff. left. exact (R sc Hsc pg Hpg).
  - apply in_app_iff. right. exact Hpg.
Qed.
Lemma amalloc_core_res : forall key n, presW res_ok (amalloc_core E key n).
Proof.
  intros; unfold amalloc_core. pw; try apply cache_pop_res; try apply sec_alloc_res; try apply depot_put_res; try pzW; res_same.
Qed.
Lemma return_res : forall c l, presW res_ok (return_to_allocator E c l).
Proof. intros; unfold return_to_allocator. pw; try apply ensure_res; res_same. Qed.
Lemma local_dealloc_res : forall c p, presW res_ok (local_dealloc E c p).
Proof. intros; unfold local_dealloc, init_cache. pw; try apply return_res; res_same. Qed.
Lemma swap_remove_sub : forall {A} (l : list A) i h x, nth_error l i = Some h ->
  In x (removelast (list_set l i (List.last l h))) -> In x l.
Proof. intros A l i h x NTH Hx. eapply Permutation_in; [apply (swap_remove_perm l i h NTH)| right; exact Hx]. Qed.
Lemma large_dealloc_res : forall p, presW res_ok (large_dealloc p).
Proof.
  intros p. apply hoareW_pre. intros s0 R0. unfold large_dealloc. apply hoareW_get_bind. intros s ->.
  destruct (list_find_index _ (as_sec s0) 0) as [i|]; [| apply hoareW_undef].
  destruct (nth_error (as_sec s0) i) as [h|] eqn:NTH; [| apply hoareW_undef].
  apply hoareW_upd_bind. apply hoareW_pre. intros s1 (s & -> & ->). set (s1 := upd_glob _ _ _).
  assert (R1 : res_ok s1).
  { eapply res_ok_frame; [| | exact R0]; [| cbn; apply incl_refl]. intros sc Hsc. cbn in Hsc. eapply swap_remove_sub; [exact NTH| exact Hsc]. }
  eapply hoareW_bind; [apply poison_zero_eq|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_pre. intros s2 (s & -> & ->).
  eapply hoareW_conseq; [apply call_munmap_eq| intros s H; exact H|]. intros s [] ->.
  eapply res_ok_frame; [| | exact R1]; [cbn; auto| cbn; apply incl_refl].
Qed.
Lemma qcb_recycle_res : forall m, presW res_ok (qcb_recycle E m).
Proof. intros; unfold qcb_recycle. pw; try apply local_dealloc_res; try apply large_dealloc_res; res_same. Qed.
Lemma recycle_items_res : forall l, presW res_ok (recycle_items E l).
Proof. intros l; induction l; cbn; pw; [apply qcb_recycle_res| assumption]. Qed.
Lemma do_recycle_res : forall bs, presW res_ok (do_recycle E bs).
Proof. intros bs; induction bs; cbn; pw; try apply recycle_items_res; try apply local_dealloc_res; try assumption. Qed.
Lemma recycle_res : presW res_ok (recycle E).
Proof. unfold recycle. pw; try apply do_recycle_res; res_same. Qed.
Lemma drain_res : presW res_ok (drain_if_needed E).
Proof. unfold drain_if_needed. pw; try apply recycle_res; res_same. Qed.
Lemma enqueue_res : forall cb n, presW res_ok (enqueue E cb n).
Proof. intros; unfold enqueue, batch_alloc. pw; try apply cache_pop_res; res_same. Qed.
Lemma afree_core_res : forall key p, presW res_ok (afree_core E key p).
Proof. intros; unfold afree_core. pw; try apply depot_put_res; try apply enqueue_res; try apply drain_res; res_same. Qed.

Theorem amalloc_res : forall key n, presW res_ok (amalloc E key n).
Proof. intros; unfold amalloc. apply amalloc_core_res. Qed.
Theorem afree_res : forall key p, presW res_ok (afree E key p).
Proof. intros; unfold afree, ia_init. pw; try apply afree_core_res; res_same. Qed.
Theorem arealloc_res : forall key p n, presW res_ok (arealloc E key p n).
Proof. intros; unfold arealloc, ia_init. pw; try apply amalloc_core_res; try apply afree_core_res; res_same. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition QS (T G : list batch) (s : astate) : Prop := as_tq s = T /\ as_gq s = G.
Ltac qs_same := match goal with H : QS ?T ?G ?st |- QS ?T ?G _ => destruct H as [?A ?B]; split; cbn; assumption end.

Lemma ensure_qs : forall T G c nf, presW (QS T G) (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; qs_same. Qed.
Lemma populate_qs : forall T G c r, presW (QS T G) (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_qs; qs_same. Qed.
Lemma gfa_qs : forall T G c n, presW (QS T G) (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_qs; qs_same. Qed.
Lemma refill_qs : forall T G c, presW (QS T G) (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_qs; qs_same. Qed.
Lemma cache_pop_qs : forall T G c, presW (QS T G) (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_qs; qs_same. Qed.
Lemma store_alloc_qs : forall T G c, presW (QS T G) (store_alloc E c).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try apply call_mmap_anon_W; try (unfold call_mmap_ordie; pw); qs_same. Qed.
Lemma depot_put_qs : forall T G k, presW (QS T G) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply store_alloc_qs; try (unfold call_mmap_ordie; pw); qs_same. Qed.
Lemma sec_alloc_qs : forall T G nd, presW (QS T G) (sec_alloc E nd).
Proof. intros; unfold sec_alloc. pw; try apply call_mmap_anon_W; try apply call_mmap_fixed_W; qs_same. Qed.
Lemma amalloc_core_qs : forall T G key n, presW (QS T G) (amalloc_core E key n).
Proof. intros; unfold amalloc_core. pw; try apply cache_pop_qs; try apply sec_alloc_qs; try apply depot_put_qs; try pzW; qs_same. Qed.
Lemma return_qs : forall T G c l, presW (QS T G) (return_to_allocator E c l).
Proof. intros; unfold return_to_allocator. pw; try apply ensure_qs; qs_same. Qed.
Lemma local_dealloc_qs : forall T G c p, presW (QS T G) (local_dealloc E c p).
Proof. intros; unfold local_dealloc, init_cache. pw; try apply return_qs; qs_same. Qed.
Lemma large_dealloc_qs : forall T G p, presW (QS T G) (large_dealloc p).
Proof. intros; unfold large_dealloc. pw; try pzW; try apply call_munmap_W; qs_same. Qed.
Lemma qcb_recycle_qs : forall T G m, presW (QS T G) (qcb_recycle E m).
Proof. intros; unfold qcb_recycle. pw; try apply local_dealloc_qs; try apply large_dealloc_qs; qs_same. Qed.
Lemma recycle_items_qs : forall T G l, presW (QS T G) (recycle_items E l).
Proof. intros T G l; induction l; cbn; pw; [apply qcb_recycle_qs| assumption]. Qed.
Lemma do_recycle_qs : forall T G bs, presW (QS T G) (do_recycle E bs).
Proof. intros T G bs; induction bs; cbn; pw; try apply recycle_items_qs; try apply local_dealloc_qs; try assumption. Qed.

Lemma pop_prefix_bytes : forall l mn, 0 <= mn -> qbytes (snd (pop_prefix l (qbytes l) mn)) <= mn.
Proof.
  intros l mn Hmn. induction l as [|b rest IH]; [unfold qbytes; cbn; lia|].
  change (qbytes (b :: rest)) with (b_size b + qbytes rest). cbn [pop_prefix].
  destruct (mn <? b_size b + qbytes rest) eqn:LT.
  - replace (b_size b + qbytes rest - b_size b) with (qbytes rest) by lia.
    destruct (pop_prefix rest (qbytes rest) mn) as [pp kk]. cbn in *. exact IH.
  - cbn [snd]. apply Z.ltb_ge in LT. change (qbytes (b :: rest)) with (b_size b + qbytes rest). lia.
Qed.

(* [comment removed for export] *)
Lemma drain_AQ : forall s0, gq_bytes s0 <= kQuarantineMax -> hoareW (fun s => s = s0) (drain_if_needed E) (fun s' _ => AQbound s').
Proof.
  intros s0 GQ. unfold drain_if_needed. apply hoareW_get_bind. intros s ->.
  destruct (kThreadQuarantineMax <? tq_bytes s0) eqn:TQ.
  - apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). apply hoareW_get_bind. intros s ->.
    match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:GQ1 end.
    + unfold recycle. apply hoareW_get_bind. intros s ->.
      eapply hoareW_bind; [apply hoareW_check with (Q := fun s' _ => s' = upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq s0) s0)); auto|]. intros [].
      apply hoareW_pre. intros s ->.
      match goal with |- hoareW _ (let '(_, _) := ?x in _) _ => destruct x as [gq1 empties] eqn:MG end.
      destruct (pop_prefix gq1 (qbytes gq1) kQuarantineMin) as [popped kept] eqn:PP.
      apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->).
      eapply hoareW_conseq; [apply (presW_from (fun a b => QS (as_tq a) (as_gq a) b)); [intros a; split; reflexivity| apply do_recycle_qs]| intros ? ->; reflexivity|].
      cbn beta. intros s [] [HT HG]. unfold AQbound, tq_bytes, gq_bytes. rewrite HT, HG. cbn.
      pose proof (pop_prefix_bytes gq1 kQuarantineMin ltac:(unfold kQuarantineMin; lia)) as PB. rewrite PP in PB. cbn in PB.
      unfold kThreadQuarantineMax, kQuarantineMax, kQuarantineMin in *. lia.
    + apply hoareW_ret. intros s ->. apply Z.ltb_ge in GQ1. unfold AQbound, tq_bytes. cbn. unfold kThreadQuarantineMax. split; [lia| exact GQ1].
  - apply hoareW_ret. intros s ->. apply Z.ltb_ge in TQ. split; [exact TQ| exact GQ].
Qed.

Lemma afree_core_AQ : forall s0 key p, gq_bytes s0 <= kQuarantineMax ->
  hoareW (fun s => s = s0) (afree_core E key p) (fun s' _ => AQbound s').
Proof.
  intros s0 key p GQ0. unfold afree_core. apply hoareW_get_bind. intros s ->.
  destruct (as_chunks s0 !! (p - kChunkHeaderSize)) as [meta|]; [| apply hoareW_undef].
  destruct (cm_state meta); [| apply hoareW_undef]. destruct (negb (cm_user_beg meta =? p)); [apply hoareW_undef|].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s1 := upd_ts _ s0).
  eapply hoareW_bind; [apply (presW_from (fun a b => QS (as_tq a) (as_gq a) b) _ s1); [intros a; split; reflexivity| apply depot_put_qs]|].
  intros fid. apply hoareW_pre. intros s2 [T2 G2].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->). set (s3 := upd_chunks _ s2).
  eapply hoareW_bind.
  { apply hoareW_pre. intros s ->. unfold enqueue, batch_alloc. apply hoareW_get_bind. intros s ->.
    match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b end.
    - eapply hoareW_bind; [eapply hoareW_bind; [apply (presW_from (fun a b => QS (as_tq a) (as_gq a) b) _ s3); [intros a; split; reflexivity| apply cache_pop_qs]|]|].
      + intros [b|]; [| apply hoareW_spin]. destruct (b =? 0); [apply hoareW_spin| apply hoareW_ret; intros s H; exact H].
      + intros b. apply hoareW_upd with (Q := fun s' _ => as_gq s' = as_gq s0). intros s [_ G]. cbn. rewrite G. exact G2.
    - apply hoareW_upd with (Q := fun s' _ => as_gq s' = as_gq s0). intros s ->. cbn. exact G2. }
  intros []. apply hoareW_pre. intros s4 G4. apply drain_AQ. unfold gq_bytes in *. rewrite G4. exact GQ0.
Qed.

Theorem amalloc_AQ : forall s0 key n, AQbound s0 -> hoareW (fun s => s = s0) (amalloc E key n) (fun s' _ => AQbound s').
Proof.
  intros s0 key n [T G]. unfold amalloc.
  eapply hoareW_conseq; [apply (presW_from (fun a b => QS (as_tq a) (as_gq a) b) _ s0); [intros a; split; reflexivity| apply amalloc_core_qs]| auto|].
  intros s r [HT HG]. unfold AQbound, tq_bytes, gq_bytes in *. rewrite HT, HG. auto.
Qed.

Theorem afree_AQ : forall s0 key p, AQbound s0 -> hoareW (fun s => s = s0) (afree E key p) (fun s' _ => AQbound s').
Proof.
  intros s0 key p [T G]. unfold afree, ia_init. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  destruct (p =? 0); [apply hoareW_ret; intros s ->; split; [exact T| exact G]|].
  apply afree_core_AQ. exact G.
Qed.

Theorem arealloc_AQ : forall s0 key p n, AQbound s0 -> hoareW (fun s => s = s0) (arealloc E key p n) (fun s' _ => AQbound s').
Proof.
  intros s0 key p n [T G]. unfold arealloc, ia_init. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  destruct (p =? 0).
  { eapply hoareW_conseq; [apply (presW_from (fun a b => QS (as_tq a) (as_gq a) b)); [intros a; split; reflexivity| apply amalloc_core_qs]| intros ? ->; reflexivity|].
    intros s r [HT HG]. unfold AQbound, tq_bytes, gq_bytes in *. rewrite HT, HG. auto. }
  destruct (n =? 0).
  { eapply hoareW_bind; [apply afree_core_AQ; exact G|]. intros []. apply hoareW_ret. intros s H; exact H. }
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->).
  eapply hoareW_bind; [apply (presW_from (fun a b => QS (as_tq a) (as_gq a) b) _ (upd_ts (ts_on_realloc n) (upd_ia_inited true s0))); [intros a; split; reflexivity| apply amalloc_core_qs]|].
  intros [q|]; [| apply hoareW_ret; intros s [HT HG]; unfold AQbound, tq_bytes, gq_bytes in *; rewrite HT, HG; auto].
  apply hoareW_get_bind. intros s1 [HT HG].
  destruct (as_chunks s1 !! (p - kChunkHeaderSize)) as [meta|]; [| apply hoareW_undef].
  destruct (cm_state meta); [| apply hoareW_undef]. destruct (cm_user_beg meta =? p); [| apply hoareW_undef].
  eapply hoareW_bind; [apply afree_core_AQ; unfold gq_bytes in *; rewrite HG; exact G|]. intros []. apply hoareW_ret. intros s H; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NP (K : Z) (s : astate) : Prop := as_nprim_ever s = K.
Ltac np_same := match goal with H : NP ?K ?st |- NP ?K _ => unfold NP in *; cbn; exact H end.

Lemma ensure_np : forall K c nf, presW (NP K) (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; np_same. Qed.
Lemma populate_np : forall K c r, presW (NP K) (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_np; np_same. Qed.
Lemma gfa_np : forall K c n, presW (NP K) (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_np; np_same. Qed.
Lemma refill_np : forall K c, presW (NP K) (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_np; np_same. Qed.
Lemma cache_pop_np : forall K c, presW (NP K) (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_np; np_same. Qed.
Lemma store_alloc_np : forall K c, presW (NP K) (store_alloc E c).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try (unfold call_mmap_ordie; pw); np_same. Qed.
Lemma depot_put_np : forall K k, presW (NP K) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply store_alloc_np; try (unfold call_mmap_ordie; pw); np_same. Qed.
Lemma sec_alloc_np : forall K nd, presW (NP K) (sec_alloc E nd).
Proof. intros; unfold sec_alloc. pw; try apply call_mmap_anon_W; try apply call_mmap_fixed_W; np_same. Qed.
Lemma return_np : forall K c l, presW (NP K) (return_to_allocator E c l).
Proof. intros; unfold return_to_allocator. pw; try apply ensure_np; np_same. Qed.
Lemma local_dealloc_np : forall K c p, presW (NP K) (local_dealloc E c p).
Proof. intros; unfold local_dealloc, init_cache. pw; try apply return_np; np_same. Qed.
Lemma large_dealloc_np : forall K p, presW (NP K) (large_dealloc p).
Proof. intros; unfold large_dealloc. pw; try pzW; try apply call_munmap_W; np_same. Qed.
Lemma qcb_recycle_np : forall K m, presW (NP K) (qcb_recycle E m).
Proof. intros; unfold qcb_recycle. pw; try apply local_dealloc_np; try apply large_dealloc_np; np_same. Qed.
Lemma recycle_items_np : forall K l, presW (NP K) (recycle_items E l).
Proof. intros K l; induction l; cbn; pw; [apply qcb_recycle_np| assumption]. Qed.
Lemma do_recycle_np : forall K bs, presW (NP K) (do_recycle E bs).
Proof. intros K bs; induction bs; cbn; pw; try apply recycle_items_np; try apply local_dealloc_np; try assumption. Qed.
Lemma recycle_np : forall K, presW (NP K) (recycle E).
Proof. intros; unfold recycle. pw; try apply do_recycle_np; np_same. Qed.
Lemma drain_np : forall K, presW (NP K) (drain_if_needed E).
Proof. intros; unfold drain_if_needed. pw; try apply recycle_np; np_same. Qed.
Lemma enqueue_np : forall K cb n, presW (NP K) (enqueue E cb n).
Proof. intros; unfold enqueue, batch_alloc. pw; try apply cache_pop_np; np_same. Qed.
Lemma afree_core_np : forall K key p, presW (NP K) (afree_core E key p).
Proof. intros; unfold afree_core. pw; try apply depot_put_np; try apply enqueue_np; try apply drain_np; np_same. Qed.

Definition bprim (n : Z) : Z := if from_primary n then 1 else 0.

Lemma amalloc_core_np : forall s0 key n,
  hoareW (fun s => s = s0) (amalloc_core E key n) (fun s' _ => NP (as_nprim_ever s0 + bprim n) s').
Proof.
  intros; unfold amalloc_core.
  eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s0); auto|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind.
  eapply hoareW_conseq with (P := NP (as_nprim_ever s0 + bprim n));
    [| intros s1 (s & -> & ->); unfold NP, bprim; cbn; destruct (from_primary n); lia | intros ? ? H; exact H].
  change (hoareW ?P ?m (fun s' _ => ?P s')) with (presW P m).
  pw; try apply cache_pop_np; try apply sec_alloc_np; try apply depot_put_np; try pzW; np_same.
Qed.

Theorem amalloc_np : forall s0 key n,
  hoareW (fun s => s = s0) (amalloc E key n) (fun s' _ => as_nprim_ever s' = as_nprim_ever s0 + bprim n).
Proof. intros; unfold amalloc. apply amalloc_core_np. Qed.

Theorem afree_np : forall s0 key p,
  hoareW (fun s => s = s0) (afree E key p) (fun s' _ => as_nprim_ever s' = as_nprim_ever s0).
Proof.
  intros. enough (H : hoareW (fun s => s = s0) (afree E key p) (fun s' _ => NP (as_nprim_ever s0) s')) by exact H.
  unfold afree, ia_init. apply hoareW_upd_bind.
  eapply hoareW_conseq with (P := NP (as_nprim_ever s0)) (Q := fun s' _ => NP (as_nprim_ever s0) s'); [| intros s1 (s & -> & ->); reflexivity| auto].
  change (hoareW ?P ?m (fun s' _ => ?P s')) with (presW P m). pw; try apply afree_core_np; np_same.
Qed.

Theorem arealloc_np : forall s0 key p n,
  hoareW (fun s => s = s0) (arealloc E key p n)
    (fun s' _ => as_nprim_ever s' = as_nprim_ever s0 + (if (negb (p =? 0)) && (n =? 0) then 0 else bprim n)).
Proof.
  intros. set (K := as_nprim_ever s0 + (if (negb (p =? 0)) && (n =? 0) then 0 else bprim n)).
  enough (H : hoareW (fun s => s = s0) (arealloc E key p n) (fun s' _ => NP K s')) by exact H. subst K.
  unfold arealloc, ia_init. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  destruct (p =? 0); cbn [negb andb].
  { eapply hoareW_conseq; [apply amalloc_core_np| intros ? ->; reflexivity| intros ? ? H; exact H]. }
  destruct (n =? 0).
  { eapply hoareW_conseq with (P := NP (as_nprim_ever s0 + 0)) (Q := fun s' _ => NP (as_nprim_ever s0 + 0) s'); [| intros ? ->; unfold NP; cbn; lia| auto].
    change (hoareW ?P ?m (fun s' _ => ?P s')) with (presW P m). pw; try apply afree_core_np; np_same. }
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->).
  eapply hoareW_bind; [apply amalloc_core_np|]. intros r.
  change (as_nprim_ever s0) with (as_nprim_ever (upd_ts (ts_on_realloc n) (upd_ia_inited true s0))).
  set (K := as_nprim_ever _ + bprim n).
  change (hoareW ?P ?m (fun s' _ => NP K s')) with (presW (NP K) m).
  pw; try apply afree_core_np; np_same.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shadow_page_mono : forall a b, a <= b -> shadow_page a <= shadow_page b.
Proof.
  intros a b LE. unfold shadow_page, round_down, mem_to_shadow, kPageSize.
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

Lemma shadow_page_mod : forall a, shadow_page a mod kPageSize = 0.
Proof. intros a. unfold shadow_page, round_down. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma shadow_page_in_hull : forall mb msz a, mb <= a < mb + msz -> In (shadow_page a) (hull_pages mb msz).
Proof.
  intros mb msz a Ha. unfold hull_pages.
  pose proof (shadow_page_mono mb a ltac:(lia)) as L1. pose proof (shadow_page_mono a (mb + msz - 1) ltac:(lia)) as L2.
  pose proof (shadow_page_mod a) as Ma. pose proof (shadow_page_mod mb) as Mb. pose proof (shadow_page_mod (mb + msz - 1)) as Me.
  unfold kPageSize in *.
  apply Z.mod_divide in Ma; [|lia]. apply Z.mod_divide in Mb; [|lia]. apply Z.mod_divide in Me; [|lia].
  destruct Ma as [qa Ha']. destruct Mb as [qb Hb']. destruct Me as [qe He'].
  assert (QA0 : 0 <= qa - qb) by nia. assert (QA1 : qa - qb <= qe - qb) by nia.
  assert (DQ : (shadow_page (mb + msz - 1) - shadow_page mb) / 4096 = qe - qb) by (rewrite He', Hb', <- Z.mul_sub_distr_r, Z.div_mul; lia).
  apply in_map_iff. exists (Z.to_nat (qa - qb)). split.
  - rewrite Z2Nat.id by exact QA0. lia.
  - apply in_seq. split; [lia|]. rewrite DQ. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_page_big : forall mb msz a, mb mod kPageSize = 0 -> 0 < msz -> mb <= a < mb + msz ->
  let '(pb, plen) := remap_range mb msz in
  (pb <= shadow_page a /\ shadow_page a + kPageSize <= pb + plen)
  \/ shadow_page a = shadow_page mb \/ shadow_page a = shadow_page (mb + msz - 1).
Proof.
  intros mb msz a AL POS Ha. unfold remap_range. cbn zeta.
  pose proof (shadow_page_mono mb a ltac:(lia)) as L1. pose proof (shadow_page_mono a (mb + msz - 1) ltac:(lia)) as L2.
  pose proof (shadow_page_mod a) as Ma. pose proof (shadow_page_mod mb) as Mb. pose proof (shadow_page_mod (mb + msz - 1)) as Me.
  unfold kPageSize in *.
  apply Z.mod_divide in Ma; [|lia]. apply Z.mod_divide in Mb; [|lia]. apply Z.mod_divide in Me; [|lia].
  destruct Ma as [qa Ha']. destruct Mb as [qb Hb']. destruct Me as [qe He'].
  rewrite Ha', Hb' in L1. rewrite Ha', He' in L2.
  destruct (Z.eq_dec qa qb) as [EQ|NE1]; [right; left; rewrite Ha', Hb', EQ; reflexivity|].
  destruct (Z.eq_dec qa qe) as [EQ|NE2]; [right; right; rewrite Ha', He', EQ; reflexivity|].
  left. rewrite Ha'.
  assert (QA1 : qb + 1 <= qa) by lia. assert (QA2 : qa + 1 <= qe) by lia.
  (* [comment removed for export] *)
  unfold shadow_page, round_down, mem_to_shadow, kPageSize in Hb', He'. unfold round_up, mem_to_shadow, round_down, kPageSize.
  set (sb := kShadowBase + mb / 8) in *.
  assert (M1 : sb / 4096 * 4096 <= sb < sb / 4096 * 4096 + 4096).
  { pose proof (Z.div_mod sb 4096 ltac:(lia)). pose proof (Z.mod_pos_bound sb 4096 ltac:(lia)). lia. }
  assert (RU : (sb + 4096 - 1) / 4096 * 4096 <= sb / 4096 * 4096 + 4096).
  { pose proof (Z.div_mod (sb + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sb + 4096 - 1) 4096 ltac:(lia)).
    assert ((sb + 4096 - 1) / 4096 < sb / 4096 + 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (SE : kShadowBase + (mb + msz - 1) / 8 <= sb + msz / 8).
  { subst sb. apply Z.mod_divide in AL; [|lia]. destruct AL as [k Hk]. rewrite Hk.
    replace (k * 4096) with ((k * 512) * 8) by lia. rewrite Z.div_mul by lia.
    replace (k * 512 * 8 + msz - 1) with ((msz - 1) + (k * 512) * 8) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_le_mono (msz - 1) msz 8 ltac:(lia) ltac:(lia)). lia. }
  assert (PE : (kShadowBase + (mb + msz - 1) / 8) / 4096 * 4096 <= (sb + msz / 8) / 4096 * 4096).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  rewrite He' in PE. rewrite Hb' in RU. lia.
Qed.

(* [comment removed for export] *)
Lemma prim_block_in_space : forall P D s cb cm c, AWf E P D s -> as_chunks s !! cb = Some cm -> cm_prim cm = Some c ->
  SB + kRegionSize <= cm_alloc_beg cm /\ cm_alloc_beg cm + class_size c <= SB + kSpaceSize.
Proof.
  intros P D s cb cm c WF Hcm PC. pose proof WF as X. destruct X as (_ & WR & _ & [K1 _] & _).
  destruct (K1 _ _ Hcm) as (_ & B & _ & D0 & _). rewrite PC in D0. destruct D0 as (D1 & D2 & CV & _).
  assert (Hc : 1 <= c <= kLargestClassID).
  { subst c. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
  exact (carved_in_space E s c _ Hc WR CV).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dphi (s : astate) : Z := as_frames s - 32 * (as_frames s / kStoreBlockFrames).

Definition depot_inv (s : astate) : Prop :=
  kDepotNodesPerBlock * zlen (as_node_blocks s) <= depot_n_ids E s
  /\ kStoreBlockFrames * zlen (as_store_blocks s) <= as_frames s
  /\ as_frames s <= ae_frames0 E + 64 * as_ndepot_ins s
  /\ 0 <= as_ndepot_ins s
  /\ depot_n_ids E s < kDepotNodesPerBlock * (zlen (as_node_blocks s) + 1)    (* [comment removed for export] *)
  /\ dphi s <= ae_frames0 E + 32 * as_ndepot_ins s                             (* [comment removed for export] *)
  /\ as_frames s <= kStoreBlockFrames * (zlen (as_store_blocks s) + 1).         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_inv6 (s : astate) : Prop :=
  kDepotNodesPerBlock * zlen (as_node_blocks s) <= depot_n_ids E s
  /\ kStoreBlockFrames * zlen (as_store_blocks s) <= as_frames s
  /\ as_frames s <= ae_frames0 E + 64 * as_ndepot_ins s
  /\ 0 <= as_ndepot_ins s
  /\ depot_n_ids E s < kDepotNodesPerBlock * (zlen (as_node_blocks s) + 1)
  /\ dphi s <= ae_frames0 E + 32 * as_ndepot_ins s.
(* [comment removed for export] *)
Definition SCI (s : astate) : Prop := 0 <= as_frames s /\ as_frames s <= kStoreBlockFrames * (zlen (as_store_blocks s) + 1).
Lemma depot_inv_split : forall s, depot_inv s <-> (depot_inv6 s /\ SCI s).
Proof.
  intros s. unfold depot_inv, depot_inv6, SCI. split.
  - intros (I1 & I2 & I3 & I4 & I5 & I6 & I7). unfold kStoreBlockFrames, zlen in *. repeat split; try assumption. lia.
  - intros ((I1 & I2 & I3 & I4 & I5 & I6) & _ & I7). repeat split; assumption.
Qed.

Lemma depot_inv_init : 0 <= ae_frames0 E <= 4096 -> zlen (ae_keys0 E) < kDepotNodesPerBlock -> depot_inv (astate0 E).
Proof.
  intros H H1. unfold depot_inv, dphi, depot_n_ids, zlen in *. cbn. unfold kDepotNodesPerBlock, kStoreBlockFrames in *.
  pose proof (Z.div_pos (ae_frames0 E) (2^20) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma depot_frames_bound : forall s, depot_inv s -> ae_frames0 E <= 4096 -> as_ndepot_ins s <= 120000000 ->
  0 <= as_frames s /\ as_frames s + kStoreBlockFrames <= 2^32 /\ as_frames s / kStoreBlockFrames + 1 < 0x1000 (* [comment removed for export] *).
Proof.
  intros s (I1 & I2 & I3 & I4 & I5 & I6 & I7) F0 ND. unfold dphi, kStoreBlockFrames in *.
  assert (F : 0 <= as_frames s) by (unfold zlen in I2; lia).
  pose proof (Z.mul_div_le (as_frames s) (2^20) ltac:(lia)) as X.
  pose proof (Z.div_pos (as_frames s) (2^20) F ltac:(lia)) as Y.
  assert (as_frames s / 2^20 < 4000) by lia.
  split; [exact F| split; [lia|]].
  lia.
Qed.

Ltac di_same := match goal with H : depot_inv ?st |- depot_inv _ => unfold depot_inv, dphi, depot_n_ids in *; cbn; exact H end.

Lemma ensure_di : forall c nf, presW depot_inv (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; di_same. Qed.
Lemma populate_di : forall c r, presW depot_inv (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_di; di_same. Qed.
Lemma gfa_di : forall c n, presW depot_inv (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_di; di_same. Qed.
Lemma refill_di : forall c, presW depot_inv (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_di; di_same. Qed.
Lemma cache_pop_di : forall c, presW depot_inv (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_di; di_same. Qed.
Lemma sec_alloc_di : forall nd, presW depot_inv (sec_alloc E nd).
Proof. intros; unfold sec_alloc. pw; try apply call_mmap_anon_W; try apply call_mmap_fixed_W; di_same. Qed.
Lemma return_di : forall c l, presW depot_inv (return_to_allocator E c l).
Proof. intros; unfold return_to_allocator. pw; try apply ensure_di; di_same. Qed.
Lemma local_dealloc_di : forall c p, presW depot_inv (local_dealloc E c p).
Proof. intros; unfold local_dealloc, init_cache. pw; try apply return_di; di_same. Qed.
Lemma large_dealloc_di : forall p, presW depot_inv (large_dealloc p).
Proof. intros; unfold large_dealloc. pw; try pzW; try apply call_munmap_W; di_same. Qed.
Lemma qcb_recycle_di : forall m, presW depot_inv (qcb_recycle E m).
Proof. intros; unfold qcb_recycle. pw; try apply local_dealloc_di; try apply large_dealloc_di; di_same. Qed.
Lemma recycle_items_di : forall l, presW depot_inv (recycle_items E l).
Proof. intros l; induction l; cbn; pw; [apply qcb_recycle_di| assumption]. Qed.
Lemma do_recycle_di : forall bs, presW depot_inv (do_recycle E bs).
Proof. intros bs; induction bs; cbn; pw; try apply recycle_items_di; try apply local_dealloc_di; try assumption. Qed.
Lemma recycle_di : presW depot_inv (recycle E).
Proof. unfold recycle. pw; try apply do_recycle_di; di_same. Qed.
Lemma drain_di : presW depot_inv (drain_if_needed E).
Proof. unfold drain_if_needed. pw; try apply recycle_di; di_same. Qed.
Lemma enqueue_di : forall cb n, presW depot_inv (enqueue E cb n).
Proof. intros; unfold enqueue, batch_alloc. pw; try apply cache_pop_di; di_same. Qed.

(* [comment removed for export] *)
Lemma call_mmap_ordie_eq : forall s0 l fl, hoareW (fun s => s = s0) (call_mmap_ordie E l fl) (fun s _ => s = s0).
Proof. intros. apply (call_mmap_ordie_W E (fun s => s = s0)). Qed.

(* [comment removed for export] *)
Lemma dphi_bump : forall f c, 0 <= f -> 0 <= c ->
  (f + c) - 32 * ((f + c) / kStoreBlockFrames) <= f - 32 * (f / kStoreBlockFrames) + c.
Proof.
  intros f c Hf Hc. unfold kStoreBlockFrames.
  pose proof (Z.div_le_mono f (f + c) (2^20) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma dphi_straddle : forall f c, 0 <= f -> 1 <= c -> (f / kStoreBlockFrames =? (f + c - 1) / kStoreBlockFrames) = false ->
  (f + c) - 32 * ((f + c) / kStoreBlockFrames) <= f - 32 * (f / kStoreBlockFrames) + c - 32.
Proof.
  intros f c Hf Hc E0. apply Z.eqb_neq in E0. unfold kStoreBlockFrames in *.
  pose proof (Z.div_le_mono f (f + c - 1) (2^20) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (f + c - 1) (f + c) (2^20) ltac:(lia) ltac:(lia)). lia.
Qed.

Definition dstate (s0 : astate) (df : Z) (dnb dsb dp : Z) (s : astate) : Prop :=
  depot_n_ids E s = depot_n_ids E s0 /\ as_frames s = as_frames s0 + df
  /\ zlen (as_node_blocks s) = zlen (as_node_blocks s0) + dnb /\ zlen (as_store_blocks s) <= zlen (as_store_blocks s0) + dsb
  /\ kStoreBlockFrames * zlen (as_store_blocks s) <= as_frames s
  /\ as_ndepot_ins s = as_ndepot_ins s0 + 1
  /\ dphi s <= dphi s0 + dp.

Lemma store_alloc_once_d : forall s1 s0 df dnb dsb dp count, 1 <= count <= 32 -> dstate s0 df dnb dsb dp s1 ->
  kStoreBlockFrames * zlen (as_store_blocks s1) <= as_frames s1 ->
  hoareW (fun s => s = s1) (store_alloc_once E count)
    (fun s' r => dstate s0 (df + count) dnb (dsb + 1) (dp + match r with Some _ => count | None => count - 32 end) s').
Proof.
  intros s1 s0 df dnb dsb dp count Hc (D1 & D2 & D3 & D4 & D5 & D6 & D7) SB. unfold store_alloc_once.
  assert (F1 : 0 <= as_frames s1) by (unfold zlen in SB; unfold kStoreBlockFrames in SB; lia).
  pose proof (dphi_bump (as_frames s1) count F1 ltac:(lia)) as PB.
  apply hoareW_get_bind. intros s ->. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:FIT end.
  - apply hoareW_get_bind. intros s ->.
    eapply hoareW_bind with (Q := fun s' _ => dstate s0 (df + count) dnb (dsb + 1) (dp + count) s').
    + match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:NEW end.
      * eapply hoareW_bind; [apply call_mmap_ordie_eq|]. intros r. apply hoareW_pre. intros s ->. apply hoareW_upd. intros s ->.
        apply andb_prop in NEW as [N1 N2]. apply Z.ltb_lt in N1. apply Z.ltb_lt in N2. apply Z.eqb_eq in FIT.
        unfold dstate, dphi, depot_n_ids, zlen in *; cbn in *. rewrite length_app; cbn. rewrite Nat2Z.inj_add. cbn.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| split; [lia| clear -PB D7; lia]].
        unfold kStoreBlockFrames in *.
        assert (X : 2^20 * ((as_frames s1) / 2^20) <= as_frames s1) by (apply Z.mul_div_le; lia). clear -X N1 N2 Hc. nia.
      * apply hoareW_ret. intros s ->. unfold dstate, dphi, depot_n_ids, zlen in *; cbn in *. repeat split; first [lia| clear -PB D7; lia].
    + intros []. apply hoareW_ret. auto.
  - pose proof (dphi_straddle (as_frames s1) count F1 ltac:(lia) FIT) as PS.
    apply hoareW_upd_bind. apply hoareW_ret. intros s (sy & -> & ->). unfold dstate, dphi, depot_n_ids, zlen in *; cbn in *.
    repeat split; first [lia| clear -PS D7; lia].
Qed.

Lemma depot_put_di6 : forall s0 key, zlen key + 1 <= 32 -> depot_inv6 s0 ->
  hoareW (fun s => s = s0) (depot_put E key) (fun s' _ => depot_inv6 s').
Proof.
  intros s0 key KL (I1 & I2 & I3 & I4 & I5 & I6). unfold depot_put. apply hoareW_get_bind. intros s ->.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s1 := upd_ndepot _ s0).
  destruct (depot_lookup E s0 key).
  { apply hoareW_ret. intros s ->. unfold depot_inv6, dphi, depot_n_ids in *; cbn. repeat split; lia. }
  eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s1); auto|]. intros []. apply hoareW_pre. intros s ->.
  destruct ((depot_n_ids E s0 + 1) mod kDepotNodesPerBlock =? 0) eqn:NBC.
  all: eapply hoareW_bind with (Q := fun s2 _ => dstate s0 0 (if (depot_n_ids E s0 + 1) mod kDepotNodesPerBlock =? 0 then 1 else 0) 0 0 s2); rewrite ?NBC.
  1:{ eapply hoareW_bind; [apply call_mmap_ordie_eq|]. intros r. apply hoareW_pre. intros s ->. apply hoareW_upd. intros s ->.
      unfold dstate, depot_n_ids, zlen in *; cbn in *. rewrite length_app, Nat2Z.inj_add. cbn. unfold dphi; cbn. repeat split; lia. }
  2:{ apply hoareW_ret. intros s ->. unfold dstate, depot_n_ids, zlen in *; cbn in *. unfold dphi; cbn. repeat split; lia. }
  all: intros []; apply hoareW_pre; intros s2 DS.
  all: eapply hoareW_bind with (Q := fun s3 _ => exists df dsb dp, 0 <= df <= 64 /\ dp <= 32 /\ dstate s0 df (if (depot_n_ids E s0 + 1) mod kDepotNodesPerBlock =? 0 then 1 else 0) dsb dp s3); rewrite ?NBC.
  1,3: unfold store_alloc; destruct DS as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  1,2: eapply hoareW_bind; [eapply (store_alloc_once_d s2 s0 0); [unfold zlen in *; lia| repeat split; try eassumption; lia| exact D5]|].
  1,2: intros [st|]; apply hoareW_pre; intros s3 DS3;
       [apply hoareW_ret; intros s ->; exists (0 + (zlen key + 1)), (0 + 1), (0 + (zlen key + 1)); split; [unfold zlen in *; lia| split; [unfold zlen in *; lia| exact DS3]]|];
       destruct DS3 as (E1 & E2 & E3 & E4 & E5 & E6 & E7);
       (eapply hoareW_bind; [eapply (store_alloc_once_d s3 s0 (0 + (zlen key + 1))); [unfold zlen in *; lia| repeat split; try eassumption; lia| exact E5]|]);
       intros [st|]; apply hoareW_pre; intros s4 DS4; [| apply hoareW_undef];
       apply hoareW_ret; intros s ->; eexists _, _, _; split; [| split; [| exact DS4]]; unfold zlen in *; lia.
  all: intros st; apply hoareW_pre; intros s3 (df & dsb & dp & Hdf & Hdp & (D1 & D2 & D3 & D4 & D5 & D6 & D7)).
  all: apply hoareW_upd_bind; apply hoareW_ret; intros s (sy & -> & ->).
  all: unfold depot_inv6, depot_n_ids, zlen in *; cbn in *; rewrite length_app, Nat2Z.inj_add; cbn.
  all: unfold dphi in *; cbn in *.
  all: split; [| split; [exact D5| split; [lia| split; [lia| split; [| clear -D7 Hdp I6 D6; lia]]]]].
  - apply Z.eqb_eq in NBC. unfold kDepotNodesPerBlock in *. apply Z.mod_divide in NBC; [|lia]. destruct NBC as [m Hm]. clear -Hm I1 I5 D1 D3. nia.
  - apply Z.eqb_eq in NBC. unfold kDepotNodesPerBlock in *. apply Z.mod_divide in NBC; [|lia]. destruct NBC as [m Hm]. clear -Hm I1 I5 D1 D3. nia.
  - unfold kDepotNodesPerBlock in *. lia.
  - apply Z.eqb_neq in NBC. unfold kDepotNodesPerBlock in *.
    match type of NBC with ?x mod _ <> 0 =>
      assert (x <> 65536 * (Z.of_nat (length (as_node_blocks s0)) + 1)) by (intros X; apply NBC; rewrite X, Z.mul_comm; apply Z_mod_mult) end.
    lia.
Qed.

(* [comment removed for export] *)
Lemma store_alloc_once_sci : forall s1 count, 1 <= count <= 32 -> 0 <= as_frames s1 ->
  (as_frames s1 <= kStoreBlockFrames * (zlen (as_store_blocks s1) + 1)
   \/ (as_frames s1 / kStoreBlockFrames <= zlen (as_store_blocks s1) + 1
       /\ (as_frames s1 + count - 1) / kStoreBlockFrames = as_frames s1 / kStoreBlockFrames)) ->
  hoareW (fun s => s = s1) (store_alloc_once E count)
    (fun s' r => 0 <= as_frames s' /\
       match r with
       | Some _ => as_frames s' <= kStoreBlockFrames * (zlen (as_store_blocks s') + 1)
       | None => as_frames s' / kStoreBlockFrames <= zlen (as_store_blocks s') + 1
                 /\ (as_frames s' + count - 1) / kStoreBlockFrames = as_frames s' / kStoreBlockFrames
       end).
Proof.
  intros s1 count Hc F PRE. unfold store_alloc_once.
  assert (Z0 : 0 <= zlen (as_store_blocks s1)) by (unfold zlen; lia).
  apply hoareW_get_bind. intros s ->. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:FIT end.
  - apply Z.eqb_eq in FIT.
    assert (B : as_frames s1 / kStoreBlockFrames <= zlen (as_store_blocks s1) + 1).
    { destruct PRE as [P|[P _]]; [| exact P]. unfold kStoreBlockFrames in *. clear -P F Z0. Z.div_mod_to_equations. nia. }
    apply hoareW_get_bind. intros s ->.
    eapply hoareW_bind with (Q := fun s' _ => 0 <= as_frames s' /\ as_frames s' <= kStoreBlockFrames * (zlen (as_store_blocks s') + 1)).
    + match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:NEW end.
      * eapply hoareW_bind; [apply call_mmap_ordie_eq|]. intros r. apply hoareW_pre. intros s ->. apply hoareW_upd. intros s ->.
        apply andb_prop in NEW as [N1 N2]. apply Z.ltb_lt in N1. apply Z.ltb_lt in N2.
        unfold zlen in *; cbn in *. rewrite length_app; cbn. rewrite Nat2Z.inj_add. cbn.
        unfold kStoreBlockFrames in *. clear -FIT B F Z0 Hc N1 N2. Z.div_mod_to_equations. nia.
      * apply hoareW_ret. intros s ->. unfold zlen in *; cbn in *.
        apply Bool.andb_false_iff in NEW. destruct NEW as [N|N]; apply Z.ltb_ge in N;
          unfold kStoreBlockFrames in *; clear -FIT B F Z0 Hc N; Z.div_mod_to_equations; nia.
    + intros []. apply hoareW_ret. intros s H. exact H.
  - apply Z.eqb_neq in FIT.
    apply hoareW_upd_bind. apply hoareW_ret. intros s (sy & -> & ->). unfold zlen in *; cbn in *.
    destruct PRE as [P|[_ P]]; [| exfalso; exact (FIT (eq_sym P))].
    unfold kStoreBlockFrames in *. clear -FIT P F Z0 Hc. Z.div_mod_to_equations. nia.
Qed.

Lemma store_alloc_sci : forall s1 count, 1 <= count <= 32 -> SCI s1 ->
  hoareW (fun s => s = s1) (store_alloc E count) (fun s' _ => SCI s').
Proof.
  intros s1 count Hc [F S]. unfold store_alloc.
  eapply hoareW_bind; [apply (store_alloc_once_sci s1 count Hc F (or_introl S))|].
  intros [st|]; apply hoareW_pre; intros s2 [F2 P2].
  - apply hoareW_ret. intros s ->. split; assumption.
  - eapply hoareW_bind; [apply (store_alloc_once_sci s2 count Hc F2 (or_intror P2))|].
    intros [st|]; apply hoareW_pre; intros s3 [F3 P3]; [apply hoareW_ret; intros s ->; split; assumption| apply hoareW_undef].
Qed.

Lemma depot_put_sci : forall key, zlen key + 1 <= 32 -> presW SCI (depot_put E key).
Proof.
  intros key KL. assert (K0 : 0 <= zlen key) by (unfold zlen; lia). unfold depot_put. pw.
  all: try (unfold SCI in *; cbn in *; assumption).
  - apply call_mmap_ordie_W.
  - apply hoareW_pre. intros s1 HS. eapply hoareW_conseq; [apply (store_alloc_sci s1); [lia| exact HS]| intros s2 ->; reflexivity| intros s2 r H2; exact H2].
Qed.

Lemma hoareW_conj2 : forall {R} (P : astate -> Prop) (m : AM R) (Q1 Q2 : astate -> R -> Prop),
  hoareW P m Q1 -> hoareW P m Q2 -> hoareW P m (fun s r => Q1 s r /\ Q2 s r).
Proof.
  intros R P m Q1 Q2 H1 H2 s Hs. pose proof (sall_conj _ _ _ (H1 s Hs) (H2 s Hs)) as H.
  eapply sall_mono; [exact H|]. intros [s' [r| |w]]; cbn; tauto.
Qed.

Lemma depot_put_di : forall s0 key, zlen key + 1 <= 32 -> depot_inv s0 ->
  hoareW (fun s => s = s0) (depot_put E key) (fun s' _ => depot_inv s').
Proof.
  intros s0 key KL DI. apply depot_inv_split in DI as [D6 SC].
  eapply hoareW_conseq; [apply hoareW_conj2; [apply (depot_put_di6 s0 key KL D6)| eapply hoareW_conseq; [apply (depot_put_sci key KL)| intros s1 ->; exact SC| intros s1 r H1; exact H1]]| intros s1 H1; exact H1|].
  intros s1 r [H6 HS]. apply depot_inv_split. split; assumption.
Qed.

Lemma amalloc_core_di : forall s0 key n, zlen key + 1 <= 32 -> depot_inv s0 ->
  hoareW (fun s => s = s0) (amalloc_core E key n) (fun s' _ => depot_inv s').
Proof.
  intros s0 key n KL DI. unfold amalloc_core.
  eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s0); auto|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  assert (DI1 : depot_inv (upd_nprimc (from_primary n) (class_id (needed1 n)) s0)) by exact DI.
  eapply hoareW_bind with (Q := fun s' _ => depot_inv s').
  { eapply hoareW_conseq; [| intros ? ->; exact DI1| intros ? ? H; exact H].
    match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b end; [apply cache_pop_di| apply sec_alloc_di]. }
  intros [ab|]; [| apply hoareW_upd_bind; apply hoareW_ret; intros s (sx & DIx & ->); unfold depot_inv, depot_n_ids in *; cbn; exact DIx].
  apply hoareW_pre. intros s1 DI2.
  eapply hoareW_bind; [apply depot_put_di; [exact KL| exact DI2]|]. intros id. cbn beta.
  change (hoareW (fun s => depot_inv s) ?m (fun s' _ => depot_inv s')) with (presW depot_inv m). pw; try pzW; di_same.
Qed.

Lemma afree_core_di : forall s0 key p, zlen key + 1 <= 32 -> depot_inv s0 ->
  hoareW (fun s => s = s0) (afree_core E key p) (fun s' _ => depot_inv s').
Proof.
  intros s0 key p KL DI. unfold afree_core. apply hoareW_get_bind. intros s ->.
  destruct (as_chunks s0 !! (p - kChunkHeaderSize)) as [meta|]; [| apply hoareW_undef].
  destruct (cm_state meta); [| apply hoareW_undef]. destruct (negb (cm_user_beg meta =? p)); [apply hoareW_undef|].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  eapply hoareW_bind; [apply depot_put_di; [exact KL| exact DI]|]. intros fid. cbn beta.
  change (hoareW (fun s => depot_inv s) ?m (fun s' _ => depot_inv s')) with (presW depot_inv m). pw; try apply enqueue_di; try apply drain_di; di_same.
Qed.

Theorem amalloc_di : forall s0 key n, zlen key + 1 <= 32 -> depot_inv s0 ->
  hoareW (fun s => s = s0) (amalloc E key n) (fun s' _ => depot_inv s').
Proof. intros. unfold amalloc. apply amalloc_core_di; assumption. Qed.

Theorem afree_di : forall s0 key p, zlen key + 1 <= 32 -> depot_inv s0 ->
  hoareW (fun s => s = s0) (afree E key p) (fun s' _ => depot_inv s').
Proof.
  intros s0 key p KL DI. unfold afree, ia_init. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  destruct (p =? 0); [apply hoareW_ret; intros s ->; exact DI| apply afree_core_di; [exact KL| exact DI]].
Qed.

Theorem arealloc_di : forall s0 key p n, zlen key + 1 <= 32 -> depot_inv s0 ->
  hoareW (fun s => s = s0) (arealloc E key p n) (fun s' _ => depot_inv s').
Proof.
  intros s0 key p n KL DI. unfold arealloc, ia_init. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  destruct (p =? 0); [apply amalloc_core_di; [exact KL| exact DI]|].
  destruct (n =? 0).
  { eapply hoareW_bind; [apply afree_core_di; [exact KL| exact DI]|]. intros []. apply hoareW_ret. auto. }
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->).
  eapply hoareW_bind; [apply amalloc_core_di; [exact KL| exact DI]|]. intros [q|]; [| apply hoareW_ret; auto].
  apply hoareW_get_bind. intros s1 DI1.
  destruct (as_chunks s1 !! (p - kChunkHeaderSize)) as [meta|]; [| apply hoareW_undef].
  destruct (cm_state meta); [| apply hoareW_undef]. destruct (cm_user_beg meta =? p); [| apply hoareW_undef].
  eapply hoareW_bind; [apply afree_core_di; [exact KL| exact DI1]|]. intros []. apply hoareW_ret. auto.
Qed.

(* [comment removed for export] *)
Theorem depot_growth_amortised : forall P D s,
  AWf E P D s -> depot_inv s -> zlen (ae_keys0 E) <= 1000 -> ae_frames0 E <= 4096 ->
  256 * zlen (as_node_blocks s) + 2048 * zlen (as_store_blocks s) <= as_ndepot_ins s.
Proof.
  intros P D s WF (I1 & I2 & I3 & I4) K0 F0.
  destruct WF as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3)).
  unfold depot_n_ids, kDepotNodesPerBlock, kStoreBlockFrames, zlen in *. rewrite Nat2Z.inj_add in I1.
  pose proof (Zle_0_nat (length (as_node_blocks s))). pose proof (Zle_0_nat (length (as_store_blocks s))). lia.
Qed.

End BU.
End RC__1.
