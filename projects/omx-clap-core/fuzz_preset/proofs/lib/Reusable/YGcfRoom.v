(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: freed_cf appends only a quarantined chunk (ck_n <= kQuarantineMax); FREEG gains the recycle disjunct (recycle_chunk_cq); free_cf_gen / free_cf_room_inv / free_cf_fifo cover it. freed_cf and FREEG statements changed. *)
(* Theorem Labs, 2026-10: fuzz_preset's event-free allocator instance (suffix cf), the ROOM FACTS that
   c-frame-alloc's lib/Spec/PresetRoom.v (P8 part C) asks of the instance's state.
   PresetRoom.v is not on this branch, so its definitions are copied VERBATIM into the module PresetRoom below
   (the class map, room_state, quar_bytes_ok, null_full, room_ok); the statements here are over those names.
   Facts, over the instance's astate under Wf_cf (YG01cf.v) and the model malloc_cf / free_cf (YG00cf.v):
     1. quar_bytes_ok_cf: at an allocation's entry the quarantine's accounted bytes are at most Q_MAX + Q_CACHE,
        with at most kBatchSlots = 1,021 chunks a batch. The invariant is room_inv_cf (cgif's qtight, YG01.v:230,
        which acall_pre_cf already carries through qmeter_cf); malloc_cf and free_cf preserve it.
     2. quar_fifo_cf: the quarantine, oldest first, is a suffix of the free history (free_cf appends freed_cf);
        its global part is at most Q_MAX and its thread part at most Q_CACHE accounted bytes (quar_fifo_parts_cf).
        Per class (quar_class_bound_cf): the quarantine's class-c bytes and chunks are at most those of the last
        frees of the history up to Q_MAX + Q_CACHE accounted bytes (last_frees).
        Q_MAX = 268,435,456 and Q_CACHE = 1,048,576 (cgif's kQuarantineMax / kQuarantineCacheMax) are MEASURED on
        both preset images: a Theorem Labs lane oomroom note, the internal file QCAP.txt.
     3. malloc_cf_null_full: a NULL from malloc_cf whose last environment answer was a grant (ns = true, the flag
        atok_cf passes to its post) is a full class: live + quarantined + batch records + refill > cap.
   The preservation facts are stated with rpost (every return of the tree, with atok_cf's ns flag) and combined
   with any atok_cf fact by atok_cf_rpost, so they compose with model_laws_cf's malloc / free posts.
   No regime_big lemma (ml_malloc_big / ml_free_big) and no st_nev upper bound is used.
   Nothing here is a function's proof (rule 24). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0k YGcfNames YG00cf YG01cf YGcfTok.
(* YG03dcf.v: maybe_drain_cf's merge choice and tail (maybe_drain_cf_eq, merge_choice_mres_cf), by qualified name. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03dcf.
(* PresetRoom.v itself, P8 part C, at lib/Spec: its names are used qualified (PresetRoom.cls, ...). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
From Stdlib Require Sorting.Permutation.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ================================================================ PresetRoom.v *)
(* c-frame-alloc's lib/Spec/PresetRoom.v is now a file of this unit (lib/Spec/PresetRoom.v, copied by path from
   c-frame-alloc-p8 4ec915e66b6): the class map, room_state, quar_bytes_ok, null_full, room_ok, acct_size and
   fifo_ok below are ITS definitions, not a copy of them. Every statement here names them qualified. *)

(* ================================================================ the room view of an astate *)
(* rs_live: the requests of the live blocks (cgif's blocks, YG01.v:212). rs_quar: the accounted size ck_n
   (req_size, at least 1) of every chunk in the quarantine's batches. rs_batches: the batch records. *)
Definition room_of_cf (s : astate) : PresetRoom.room_state :=
  PresetRoom.Build_room_state (map snd (blocks s)) (map ck_n (q_items s)) (Z.of_nat (length (all_batches s))).

(* The room invariant: cgif's qtight (YG01.v:230-231), thread part <= Q_CACHE, global part <= Q_MAX, and
   every chunk marked quarantined accounted in the queue. Wf_cf does not imply it; acall_pre_cf carries it
   (qmeter_cf, YG0ncf.v:156). *)
Definition room_inv_cf (s : astate) : Prop := qtight s.

Lemma room_inv_cf_init : room_inv_cf init_state.
Proof. exact qtight_init. Qed.

(* The quarantine in FIFO order, oldest first: the global batches, then the thread's. *)
Definition q_fifo (s : astate) : list chunk := flat_map b_items (qc_list (st_qglobal s) ++ qc_list (st_qthread s)).
(* The quarantine is a suffix of the free history hist (the chunks freed so far, in order). *)
Definition quar_fifo_cf (hist : list chunk) (s : astate) : Prop := exists pre, hist = pre ++ q_fifo s.
(* What free_cf p appends to the history: the chunk it quarantines. A chunk above kQuarantineMax is not
   quarantined (free_cf's size test, Quarantine::Put): it is recycled at once and appends nothing. *)
Definition freed_cf (s : astate) (p : sptr) : list chunk :=
  match p with
  | PNull => []
  | _ => match find_user (st_chunks s) p with
         | Some k => if ck_n k <=? kQuarantineMax then [mkChunk (ck_beg k) (ck_req k) CQuarantined] else []
         | None => []
         end
  end.

Lemma quar_fifo_cf_init : quar_fifo_cf [] init_state.
Proof. exists []. reflexivity. Qed.

(* ================================================================ the two links to PresetRoom.fifo_ok *)
(* LINK 1. q_items (YG01.v:209) walks the thread's batches then the global ones; q_fifo walks them oldest
   first, the global ones then the thread's. Both are a flat_map of the same two lists, so the accounted
   sizes of one are a permutation of the other's. No premise: it is an identity of the two definitions. *)
Lemma q_fifo_perm_items_cf : forall s, Permutation.Permutation (map ck_n (q_fifo s)) (map ck_n (q_items s)).
Proof.
  intros s. apply Permutation.Permutation_map. unfold q_fifo, q_items, all_batches.
  rewrite !flat_map_app. apply Permutation.Permutation_app_comm.
Qed.

(* LINK 2. ck_n is PresetRoom's acct_size of the request: ck_n k = req_size (ck_req k) and
   req_size n = (if n =? 0 then 1 else n) = Z.max n 1 for a non-negative request. *)
Lemma ck_n_acct_size : forall k, 0 <= ck_req k -> ck_n k = Z.max (ck_req k) 1.
Proof. intros k H. unfold ck_n. symmetry. exact (proj1 (req_size_bounds (ck_req k) H)). Qed.

Lemma map_ck_n_acct_cf : forall l, Forall (fun k => 0 <= ck_req k) l ->
  map ck_n l = map PresetRoom.acct_size (map ck_req l).
Proof.
  intros l H. induction H as [|k t Hk Ht IH]; [reflexivity|].
  cbn [map]. rewrite (ck_n_acct_size k Hk), IH. unfold PresetRoom.acct_size. reflexivity.
Qed.

(* A chunk of a well-formed state has a non-negative request, so LINK 2 applies to any history of the
   model's own chunks (freed_cf_req_cf below, for the chunks free_cf appends). *)
Lemma chunk_ok_cf_req : forall {cp : CfParams} s k, chunk_ok_cf s k -> 0 <= ck_req k.
Proof. intros cp s k [Hr _]. lia. Qed.

(* THE LINK, in the form P8's top theorem takes: a free history whose quarantine is its suffix gives
   PresetRoom.fifo_ok over the accounted sizes, against the room view's rs_quar. *)
Lemma fifo_ok_of_quar_fifo_cf : forall hist s, quar_fifo_cf hist s ->
  PresetRoom.fifo_ok (map ck_n hist) (PresetRoom.rs_quar (room_of_cf s)).
Proof.
  intros hist s [pre ->]. exists (map ck_n pre), (map ck_n (q_fifo s)).
  split; [rewrite map_app; reflexivity | exact (q_fifo_perm_items_cf s)].
Qed.

(* and over the RAW requests of the history, PresetRoom.quar17_flush_raw's form *)
Lemma fifo_ok_acct_of_quar_fifo_cf : forall hist s, quar_fifo_cf hist s ->
  Forall (fun k => 0 <= ck_req k) hist ->
  PresetRoom.fifo_ok (map PresetRoom.acct_size (map ck_req hist)) (PresetRoom.rs_quar (room_of_cf s)).
Proof.
  intros hist s H Hr. rewrite <- (map_ck_n_acct_cf hist Hr). exact (fifo_ok_of_quar_fifo_cf hist s H).
Qed.

(* ================================================================ rpost: every return, with atok_cf's flag *)
Fixpoint rpost {A : Type} (ns : bool) (t : itree astate A) (P : bool -> A -> Prop) : Prop :=
  match t with
  | IRet a => P ns a
  | ISpin _ => True
  | IFail _ => True
  | IAsk q snap k => forall z, aok snap q z -> rpost (progz q z) (k z) P
  end.

Lemma rpost_mono {A} (t : itree astate A) : forall ns (P P' : bool -> A -> Prop),
  (forall b a, P b a -> P' b a) -> rpost ns t P -> rpost ns t P'.
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns P P' HP H.
  - exact (HP _ _ H).
  - intros z Hz. exact (IH z _ P P' HP (H z Hz)).
  - exact I.
  - exact I.
Qed.

Lemma rpost_ibind {A B} (t : itree astate A) : forall ns (k : A -> itree astate B) (P : bool -> B -> Prop),
  rpost ns t (fun ns' a => rpost ns' (k a) P) -> rpost ns (ibind t k) P.
Proof.
  induction t as [a | q snap c IH | pc | f]; cbn; intros ns k P H.
  - exact H.
  - intros z Hz. apply IH. exact (H z Hz).
  - exact I.
  - exact I.
Qed.

Lemma rpost_bind {A B} ns (m : M B) (k : B -> M A) s (P : bool -> A * astate -> Prop) :
  rpost ns (m s) (fun ns' r => rpost ns' (k (fst r) (snd r)) P) -> rpost ns (bind m k s) P.
Proof.
  intros H. unfold bind. apply rpost_ibind. eapply rpost_mono; [|exact H]. intros b [x s'] Hb. exact Hb.
Qed.

Lemma rpost_and {A} (t : itree astate A) : forall ns (P P' : bool -> A -> Prop),
  rpost ns t P -> rpost ns t P' -> rpost ns t (fun b a => P b a /\ P' b a).
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns P P' H H'.
  - split; assumption.
  - intros z Hz. exact (IH z _ P P' (H z Hz) (H' z Hz)).
  - exact I.
  - exact I.
Qed.

Lemma rpost_of_apost {A} (t : itree astate A) : forall ns (P' : A -> Prop) (P : bool -> A -> Prop),
  apost t P' -> (forall b a, P' a -> P b a) -> rpost ns t P.
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns P' P H HP.
  - apply HP. apply (H []). cbn. reflexivity.
  - intros z Hz. apply (IH z _ P'); [|exact HP]. intros tr a Hy. apply (H ((q, z) :: tr)). cbn.
    split; [reflexivity | split; [exact Hz | exact Hy]].
  - exact I.
  - exact I.
Qed.

Lemma rpost_apath {A} (t : itree astate A) : forall ns P tr a, rpost ns t P -> apath t tr a -> exists b, P b a.
Proof.
  induction t as [a' | q snap k IH | pc | f]; cbn; intros ns P tr a H Hy.
  - destruct tr; [subst; exists ns; exact H | destruct Hy].
  - destruct tr as [|[q' z] tr']; [destruct Hy|]. destruct Hy as (-> & Hz & Hy). exact (IH z _ P tr' a (H z Hz) Hy).
  - destruct tr; destruct Hy.
  - destruct tr; destruct Hy.
Qed.

(* rpost's ns-free form gives cgif's path-wise apost (YG0k.v:102). *)
Lemma apost_of_rpost {A} (t : itree astate A) : forall ns (P : A -> Prop),
  rpost ns t (fun _ a => P a) -> apost t P.
Proof. intros ns P H tr a Hy. destruct (rpost_apath t ns _ tr a H Hy) as [_ Ha]. exact Ha. Qed.

(* THE COMPOSITION with the atok_cf layer: any atok_cf fact (model_laws_cf's malloc / free posts) gains an
   rpost fact as a conjunct of its post. *)
Lemma atok_cf_rpost {cp : CfParams} {A} (t : itree astate A) : forall ns (Q P : bool -> A -> Prop),
  atok_cf ns t Q -> rpost ns t P -> atok_cf ns t (fun b a => Q b a /\ P b a).
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q P HQ HP.
  - split; assumption.
  - destruct HQ as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH; [exact (Hk z Hz) | exact (HP z Hz)].
  - exact HQ.
  - exact HQ.
Qed.

Lemma rpost_true {A} (t : itree astate A) : forall ns, rpost ns t (fun _ _ => True).
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns.
  - exact I.
  - intros z _. apply IH.
  - exact I.
  - exact I.
Qed.

Lemma rpost_all {A} (t : itree astate A) : forall ns (P : bool -> A -> Prop), (forall b a, P b a) -> rpost ns t P.
Proof. intros ns P H. eapply rpost_mono; [|apply rpost_true]. intros b a _. apply H. Qed.

Lemma rpost_impl {A} (Pre : Prop) (t : itree astate A) : forall ns (Q : bool -> A -> Prop),
  (Pre -> rpost ns t Q) -> rpost ns t (fun b a => Pre -> Q b a).
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H.
  - exact H.
  - intros z Hz. apply IH. intros HP. exact (H HP z Hz).
  - exact I.
  - exact I.
Qed.

(* ================================================================ the class map agrees with cgif's *)
Lemma size_of_class_eq : forall c, 1 <= c <= 31 -> PresetRoom.size_of_class c = class_size c.
Proof.
  assert (H : zall (Z.to_nat (31 - 1 + 1)) 1 (fun c => PresetRoom.size_of_class c =? class_size c) = true)
    by (vm_compute; reflexivity).
  intros c Hc. apply Z.eqb_eq. exact (zall_range 1 31 _ H c Hc).
Qed.

Lemma class_id_eq : forall s, 1 <= s <= kMaxSize -> PresetRoom.class_id s = class_id s.
Proof.
  assert (H : zall (Z.to_nat (65536 - 1 + 1)) 1 (fun s => PresetRoom.class_id s =? class_id s) = true)
    by (vm_compute; reflexivity).
  intros s Hs. apply Z.eqb_eq. exact (zall_range 1 65536 _ H s Hs).
Qed.

Lemma needed0_eq : forall n, PresetRoom.needed0 n = needed_primary n.
Proof. intros n. reflexivity. Qed.

Lemma is_primary_eq : forall n, PresetRoom.is_primary n = from_primary n.
Proof. intros n. reflexivity. Qed.

Lemma needed_primary_pos : forall n, 24 <= needed_primary n.
Proof.
  intros n. unfold needed_primary, rounded_size.
  pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)) as [[H1 _] _]. pose proof (rz_size_bounds n) as [H2 _]. lia.
Qed.

Lemma chunk_class_range : forall n, from_primary n = true -> 1 <= chunk_class n <= 30.
Proof.
  intros n H. unfold chunk_class, needed_size. rewrite H. unfold from_primary in H. apply Z.leb_le in H.
  pose proof (needed_primary_pos n). exact (proj1 (class_id_ok (needed_primary n) ltac:(lia))).
Qed.

Lemma cls_primary : forall n, from_primary n = true -> PresetRoom.cls n = Some (chunk_class n).
Proof.
  intros n H. unfold PresetRoom.cls. rewrite is_primary_eq, H. f_equal.
  unfold chunk_class, needed_size. rewrite H, needed0_eq. apply class_id_eq.
  unfold from_primary in H. apply Z.leb_le in H. pose proof (needed_primary_pos n). lia.
Qed.

Lemma cls_secondary : forall n, from_primary n = false -> PresetRoom.cls n = None.
Proof. intros n H. unfold PresetRoom.cls. rewrite is_primary_eq, H. reflexivity. Qed.

Lemma in_cls_req_size : forall c n, 0 <= n -> PresetRoom.in_cls c (req_size n) = PresetRoom.in_cls c n.
Proof.
  intros c n Hn. unfold req_size. destruct (Z.eqb_spec n 0) as [->|_]; [|reflexivity].
  vm_compute. reflexivity.
Qed.

Lemma refill_eq : forall c, 1 <= c <= 31 -> PresetRoom.refill c = max_cached c / 2.
Proof. intros c Hc. unfold PresetRoom.refill, PresetRoom.max_cached, max_cached. rewrite size_of_class_eq by exact Hc. reflexivity. Qed.

Lemma cap_eq : forall c, 1 <= c <= 31 -> PresetRoom.cap c = kFreeArrayOffset / class_size c.
Proof. intros c Hc. unfold PresetRoom.cap. rewrite size_of_class_eq by exact Hc. reflexivity. Qed.

(* ================================================================ list facts *)
Definition sptr_eq_dec : forall p q : sptr, {p = q} + {p <> q}.
Proof. decide equality; first [apply Z.eq_dec | apply Nat.eq_dec]. Defined.

Definition chunk_eq_dec : forall a b : chunk, {a = b} + {a <> b}.
Proof. decide equality; first [apply Z.eq_dec | apply sptr_eq_dec | decide equality]. Defined.

Lemma items_n_nonneg : forall l, Forall (fun x => 0 <= ck_n x) l -> 0 <= items_n l.
Proof.
  induction l as [|k t IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [Hk Ht]. rewrite items_n_cons. specialize (IH Ht). lia.
Qed.

Lemma items_n_incl : forall l1 l2, NoDup l1 -> incl l1 l2 -> Forall (fun x => 0 <= ck_n x) l2 ->
  items_n l1 <= items_n l2.
Proof.
  induction l1 as [|a t IH]; intros l2 Hnd Hinc Hpos.
  - rewrite items_n_nil. apply items_n_nonneg. exact Hpos.
  - apply NoDup_cons_iff in Hnd as [Hna Hndt].
    destruct (in_split a l2 (Hinc a (or_introl eq_refl))) as (u & v & ->).
    assert (Hinc' : incl t (u ++ v)).
    { intros y Hy. pose proof (Hinc y (or_intror Hy)) as Hy2. apply in_app_or in Hy2 as [Hu|[Heq|Hv]].
      - apply in_or_app. left. exact Hu.
      - subst. contradiction.
      - apply in_or_app. right. exact Hv. }
    apply Forall_app in Hpos as [Hu Hav]. apply Forall_cons_iff in Hav as [Ha Hv0].
    assert (Hpos' : Forall (fun x => 0 <= ck_n x) (u ++ v)) by (apply Forall_app; split; assumption).
    specialize (IH (u ++ v) Hndt Hinc' Hpos').
    rewrite items_n_app in IH. rewrite items_n_cons, items_n_app, items_n_cons. lia.
Qed.

Lemma quar_nl_filter : forall l, quar_nl l = items_n (filter (fun k => negb (is_alloc k)) l).
Proof.
  induction l as [|k t IH]; [reflexivity|]. cbn [filter]. unfold quar_nl in *. cbn [fold_right].
  destruct (is_alloc k); cbn [negb]; [exact IH|]. rewrite IH, items_n_cons. reflexivity.
Qed.

Lemma zsum_map_ck_n : forall l, PresetRoom.zsum (map ck_n l) = items_n l.
Proof. induction l as [|k t IH]; [reflexivity|]. cbn [map PresetRoom.zsum]. rewrite IH. reflexivity. Qed.

Lemma sum_bytes_items_rm : forall l,
  sum_bytes l = kBatchBytes * Z.of_nat (length l) + items_n (flat_map b_items l).
Proof.
  induction l as [|b t IH]; [cbn; lia|]. unfold sum_bytes in *. cbn [fold_right length flat_map].
  rewrite Nat2Z.inj_succ, items_n_app, IH. unfold b_bytes, items_n. lia.
Qed.

Lemma length_flat_items : forall l, Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) l ->
  Z.of_nat (length (flat_map b_items l)) <= kBatchSlots * Z.of_nat (length l).
Proof.
  induction l as [|b t IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [Hb Ht]. cbn [flat_map length]. rewrite length_app, Nat2Z.inj_add, Nat2Z.inj_succ.
  specialize (IH Ht). apply Nat2Z.inj_le in Hb. rewrite Z2Nat.id in Hb by (unfold kBatchSlots; lia). lia.
Qed.

Lemma chunk_ok_cf_n : forall {cp : CfParams} s k, chunk_ok_cf s k -> 1 <= ck_n k.
Proof.
  intros cp s k [Hr _]. unfold ck_n. pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
Qed.

(* upd_chunk adds at most the new chunk's quarantined bytes, when no chunk accounts negative bytes *)
Lemma quar_nl_upd : forall l k, Forall (fun x => 0 <= ck_n x) l ->
  quar_nl (upd_chunk l k) <= quar_nl l + (if is_alloc k then 0 else ck_n k).
Proof.
  induction l as [|k0 t IH]; intros k Hpos; cbn [upd_chunk].
  - unfold quar_nl. cbn [fold_right]. destruct (is_alloc k); lia.
  - apply Forall_cons_iff in Hpos as [H0 Ht]. destruct (sptr_eqb (ck_beg k0) (ck_beg k)).
    + unfold quar_nl. cbn [fold_right]. destruct (is_alloc k), (is_alloc k0); lia.
    + specialize (IH k Ht). unfold quar_nl in *. cbn [fold_right]. destruct (is_alloc k0), (is_alloc k); lia.
Qed.

Lemma del_chunk_incl : forall l b x, In x (del_chunk l b) -> In x l.
Proof.
  induction l as [|k t IH]; intros b x H; cbn [del_chunk] in H; [exact H|].
  destruct (sptr_eqb (ck_beg k) b); [right; exact H|].
  destruct H as [<-|H]; [left; reflexivity | right; exact (IH b x H)].
Qed.

Lemma nodup_del_chunk : forall l b, NoDup (map ck_beg l) -> NoDup (map ck_beg (del_chunk l b)).
Proof.
  induction l as [|k t IH]; intros b H; cbn [del_chunk]; [exact H|]. cbn [map] in H.
  apply NoDup_cons_iff in H as [Hn Ht]. destruct (sptr_eqb (ck_beg k) b); [exact Ht|]. cbn [map].
  constructor; [|exact (IH b Ht)]. intros Hin. apply Hn. apply in_map_iff in Hin as (y & Hy & Hy2).
  apply in_map_iff. exists y. split; [exact Hy | exact (del_chunk_incl _ _ _ Hy2)].
Qed.

(* deleting a present quarantined chunk by its base takes exactly its bytes off the quarantined count *)
Lemma quar_nl_del : forall l k, NoDup (map ck_beg l) -> In k l -> ck_state k = CQuarantined ->
  quar_nl (del_chunk l (ck_beg k)) + ck_n k = quar_nl l.
Proof.
  intros l k Hnd Hin Hst. destruct (in_split k l Hin) as (l1 & l2 & ->).
  assert (Hn1 : ~ In (ck_beg k) (map ck_beg l1)).
  { rewrite map_app in Hnd. cbn [map] in Hnd. apply NoDup_app_iff in Hnd as (_ & _ & Hx).
    intros H. exact (Hx (ck_beg k) H (or_introl eq_refl)). }
  rewrite del_chunk_present by exact Hn1. rewrite quar_nl_split. unfold is_alloc. rewrite Hst. lia.
Qed.

Lemma map_beg_upd : forall l k, In (ck_beg k) (map ck_beg l) -> map ck_beg (upd_chunk l k) = map ck_beg l.
Proof.
  induction l as [|k0 t IH]; intros k H; [destruct H|]. cbn [upd_chunk map] in *.
  destruct (sptr_eqb (ck_beg k0) (ck_beg k)) eqn:E.
  - apply sptr_eqb_spec in E. cbn [map]. rewrite E. reflexivity.
  - cbn [map]. f_equal. apply IH. destruct H as [H|H]; [|exact H].
    rewrite H, sptr_eqb_refl in E. discriminate.
Qed.

(* qc_push (YG00.v:430-437): the pushed chunk lands last, the byte count stays the batches' sum, and at most
   one batch is added *)
Lemma qc_push_items : forall q k nb, (nb = None -> need_new_batch q = false) ->
  flat_map b_items (qc_list (qc_push q k nb)) = flat_map b_items (qc_list q) ++ [k].
Proof.
  intros q k [b|] H; unfold qc_push; cbn [qc_list].
  - rewrite flat_map_app. reflexivity.
  - specialize (H eq_refl). unfold need_new_batch in H.
    destruct (rev (qc_list q)) as [|lastb initr] eqn:Er; [try rewrite Er in H; discriminate|].
    assert (Eq : qc_list q = rev initr ++ [lastb]) by (rewrite <- (rev_involutive (qc_list q)), Er; reflexivity).
    rewrite Eq, !flat_map_app. cbn [flat_map b_items]. rewrite !app_nil_r, app_assoc. reflexivity.
Qed.

Lemma qc_push_bytes : forall q k nb, (nb = None -> need_new_batch q = false) ->
  qc_bytes q = sum_bytes (qc_list q) -> qc_bytes (qc_push q k nb) = sum_bytes (qc_list (qc_push q k nb)).
Proof.
  intros q k [b|] H Hq; unfold qc_push; cbn [qc_list qc_bytes].
  - rewrite sum_bytes_app, Hq. unfold sum_bytes, b_bytes. cbn [fold_right b_items]. lia.
  - specialize (H eq_refl). unfold need_new_batch in H.
    destruct (rev (qc_list q)) as [|lastb initr] eqn:Er; [try rewrite Er in H; discriminate|].
    assert (Eq : qc_list q = rev initr ++ [lastb]) by (rewrite <- (rev_involutive (qc_list q)), Er; reflexivity).
    rewrite Hq, Eq, !sum_bytes_app. pose proof (b_bytes_app1 lastb k) as E. unfold sum_bytes in *. cbn [fold_right]. lia.
Qed.

Lemma fa_pop_n_nonempty : forall fuel size n l acc tops rest,
  fa_pop_n fuel size n l acc = Some (tops, rest) -> (acc <> [] \/ 1 <= n) -> tops <> [].
Proof.
  induction fuel as [|f IH]; intros size n l acc tops rest H Hne; cbn [fa_pop_n] in H; [discriminate|].
  destruct (Z.leb_spec n 0) as [Hn|Hn].
  - injection H as <- <-. destruct Hne as [Hne|Hne]; [|lia]. intros Hr. apply Hne.
    apply (f_equal (@rev Z)) in Hr. rewrite rev_involutive in Hr. exact Hr.
  - destruct (fa_pop size l) as [[off l']|]; [|discriminate]. apply (IH _ _ _ _ _ _ H). left. discriminate.
Qed.

(* The arm's test (YG00cf.v:159) fails only when the request does not fit below kFreeArrayOffset: the mapped
   size and kFreeArrayOffset are both multiples of kUserMapSize. *)
Lemma arm_of_full : forall m total, m mod kUserMapSize = 0 -> m < total ->
  kFreeArrayOffset < m + round_up (total - m) kUserMapSize -> kFreeArrayOffset < total.
Proof.
  intros m total Hm Hlt Hfull. apply Z.nle_gt. intros Hle.
  assert (Hd : (kFreeArrayOffset - m) mod kUserMapSize = 0).
  { pose proof (Z.div_mod m kUserMapSize ltac:(unfold kUserMapSize; lia)) as Dm. rewrite Hm, Z.add_0_r in Dm.
    replace (kFreeArrayOffset - m) with ((14336 - m / kUserMapSize) * kUserMapSize)
      by (unfold kFreeArrayOffset, kUserMapSize in *; lia).
    apply Z_mod_mult. }
  pose proof (round_up_le (total - m) kUserMapSize (kFreeArrayOffset - m) ltac:(unfold kUserMapSize; lia)
    ltac:(lia) Hd). lia.
Qed.

Lemma znth_init_caches : forall l c, 0 <= c <= 31 ->
  znth pclass0 c (init_caches l) = mkPC (max_cached c) (pc_chunks (znth pclass0 c l)).
Proof.
  intros l c Hc. pose proof (cache_after_init (set_cache l init_state) c Hc) as E.
  unfold cache in E. cbn [st_cache set_cache_inited set_cache] in E. exact E.
Qed.

Lemma length_init_caches : forall l, length (init_caches l) = 32%nat.
Proof. intros l. unfold init_caches. rewrite length_map, length_seq. reflexivity. Qed.

Lemma length_filter_map : forall (f : Z -> bool) (g : chunk -> Z) l,
  length (filter f (map g l)) = length (filter (fun x => f (g x)) l).
Proof.
  induction l as [|k t IH]; [reflexivity|]. cbn [map filter].
  destruct (f (g k)); cbn [length]; rewrite IH; reflexivity.
Qed.

(* ================================================================ walking a model tree with rpost *)
(* get_region / get_pc are binds and mcheck / aGranted / aDestroyed do not reduce on an open argument, so cbn
   would fold them back: they are unfolded outright. *)
Ltac rred := try unfold get_region; try unfold get_pc; try unfold mcheck; try unfold aGranted;
  try unfold aDestroyed; cbn [rpost ret get put modify askz tick mcheck fail spin progz aGranted aDestroyed
  get_region set_region get_pc set_pc fst snd negb qc0 pclass0
  st_regions st_cache_inited st_cache st_chunks st_secs st_sec_arr st_sec_reserved st_qthread st_qglobal
  st_fs st_depot st_internal_inited st_nev
  set_regions set_cache_inited set_cache set_chunks set_secs set_sec_arr set_sec_reserved set_qthread
  set_qglobal set_fs set_depot set_internal_inited set_nev
  qc_list qc_bytes rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes pc_max pc_chunks].
Tactic Notation "rred" "in" "*" := cbn [rpost ret get put modify askz tick mcheck fail spin progz aGranted
  aDestroyed get_region set_region get_pc set_pc fst snd negb qc0 pclass0
  st_regions st_cache_inited st_cache st_chunks st_secs st_sec_arr st_sec_reserved st_qthread st_qglobal
  st_fs st_depot st_internal_inited st_nev
  set_regions set_cache_inited set_cache set_chunks set_secs set_sec_arr set_sec_reserved set_qthread
  set_qglobal set_fs set_depot set_internal_inited set_nev
  qc_list qc_bytes rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes pc_max pc_chunks] in *.
Tactic Notation "rred" "in" hyp(H) := cbn [rpost ret get put modify askz tick mcheck fail spin progz aGranted
  aDestroyed get_region set_region get_pc set_pc fst snd negb qc0 pclass0
  st_regions st_cache_inited st_cache st_chunks st_secs st_sec_arr st_sec_reserved st_qthread st_qglobal
  st_fs st_depot st_internal_inited st_nev
  set_regions set_cache_inited set_cache set_chunks set_secs set_sec_arr set_sec_reserved set_qthread
  set_qglobal set_fs set_depot set_internal_inited set_nev
  qc_list qc_bytes rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes pc_max pc_chunks] in H.

Ltac dands := repeat match goal with H : _ /\ _ |- _ => destruct H end.
(* binds and reductions only *)
Ltac rgo := repeat (rred; first [ exact I | match goal with |- rpost _ (bind _ _ _) _ => apply rpost_bind end ]); rred.
(* a sub-call by its lemma *)
Ltac rsub lem := eapply rpost_mono; [|apply lem]; cbv beta; intros ? [? ?] ?.
Ltac rhook := fail.
Ltac rleaf := fail.
(* the whole tree: every branch, sub-calls by rhook, leaves by rleaf *)
Ltac rwalk := repeat (rred; first [ progress intros | exact I | solve [rleaf]
  | match goal with |- rpost _ (bind _ _ _) _ => apply rpost_bind end
  | rhook
  | match goal with |- context [match ?e with _ => _ end] => destruct e eqn:? end ]); rred.
Ltac dle H := match goal with |- rpost _ ((if ?a <=? ?b then _ else _) _) _ => destruct (Z.leb_spec a b) as [H|H] end.
Ltac dlt H := match goal with |- rpost _ ((if ?a <? ?b then _ else _) _) _ => destruct (Z.ltb_spec a b) as [H|H] end.
Ltac dif := match goal with |- rpost _ ((if ?b then _ else _) _) _ => destruct b end.

(* frames: the chunk list and both queues unchanged (CQ); regions and caches too (ER) *)
Definition CQ (s x : astate) : Prop :=
  st_chunks x = st_chunks s /\ st_qthread x = st_qthread s /\ st_qglobal x = st_qglobal s.
Definition ER (s x : astate) : Prop := st_regions x = st_regions s /\ st_cache x = st_cache s /\ CQ s x.
Ltac fr_leaf := unfold ER, CQ in *; rred in *; dands; repeat split; congruence.
#[local] Ltac rleaf ::= fr_leaf.

(* ================================================================ per-class bytes of a chunk list *)
Definition cbytes (c : Z) (l : list chunk) : Z := items_n (filter (fun k => PresetRoom.in_cls c (ck_n k)) l).
Definition ccount (c : Z) (l : list chunk) : nat := length (filter (fun k => PresetRoom.in_cls c (ck_n k)) l).
(* the longest prefix of l whose accounted bytes stay within T *)
Fixpoint take_within (T : Z) (l : list chunk) : list chunk :=
  match l with [] => [] | k :: t => if ck_n k <=? T then k :: take_within (T - ck_n k) t else [] end.
(* the last frees of a history, newest last, up to T accounted bytes in total *)
Definition last_frees (T : Z) (hist : list chunk) : list chunk := rev (take_within T (rev hist)).

Lemma cbytes_app : forall c l1 l2, cbytes c (l1 ++ l2) = cbytes c l1 + cbytes c l2.
Proof. intros c l1 l2. unfold cbytes. rewrite filter_app, items_n_app. reflexivity. Qed.

Lemma ccount_app : forall c l1 l2, ccount c (l1 ++ l2) = (ccount c l1 + ccount c l2)%nat.
Proof. intros c l1 l2. unfold ccount. rewrite filter_app, length_app. reflexivity. Qed.

Lemma cbytes_nonneg : forall c l, Forall (fun x => 0 <= ck_n x) l -> 0 <= cbytes c l.
Proof.
  intros c l H. unfold cbytes. apply items_n_nonneg. apply Forall_forall. intros x Hx.
  apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall _ _) H x Hx).
Qed.

Lemma items_n_rev : forall l, items_n (rev l) = items_n l.
Proof.
  induction l as [|k t IH]; [reflexivity|]. cbn [rev]. rewrite items_n_app, IH.
  change (items_n [k]) with (ck_n k + 0). change (items_n (k :: t)) with (ck_n k + items_n t). lia.
Qed.

Lemma take_within_app : forall l1 l2 T, Forall (fun x => 0 <= ck_n x) l1 -> items_n l1 <= T ->
  take_within T (l1 ++ l2) = l1 ++ take_within (T - items_n l1) l2.
Proof.
  induction l1 as [|k t IH]; intros l2 T H HT.
  - rewrite items_n_nil, Z.sub_0_r. reflexivity.
  - apply Forall_cons_iff in H as [Hk Ht]. rewrite items_n_cons in HT |- *. pose proof (items_n_nonneg t Ht).
    cbn [app take_within]. destruct (Z.leb_spec (ck_n k) T) as [_|Hgt]; [|lia].
    rewrite (IH l2 (T - ck_n k) Ht) by lia.
    replace (T - ck_n k - items_n t) with (T - (ck_n k + items_n t)) by lia. reflexivity.
Qed.

Lemma take_within_incl : forall T l x, In x (take_within T l) -> In x l.
Proof.
  intros T l. revert T. induction l as [|k t IH]; intros T x H; cbn [take_within] in H; [exact H|].
  destruct (ck_n k <=? T); [|destruct H]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH _ _ H)].
Qed.

Lemma take_within_prefix : forall T l, exists rest, l = take_within T l ++ rest.
Proof.
  intros T l. revert T. induction l as [|k t IH]; intros T; [exists []; reflexivity|]. cbn [take_within].
  destruct (ck_n k <=? T); [|exists (k :: t); reflexivity].
  destruct (IH (T - ck_n k)) as [rest E]. exists rest. cbn [app]. rewrite <- E. reflexivity.
Qed.

Lemma take_within_sum : forall T l, 0 <= T -> items_n (take_within T l) <= T.
Proof.
  intros T l. revert T. induction l as [|k t IH]; intros T HT; cbn [take_within]; [rewrite items_n_nil; exact HT|].
  destruct (Z.leb_spec (ck_n k) T); [|rewrite items_n_nil; exact HT].
  rewrite items_n_cons. pose proof (IH (T - ck_n k) ltac:(lia)). lia.
Qed.

(* last_frees T hist is a suffix of hist, of at most T accounted bytes *)
Lemma last_frees_suffix : forall T hist, exists pre, hist = pre ++ last_frees T hist.
Proof.
  intros T hist. destruct (take_within_prefix T (rev hist)) as [rest E]. exists (rev rest). unfold last_frees.
  rewrite <- rev_app_distr, <- E, rev_involutive. reflexivity.
Qed.

Lemma last_frees_total : forall T hist, 0 <= T -> items_n (last_frees T hist) <= T.
Proof. intros T hist HT. unfold last_frees. rewrite items_n_rev. exact (take_within_sum T _ HT). Qed.

Lemma cbytes_q : forall c s, cbytes c (q_items s) = cbytes c (q_fifo s).
Proof. intros c s. unfold q_items, q_fifo, all_batches. rewrite !flat_map_app, !cbytes_app. lia. Qed.

Lemma ccount_q : forall c s, ccount c (q_items s) = ccount c (q_fifo s).
Proof. intros c s. unfold q_items, q_fifo, all_batches. rewrite !flat_map_app, !ccount_app. lia. Qed.

Lemma items_n_q : forall s, items_n (q_items s) = items_n (q_fifo s).
Proof. intros s. unfold q_items, q_fifo, all_batches. rewrite !flat_map_app, !items_n_app. lia. Qed.

(* ccount of the queue is PresetRoom's ccnt of rs_quar *)
Lemma ccount_ccnt : forall c s, ccount c (q_items s) = PresetRoom.ccnt c (PresetRoom.rs_quar (room_of_cf s)).
Proof.
  intros c s. unfold ccount, PresetRoom.ccnt, room_of_cf. cbn [PresetRoom.rs_quar].
  rewrite length_filter_map. reflexivity.
Qed.

(* the FIFO steps on a free history *)
Lemma quar_fifo_malloc_step : forall hist s s', quar_fifo_cf hist s -> q_fifo s' = q_fifo s -> quar_fifo_cf hist s'.
Proof. intros hist s s' [pre ->] E. exists pre. rewrite E. reflexivity. Qed.

Lemma quar_fifo_free_step : forall hist s p s' P, quar_fifo_cf hist s ->
  q_fifo s ++ freed_cf s p = flat_map b_items P ++ q_fifo s' -> quar_fifo_cf (hist ++ freed_cf s p) s'.
Proof.
  intros hist s p s' P [pre ->] E. exists (pre ++ flat_map b_items P).
  rewrite <- app_assoc, E, app_assoc. reflexivity.
Qed.

Section ROOM.
Context {ci : CfImg} {cp : CfParams}.

(* ================================================================ fact 1: quar_bytes_ok *)
Theorem quar_bytes_ok_cf : forall U s, Wf_cf U s -> room_inv_cf s -> PresetRoom.quar_bytes_ok (room_of_cf s).
Proof.
  intros U s W (T1 & T2 & _). pose proof (wfc_quarantine _ _ _ _ _ W) as Q.
  unfold PresetRoom.quar_bytes_ok, room_of_cf. cbn [PresetRoom.rs_quar PresetRoom.rs_batches].
  split; [|split; [|split]].
  - apply Forall_map. eapply Forall_impl; [|exact (wq_items _ Q)]. cbv beta. intros k [Hk _].
    exact (chunk_ok_cf_n s k (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk)).
  - lia.
  - rewrite length_map. unfold q_items.
    assert (HB : Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches s)).
    { eapply Forall_impl; [|exact (wq_batches _ Q)]. cbv beta. intros b Hb. exact (proj2 Hb). }
    pose proof (length_flat_items _ HB) as H. unfold PresetRoom.Q_BATCH, kBatchSlots in *. lia.
  - rewrite zsum_map_ck_n. unfold q_items.
    pose proof (sum_bytes_items_rm (all_batches s)) as E. unfold all_batches in E |- *.
    rewrite sum_bytes_app, <- (wq_bytes_t _ Q), <- (wq_bytes_g _ Q) in E.
    unfold PresetRoom.QT, PresetRoom.Q_MAX, PresetRoom.Q_CACHE, PresetRoom.Q_BATCH_BYTES,
      kBatchBytes, kQuarantineMax, kQuarantineCacheMax in *. lia.
Qed.

(* Every chunk marked quarantined is in the queue: the queue's chunks are distinct quarantined chunks
   (wq_items, wq_nodup), each accounts at least 1 byte, and qtight's quar_n <= queued_n leaves no room for
   one more. *)
Lemma quar_in_q : forall U s, Wf_cf U s -> qtight s ->
  forall k, In k (st_chunks s) -> ck_state k = CQuarantined -> In k (q_items s).
Proof.
  intros U s W (_ & _ & Hqn) k Hk Hst.
  destruct (in_dec chunk_eq_dec k (q_items s)) as [Hin|Hni]; [exact Hin|exfalso].
  pose proof (wfc_quarantine _ _ _ _ _ W) as Q. pose proof (wfc_chunks _ _ _ _ _ W) as HC.
  assert (Hpos : Forall (fun x => 0 <= ck_n x) (st_chunks s)).
  { eapply Forall_impl; [|exact HC]. cbv beta. intros x Hx. pose proof (chunk_ok_cf_n s x Hx). lia. }
  unfold quar_n, queued_n in Hqn. rewrite quar_nl_filter in Hqn.
  set (QC := filter (fun x => negb (is_alloc x)) (st_chunks s)) in *.
  assert (HndC : NoDup (st_chunks s)) by exact (NoDup_map_inv _ _ (wfc_chunks_nodup _ _ _ _ _ W)).
  assert (HndQ : NoDup (q_items s)) by exact (NoDup_map_inv _ _ (wq_nodup _ Q)).
  assert (HndK : NoDup (k :: q_items s)) by (constructor; assumption).
  assert (Hinc : incl (k :: q_items s) QC).
  { intros x [<-|Hx]; unfold QC; apply filter_In.
    - split; [exact Hk|]. unfold is_alloc. rewrite Hst. reflexivity.
    - pose proof (proj1 (Forall_forall _ _) (wq_items _ Q) x Hx) as [Hx1 Hx2].
      split; [exact Hx1|]. unfold is_alloc. rewrite Hx2. reflexivity. }
  assert (HposQC : Forall (fun x => 0 <= ck_n x) QC).
  { apply Forall_forall. intros x Hx. unfold QC in Hx. apply filter_In in Hx as [Hx _].
    exact (proj1 (Forall_forall _ _) Hpos x Hx). }
  pose proof (items_n_incl (k :: q_items s) QC HndK Hinc HposQC) as Hle. rewrite items_n_cons in Hle.
  pose proof (chunk_ok_cf_n s k (proj1 (Forall_forall _ _) HC k Hk)). lia.
Qed.

(* ================================================================ frames of the sub-calls *)
#[local] Ltac rhook ::= fail.
Lemma er_errb_map_cf : forall want x ns, rpost ns (errb_map_cf want x) (fun _ r => ER x (snd r)).
Proof. intros want x ns. unfold errb_map_cf, errb_retire. rwalk. Qed.

#[local] Ltac rhook ::= rsub er_errb_map_cf.
Lemma er_errb_append_cf : forall len x ns, rpost ns (errb_append_cf len x) (fun _ r => ER x (snd r)).
Proof. intros len x ns. unfold errb_append_cf, errb_set_size. rwalk. Qed.

#[local] Ltac rhook ::= rsub er_errb_append_cf.
Lemma er_errb_report_cf : forall c x ns, rpost ns (errb_report_cf c x) (fun _ r => ER x (snd r)).
Proof. intros c x ns. unfold errb_report_cf. rwalk. Qed.

#[local] Ltac rhook ::= fail.
Lemma cq_ensure_free_array : forall c need b x ns, rpost ns (ensure_free_array c need b x) (fun _ r => CQ x (snd r)).
Proof. intros c need b x ns. unfold ensure_free_array. rwalk. Qed.

Lemma cq_map_more_user : forall c need x ns, rpost ns (map_more_user c need x) (fun _ r => CQ x (snd r)).
Proof. intros c need x ns. unfold map_more_user. rwalk. Qed.

#[local] Ltac rhook ::= first [rsub er_errb_report_cf | rsub cq_map_more_user].
Lemma cq_map_more_user_cf : forall c need x ns, rpost ns (map_more_user_cf c need x) (fun _ r => CQ x (snd r)).
Proof. intros c need x ns. unfold map_more_user_cf, set_exh_cf. rwalk. Qed.

#[local] Ltac rhook ::= first [rsub cq_map_more_user | rsub cq_ensure_free_array].
Lemma cq_populate : forall c need x ns, rpost ns (populate c need x) (fun _ r => CQ x (snd r)).
Proof. intros c need x ns. unfold populate. rwalk. Qed.

#[local] Ltac rhook ::= first [rsub cq_populate | rsub cq_map_more_user_cf | rsub cq_ensure_free_array].
Lemma cq_populate_cf : forall c need x ns, rpost ns (populate_cf c need x) (fun _ r => CQ x (snd r)).
Proof. intros c need x ns. unfold populate_cf, clear_exh_cf. rwalk. Qed.

#[local] Ltac rhook ::= rsub cq_populate.
Lemma cq_get_from_allocator : forall c n x ns, rpost ns (get_from_allocator c n x) (fun _ r => CQ x (snd r)).
Proof. intros c n x ns. unfold get_from_allocator. rwalk. Qed.

#[local] Ltac rhook ::= rsub cq_populate_cf.
Lemma cq_get_from_allocator_cf : forall c n x ns,
  rpost ns (get_from_allocator_cf c n x) (fun _ r => CQ x (snd r)).
Proof. intros c n x ns. unfold get_from_allocator_cf. rwalk. Qed.

#[local] Ltac rhook ::= rsub cq_get_from_allocator.
Lemma cq_cache_alloc : forall c x ns, rpost ns (cache_alloc c x) (fun _ r => CQ x (snd r)).
Proof. intros c x ns. unfold cache_alloc, init_cache_if_needed, refill_if_empty. rwalk. Qed.

#[local] Ltac rhook ::= rsub cq_get_from_allocator_cf.
Lemma cq_cache_alloc_cf : forall c x ns, rpost ns (cache_alloc_cf c x) (fun _ r => CQ x (snd r)).
Proof. intros c x ns. unfold cache_alloc_cf, init_cache_if_needed, refill_if_empty_cf. rwalk. Qed.

#[local] Ltac rhook ::= fail.
Lemma cq_sec_alloc : forall n x ns, rpost ns (sec_alloc n x) (fun _ r => CQ x (snd r)).
Proof. intros n x ns. unfold sec_alloc. rwalk. Qed.

Lemma cq_depot_put : forall tr x ns, rpost ns (depot_put tr x) (fun _ r => CQ x (snd r)).
Proof. intros tr x ns. unfold depot_put. rwalk. Qed.

#[local] Ltac rhook ::= rsub cq_ensure_free_array.
Lemma cq_return_to_allocator : forall c offs x ns,
  rpost ns (return_to_allocator c offs x) (fun _ r => CQ x (snd r)).
Proof. intros c offs x ns. unfold return_to_allocator. rwalk. Qed.

#[local] Ltac rhook ::= rsub cq_return_to_allocator.
Lemma cq_cache_dealloc : forall c off x ns, rpost ns (cache_dealloc c off x) (fun _ r => CQ x (snd r)).
Proof. intros c off x ns. unfold cache_dealloc, init_cache_if_needed. rwalk. Qed.

#[local] Ltac rhook ::= fail.
Lemma cq_sec_dealloc : forall r x ns, rpost ns (sec_dealloc r x) (fun _ r' => CQ x (snd r')).
Proof. intros r x ns. unfold sec_dealloc. rwalk. Qed.

(* ================================================================ malloc_cf keeps the queues *)
Definition MQ (s x : astate) : Prop :=
  st_qthread x = st_qthread s /\ st_qglobal x = st_qglobal s /\
  (st_chunks x = st_chunks s \/ exists k, is_alloc k = true /\ st_chunks x = upd_chunk (st_chunks s) k).
Ltac mq_leaf := unfold MQ, CQ in *; rred in *; dands; split; [congruence|]; split; [congruence|];
  first [ left; congruence
        | right; match goal with |- exists k, _ /\ upd_chunk _ ?k0 = _ => exists k0 end;
          split; [reflexivity | f_equal; congruence] ].
#[local] Ltac rhook ::= first [rsub cq_cache_alloc_cf | rsub cq_sec_alloc | rsub cq_depot_put].
#[local] Ltac rleaf ::= mq_leaf.
Lemma malloc_cf_mq : forall n tr s ns, rpost ns (malloc_cf n tr s) (fun _ r => MQ s (snd r)).
Proof. intros n tr s ns. unfold malloc_cf. rwalk. Qed.
#[local] Ltac rleaf ::= fr_leaf.
#[local] Ltac rhook ::= fail.

Lemma malloc_cf_room_inv : forall U s n tr ns, Wf_cf U s -> room_inv_cf s ->
  rpost ns (malloc_cf n tr s) (fun _ r => room_inv_cf (snd r)).
Proof.
  intros U s n tr ns W (T1 & T2 & T3).
  assert (Hpos : Forall (fun x => 0 <= ck_n x) (st_chunks s)).
  { eapply Forall_impl; [|exact (wfc_chunks _ _ _ _ _ W)]. cbv beta. intros x Hx. pose proof (chunk_ok_cf_n s x Hx). lia. }
  eapply rpost_mono; [|apply malloc_cf_mq]. cbv beta. intros _ [p x] (E1 & E2 & E3). cbn [snd] in *.
  unfold room_inv_cf, qtight, quar_n, queued_n, q_items, all_batches in *. rewrite E1, E2.
  split; [exact T1|]. split; [exact T2|].
  destruct E3 as [E3|(k & Hk & E3)]; rewrite E3; [exact T3|].
  pose proof (quar_nl_upd _ k Hpos) as H.
  replace (if is_alloc k then 0 else ck_n k) with 0 in H by (rewrite Hk; reflexivity). lia.
Qed.

Lemma malloc_cf_fifo : forall s n tr ns,
  rpost ns (malloc_cf n tr s) (fun _ r => q_fifo (snd r) = q_fifo s /\ all_batches (snd r) = all_batches s).
Proof.
  intros s n tr ns. eapply rpost_mono; [|apply malloc_cf_mq]. cbv beta. intros _ [p x] (E1 & E2 & _).
  cbn [snd] in *.
  unfold q_fifo, all_batches. rewrite E1, E2. split; reflexivity.
Qed.

(* ================================================================ the recycle *)
Lemma recycle_chunk_n : forall k x ns, NoDup (map ck_beg (st_chunks x)) -> ck_state k = CQuarantined ->
  rpost ns (recycle_chunk k x) (fun _ r => NoDup (map ck_beg (st_chunks (snd r))) /\
    quar_n (snd r) + ck_n k = quar_n x /\ st_qthread (snd r) = st_qthread x /\ st_qglobal (snd r) = st_qglobal x).
Proof.
  intros k x ns Hnd Hst. unfold recycle_chunk. rgo.
  destruct (mem_chunk k (st_chunks x)) eqn:Hm; rgo.
  apply mem_chunk_spec in Hm.
  pose proof (quar_nl_del _ _ Hnd Hm Hst) as Hq. pose proof (nodup_del_chunk (st_chunks x) (ck_beg k) Hnd) as Hn.
  revert Hq Hn. destruct (ck_beg k) as [|off|r off|cid pos]; intros Hq Hn; rgo.
  - eapply rpost_mono; [|apply cq_cache_dealloc]. cbv beta. intros _ [u y] Hy. unfold CQ in Hy. cbn [snd] in *.
    rred in Hy. destruct Hy as (E1 & E2 & E3). unfold quar_n. rewrite E1, E2, E3.
    split; [exact Hn|]. split; [exact Hq|]. split; reflexivity.
  - eapply rpost_mono; [|apply cq_sec_dealloc]. cbv beta. intros _ [u y] Hy. unfold CQ in Hy. cbn [snd] in *.
    rred in Hy. destruct Hy as (E1 & E2 & E3). unfold quar_n. rewrite E1, E2, E3.
    split; [exact Hn|]. split; [exact Hq|]. split; reflexivity.
Qed.

Lemma recycle_items_n : forall fuel items x ns, NoDup (map ck_beg (st_chunks x)) ->
  Forall (fun k => ck_state k = CQuarantined) items ->
  rpost ns (recycle_items fuel items x) (fun _ r => NoDup (map ck_beg (st_chunks (snd r))) /\
    quar_n (snd r) + items_n items = quar_n x /\ st_qthread (snd r) = st_qthread x /\
    st_qglobal (snd r) = st_qglobal x).
Proof.
  induction fuel as [|f IH]; intros items x ns Hnd Hst; destruct items as [|k t]; cbn [recycle_items]; rgo.
  - rewrite items_n_nil. split; [exact Hnd|]. split; [lia|]. split; reflexivity.
  - rewrite items_n_nil. split; [exact Hnd|]. split; [lia|]. split; reflexivity.
  - apply Forall_cons_iff in Hst as [Hk Ht].
    eapply rpost_mono; [|apply recycle_chunk_n; assumption]. cbv beta. intros b [u y] (N1 & E1 & E2 & E3).
    cbn [snd] in *. rgo.
    eapply rpost_mono; [|apply IH; assumption]. cbv beta. intros b' [u' y'] (N2 & F1 & F2 & F3). cbn [snd] in *.
    rewrite items_n_cons. split; [exact N2|]. split; [lia|]. split; congruence.
Qed.

Lemma do_recycle_n : forall fuel bs x ns, NoDup (map ck_beg (st_chunks x)) ->
  Forall (fun k => ck_state k = CQuarantined) (flat_map b_items bs) ->
  rpost ns (do_recycle fuel bs x) (fun _ r => NoDup (map ck_beg (st_chunks (snd r))) /\
    quar_n (snd r) + items_n (flat_map b_items bs) = quar_n x /\ st_qthread (snd r) = st_qthread x /\
    st_qglobal (snd r) = st_qglobal x).
Proof.
  induction fuel as [|f IH]; intros bs x ns Hnd Hst; destruct bs as [|b t]; cbn [do_recycle]; rgo.
  - cbn [flat_map]. rewrite items_n_nil. split; [exact Hnd|]. split; [lia|]. split; reflexivity.
  - cbn [flat_map]. rewrite items_n_nil. split; [exact Hnd|]. split; [lia|]. split; reflexivity.
  - cbn [flat_map] in Hst. apply Forall_app in Hst as [Hb Ht].
    eapply rpost_mono; [|apply recycle_items_n; assumption]. cbv beta. intros b1 [u y] (N1 & E1 & E2 & E3).
    cbn [snd] in *. rgo.
    eapply rpost_mono; [|apply cq_cache_dealloc]. cbv beta. intros b2 [u2 y2] Hy. unfold CQ in Hy.
    cbn [snd] in *. destruct Hy as (C1 & C2 & C3). rgo.
    eapply rpost_mono; [|apply IH; [rewrite C1; exact N1 | exact Ht]]. cbv beta.
    intros b3 [u3 y3] (N3 & F1 & F2 & F3). cbn [snd] in *.
    cbn [flat_map]. rewrite items_n_app. unfold quar_n in *. rewrite C1 in F1.
    split; [exact N3|]. split; [lia|]. split; congruence.
Qed.

Lemma recycle_chunk_q : forall k x ns,
  rpost ns (recycle_chunk k x) (fun _ r => st_qthread (snd r) = st_qthread x /\ st_qglobal (snd r) = st_qglobal x).
Proof.
  intros k x ns. unfold recycle_chunk. rgo.
  destruct (mem_chunk k (st_chunks x)); rgo.
  destruct (ck_beg k); rgo.
  - eapply rpost_mono; [|apply cq_cache_dealloc]. cbv beta. intros _ [u y] Hy. unfold CQ in Hy. cbn [snd] in *.
    rred in Hy. tauto.
  - eapply rpost_mono; [|apply cq_sec_dealloc]. cbv beta. intros _ [u y] Hy. unfold CQ in Hy. cbn [snd] in *.
    rred in Hy. tauto.
Qed.

(* the recycle side of free_cf's size test: the chunk leaves the list, both queues unchanged *)
Lemma recycle_chunk_cq : forall k x ns,
  rpost ns (recycle_chunk k x) (fun _ r => st_chunks (snd r) = del_chunk (st_chunks x) (ck_beg k) /\
    st_qthread (snd r) = st_qthread x /\ st_qglobal (snd r) = st_qglobal x).
Proof.
  intros k x ns. unfold recycle_chunk. rgo.
  destruct (mem_chunk k (st_chunks x)); rgo.
  destruct (ck_beg k); rgo.
  - eapply rpost_mono; [|apply cq_cache_dealloc]. cbv beta. intros _ [u y] Hy. unfold CQ in Hy. cbn [snd] in *.
    rred in Hy. tauto.
  - eapply rpost_mono; [|apply cq_sec_dealloc]. cbv beta. intros _ [u y] Hy. unfold CQ in Hy. cbn [snd] in *.
    rred in Hy. tauto.
Qed.

Lemma recycle_items_q : forall fuel items x ns,
  rpost ns (recycle_items fuel items x) (fun _ r => st_qthread (snd r) = st_qthread x /\ st_qglobal (snd r) = st_qglobal x).
Proof.
  induction fuel as [|f IH]; intros items x ns; destruct items as [|k t]; cbn [recycle_items]; rgo;
    try (split; reflexivity).
  eapply rpost_mono; [|apply recycle_chunk_q]. cbv beta. intros b [u y] (E1 & E2). cbn [snd] in *. rgo.
  eapply rpost_mono; [|apply IH]. cbv beta. intros b' [u' y'] (F1 & F2). cbn [snd] in *. split; congruence.
Qed.

Lemma do_recycle_q : forall fuel bs x ns,
  rpost ns (do_recycle fuel bs x) (fun _ r => st_qthread (snd r) = st_qthread x /\ st_qglobal (snd r) = st_qglobal x).
Proof.
  induction fuel as [|f IH]; intros bs x ns; destruct bs as [|b t]; cbn [do_recycle]; rgo;
    try (split; reflexivity).
  eapply rpost_mono; [|apply recycle_items_q]. cbv beta. intros b1 [u y] (E1 & E2). cbn [snd] in *. rgo.
  eapply rpost_mono; [|apply cq_cache_dealloc]. cbv beta. intros b2 [u2 y2] Hy. unfold CQ in Hy.
  cbn [snd] in *. destruct Hy as (C1 & C2 & C3). rgo.
  eapply rpost_mono; [|apply IH]. cbv beta. intros b3 [u3 y3] (F1 & F2). cbn [snd] in *. split; congruence.
Qed.

(* ================================================================ enqueue and the drain *)
Lemma enqueue_post : forall k x ns, rpost ns (enqueue k x) (fun _ r =>
  st_chunks (snd r) = st_chunks x /\ st_qglobal (snd r) = st_qglobal x /\
  exists nb, st_qthread (snd r) = qc_push (st_qthread x) k nb /\ (nb = None -> need_new_batch (st_qthread x) = false)).
Proof.
  intros k x ns. unfold enqueue. rgo.
  destruct (need_new_batch (st_qthread x)) eqn:Hn; rgo.
  - eapply rpost_mono; [|apply cq_cache_alloc]. cbv beta. intros b [ob y] Hy. unfold CQ in Hy. cbn [snd] in *.
    destruct Hy as (E1 & E2 & E3). rgo.
    destruct ob as [off|]; rgo.
    split; [exact E1|]. split; [exact E3|]. exists (Some off).
    split; [rewrite E2; reflexivity | intros Hc; discriminate Hc].
  - split; [reflexivity|]. split; [reflexivity|]. exists None. split; [reflexivity | intros _; reflexivity].
Qed.

(* what free_cf's drain (maybe_drain_cf, YG00cf.v) needs of its entry state to leave qtight. Its fuels are
   the lists' own lengths, so no length bound is needed. *)
Definition DRAIN_PRE (x : astate) : Prop :=
  qc_bytes (st_qglobal x) <= kQuarantineMax /\
  qc_bytes (st_qthread x) = sum_bytes (qc_list (st_qthread x)) /\
  qc_bytes (st_qglobal x) = sum_bytes (qc_list (st_qglobal x)) /\
  Forall (fun k => ck_state k = CQuarantined) (q_items x) /\
  NoDup (map ck_beg (st_chunks x)) /\ quar_n x <= queued_n x.

(* maybe_drain_cf split as YG03dcf.v's maybe_drain_cf_eq: the merge choice, then the pop and the recycle. The
   merge keeps the items (mres_cf) and extracts empty batches, which the recycle frees with the popped ones. *)
Lemma maybe_drain_tight : forall x ns, DRAIN_PRE x -> rpost ns (maybe_drain_cf x) (fun _ r => qtight (snd r)).
Proof.
  intros x ns (HG & HBt & HBg & HQ & HND & HQN). rewrite YG03dcf.maybe_drain_cf_eq. rgo.
  dle Ht; rgo.
  { unfold qtight. split; [exact Ht|]. split; [exact HG | exact HQN]. }
  dle Hg; rgo.
  { unfold qtight, quar_n, queued_n, q_items, all_batches in *. rred.
    rewrite !flat_map_app, !items_n_app in *. cbn [flat_map app] in *. rewrite items_n_nil.
    split; [unfold kQuarantineCacheMax; lia|]. split; [exact Hg|]. lia. }
  match goal with |- context [YG03dcf.merge_choice_cf ?g] =>
    destruct (YG03dcf.merge_choice_cf g) as [gm ex] eqn:EMR end.
  pose proof (YG03dcf.merge_choice_mres_cf _ _ _ EMR) as (M1 & _ & M3 & M4 & _). cbn [qc_list qc_bytes] in M1, M4.
  unfold YG03dcf.drain_tail_cf.
  match goal with |- context [pop_batches ?f ?q ?a] => destruct (pop_batches f q a) as [g' popped] eqn:Hpop end. rgo.
  pose proof (pop_batches_spec _ _ _ _ _ Hpop) as (P & Epop & El & Eb). cbn [rev app] in Epop.
  subst popped.
  pose proof (pop_batches_stop _ _ _ _ _ Hpop (Nat.lt_succ_diag_r _)) as Hstop.
  assert (Hn : items_n (flat_map b_items (qc_list (st_qglobal x))) + items_n (flat_map b_items (qc_list (st_qthread x)))
    = items_n (flat_map b_items P) + items_n (flat_map b_items (qc_list g'))).
  { rewrite <- !items_n_app, <- !flat_map_app, <- El, M1. reflexivity. }
  eapply rpost_mono; [|apply do_recycle_n].
  - cbv beta. intros _ [u w] (_ & Eq & Et & Eg). cbn [snd] in *. rred in Et. rred in Eg.
    rewrite flat_map_app, (YG03dcf.flat_items_empty_cf ex M3) in Eq. cbn [app] in Eq.
    unfold qtight, quar_n, queued_n, q_items, all_batches in *. rred in Eq. rewrite Et, Eg. rred.
    rewrite flat_map_app, items_n_app in HQN. cbn [app].
    split; [unfold kQuarantineCacheMax; lia|]. split; [|lia].
    destruct Hstop as [Hs|Hs]; [unfold kQuarantineMin, kQuarantineMax in *; lia|].
    rewrite Hs, app_nil_r in El. rewrite Eb, <- El, M4, sum_bytes_app. unfold kQuarantineMax. lia.
  - rred. exact HND.
  - rewrite flat_map_app, (YG03dcf.flat_items_empty_cf ex M3). cbn [app].
    unfold q_items, all_batches in HQ. rewrite flat_map_app in HQ. apply Forall_app in HQ as [HQt HQg].
    assert (HA : Forall (fun k => ck_state k = CQuarantined) (flat_map b_items (qc_list gm))).
    { rewrite M1, flat_map_app. apply Forall_app. split; assumption. }
    rewrite El, flat_map_app in HA. apply Forall_app in HA as [HA _]. exact HA.
Qed.

Lemma maybe_drain_fifo : forall x ns,
  rpost ns (maybe_drain_cf x) (fun _ r => exists P, q_fifo x = flat_map b_items P ++ q_fifo (snd r)).
Proof.
  intros x ns. rewrite YG03dcf.maybe_drain_cf_eq. rgo.
  dle Ht; rgo.
  { exists []. reflexivity. }
  dle Hg; rgo.
  { exists []. unfold q_fifo. rred. rewrite app_nil_r. reflexivity. }
  match goal with |- context [YG03dcf.merge_choice_cf ?g] =>
    destruct (YG03dcf.merge_choice_cf g) as [gm ex] eqn:EMR end.
  pose proof (YG03dcf.merge_choice_mres_cf _ _ _ EMR) as (M1 & _). cbn [qc_list] in M1.
  unfold YG03dcf.drain_tail_cf.
  match goal with |- context [pop_batches ?f ?q ?a] => destruct (pop_batches f q a) as [g' popped] eqn:Hpop end. rgo.
  pose proof (pop_batches_spec _ _ _ _ _ Hpop) as (P & Epop & El & _). cbn [rev app] in Epop.
  subst popped.
  eapply rpost_mono; [|apply do_recycle_q]. cbv beta. intros _ [u w] (Et & Eg). cbn [snd] in *.
  rred in Et. rred in Eg.
  exists P. unfold q_fifo. rewrite Et, Eg. rred. rewrite app_nil_r, <- M1, El, flat_map_app. reflexivity.
Qed.

(* ================================================================ free_cf: one walk, any drain fact *)
Definition FREEG (R : astate -> astate -> Prop) (s : astate) (p : sptr) (y : astate) : Prop :=
  (freed_cf s p = [] /\ CQ s y) \/
  (exists k nb x5, find_user (st_chunks s) p = Some k /\ ck_state k = CAllocated /\
     freed_cf s p = [mkChunk (ck_beg k) (ck_req k) CQuarantined] /\
     st_chunks x5 = upd_chunk (st_chunks s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) /\
     st_qglobal x5 = st_qglobal s /\
     st_qthread x5 = qc_push (st_qthread s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) nb /\
     (nb = None -> need_new_batch (st_qthread s) = false) /\ R x5 y) \/
  (* the recycle side: a chunk above kQuarantineMax leaves at once, the queues as they were *)
  (exists k x5, find_user (st_chunks s) p = Some k /\ ck_state k = CAllocated /\ kQuarantineMax < ck_n k /\
     freed_cf s p = [] /\
     st_chunks x5 = del_chunk (upd_chunk (st_chunks s) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) (ck_beg k) /\
     st_qglobal x5 = st_qglobal s /\ st_qthread x5 = st_qthread s /\ R x5 y).

Lemma free_cf_gen : forall (R : astate -> astate -> Prop) p tr s ns,
  (forall x ns', rpost ns' (maybe_drain_cf x) (fun _ r => R x (snd r))) ->
  rpost ns (free_cf p tr s) (fun _ r => FREEG R s p (snd r)).
Proof.
  intros R p tr s ns HR. unfold free_cf. rgo.
  destruct (st_internal_inited s); rgo; destruct p as [|off|r off|cid pos]; rgo.
  all: first [ solve [ unfold FREEG; left; split; [reflexivity | unfold CQ; rred; repeat split; reflexivity] ]
             | idtac ].
  all: match goal with |- context [find_user ?l ?q] => destruct (find_user l q) as [k|] eqn:Hf end; rgo.
  all: destruct (ck_state k) eqn:Hst; rgo.
  all: eapply rpost_mono; [|apply cq_depot_put]; cbv beta; intros b [u x3] H3; cbn [snd] in *; rgo.
  all: dle QSZ; [
    eapply rpost_mono; [|apply enqueue_post]; cbv beta; intros b' [u' x5] (E1 & E2 & nb & E3 & E4);
    cbn [snd] in *; rgo;
    eapply rpost_mono; [|apply HR]; cbv beta; intros b'' [u'' y] Hy; cbn [snd] in *;
    unfold CQ in H3; rred in H3; destruct H3 as (C1 & C2 & C3); rred in E1; rred in E2; rred in E3; rred in E4;
    unfold FREEG; right; left; exists k, nb, x5; split; [exact Hf|]; split; [exact Hst|];
    split; [cbn [freed_cf]; rewrite Hf, (proj2 (Z.leb_le (ck_n k) kQuarantineMax) QSZ); reflexivity|];
    split; [congruence|]; split; [congruence|]; split; [congruence|];
    split; [intros Hnb; specialize (E4 Hnb); congruence | exact Hy]
  | eapply rpost_mono; [|apply recycle_chunk_cq]; cbv beta; intros b' [u' x5] (E1 & E2 & E3);
    cbn [snd] in *; rgo;
    eapply rpost_mono; [|apply HR]; cbv beta; intros b'' [u'' y] Hy; cbn [snd] in *;
    unfold CQ in H3; rred in H3; destruct H3 as (C1 & C2 & C3); rred in E1; rred in E2; rred in E3;
    cbn [ck_beg] in E1;
    unfold FREEG; right; right; exists k, x5; split; [exact Hf|]; split; [exact Hst|]; split; [exact QSZ|];
    split; [cbn [freed_cf]; rewrite Hf, (proj2 (Z.leb_gt (ck_n k) kQuarantineMax) QSZ); reflexivity|];
    split; [congruence|]; split; [congruence|]; split; [congruence | exact Hy] ].
Qed.

Lemma free_cf_room_inv : forall U s p tr ns, Wf_cf U s -> room_inv_cf s ->
  rpost ns (free_cf p tr s) (fun _ r => room_inv_cf (snd r)).
Proof.
  intros U s p tr ns W T. pose proof T as (T1 & T2 & T3).
  pose proof (wfc_quarantine _ _ _ _ _ W) as Q. pose proof (wfc_chunks _ _ _ _ _ W) as HC.
  pose proof (wfc_chunks_nodup _ _ _ _ _ W) as HND.
  assert (Hpos : Forall (fun x => 0 <= ck_n x) (st_chunks s)).
  { eapply Forall_impl; [|exact HC]. cbv beta. intros x Hx. pose proof (chunk_ok_cf_n s x Hx). lia. }
  eapply rpost_mono; [|apply (free_cf_gen (fun x y => DRAIN_PRE x -> qtight y)); intros x ns';
    apply rpost_impl; intros HD; apply maybe_drain_tight; exact HD].
  cbv beta. intros _ [u y] [(_ & E1 & E2 & E3)|[(k & nb & x5 & Hf & Hst & _ & E1 & E2 & E3 & E4 & HR)|
    (k & x5 & Hf & Hst & Hbig & _ & E1 & E2 & E3 & HR)]];
    cbn [snd] in *.
  - unfold room_inv_cf, qtight, quar_n, queued_n, q_items, all_batches in *. rewrite E1, E2, E3. exact T.
  - apply HR. clear HR. destruct (find_user_spec _ _ _ Hf) as [Hk _].
    unfold DRAIN_PRE. rewrite E1, E2, E3.
    split; [exact T2|]. split; [apply qc_push_bytes; [exact E4 | exact (wq_bytes_t _ Q)]|].
    split; [exact (wq_bytes_g _ Q)|].
    split.
    { unfold q_items, all_batches. rewrite E3, E2, flat_map_app, qc_push_items by exact E4.
      pose proof (wq_items _ Q) as HQ. unfold q_items, all_batches in HQ. rewrite flat_map_app in HQ.
      apply Forall_app in HQ as [HQt HQg].
      apply Forall_app. split; [apply Forall_app; split; [|constructor; [reflexivity | constructor]]|].
      - eapply Forall_impl; [|exact HQt]. cbv beta. intros x [_ Hx]. exact Hx.
      - eapply Forall_impl; [|exact HQg]. cbv beta. intros x [_ Hx]. exact Hx. }
    split.
    { rewrite map_beg_upd; [exact HND|]. exact (in_map ck_beg _ _ Hk). }
    unfold quar_n, queued_n, q_items, all_batches in *. rewrite E1, E2, E3, flat_map_app, qc_push_items by exact E4.
    rewrite flat_map_app, items_n_app in T3. rewrite !items_n_app, items_n_cons, items_n_nil.
    pose proof (quar_nl_upd (st_chunks s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) Hpos) as Hu.
    cbn [is_alloc ck_state] in Hu. unfold ck_n in *. cbn [ck_req] in *. lia.
  - (* the recycle side: the chunk was allocated and leaves the list; the queues are as they were *)
    apply HR. clear HR. destruct (find_user_spec _ _ _ Hf) as [Hk _].
    destruct (In_split_beg _ _ Hk HND) as (l1 & l2 & EL & N1 & N2).
    assert (EC : st_chunks x5 = l1 ++ l2).
    { rewrite E1, EL, upd_chunk_present by (reflexivity || exact N1).
      exact (del_chunk_present l1 (mkChunk (ck_beg k) (ck_req k) CQuarantined) l2 N1). }
    unfold DRAIN_PRE. rewrite E2, E3.
    split; [exact T2|]. split; [exact (wq_bytes_t _ Q)|]. split; [exact (wq_bytes_g _ Q)|].
    split.
    { unfold q_items, all_batches. rewrite E2, E3. pose proof (wq_items _ Q) as HQ. unfold q_items, all_batches in HQ.
      eapply Forall_impl; [|exact HQ]. cbv beta. intros x [_ Hx]. exact Hx. }
    split.
    { rewrite EC. rewrite EL, map_app in HND. cbn [map] in HND. rewrite map_app. exact (NoDup_remove_1 _ _ _ HND). }
    unfold quar_n, queued_n, q_items, all_batches in *. rewrite EC, E2, E3.
    rewrite EL, YG03cf.quar_nl_split_cf in T3.
    replace (is_alloc k) with true in T3 by (unfold is_alloc; rewrite Hst; reflexivity). lia.
Qed.

Lemma free_cf_fifo : forall p tr s ns,
  rpost ns (free_cf p tr s) (fun _ r => exists P, q_fifo s ++ freed_cf s p = flat_map b_items P ++ q_fifo (snd r)).
Proof.
  intros p tr s ns.
  eapply rpost_mono; [|apply (free_cf_gen (fun x y => exists P, q_fifo x = flat_map b_items P ++ q_fifo y));
    intros x ns'; apply maybe_drain_fifo].
  cbv beta. intros _ [u y] [(Hfr & E1 & E2 & E3)|[(k & nb & x5 & _ & _ & Hfr & _ & E2 & E3 & E4 & (P & HP))|
    (k & x5 & _ & _ & _ & Hfr & _ & E2 & E3 & (P & HP))]];
    cbn [snd] in *.
  - exists []. rewrite Hfr, app_nil_r. unfold q_fifo. rewrite E2, E3. reflexivity.
  - exists P. rewrite Hfr, <- HP. unfold q_fifo. rewrite E2, E3, !flat_map_app, qc_push_items by exact E4.
    rewrite app_assoc. reflexivity.
  - exists P. rewrite Hfr, app_nil_r, <- HP. unfold q_fifo. rewrite E2, E3. reflexivity.
Qed.

Lemma freed_cf_pos : forall U s p, Wf_cf U s -> Forall (fun k => 1 <= ck_n k) (freed_cf s p).
Proof.
  intros U s p W. apply Forall_forall. intros x Hx. unfold freed_cf in Hx.
  destruct p as [|off|r off|cid pos]; [destruct Hx| | |];
    (match type of Hx with context [find_user ?l ?q] => destruct (find_user l q) as [k|] eqn:Hf end;
     [destruct (ck_n k <=? kQuarantineMax); [|destruct Hx]; destruct Hx as [<-|[]]; destruct (find_user_spec _ _ _ Hf) as [Hk _];
      exact (chunk_ok_cf_n s k (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk))
     | destruct Hx]).
Qed.

(* the requests free_cf appends to the history are non-negative, so map_ck_n_acct_cf applies to it *)
Lemma freed_cf_req_cf : forall U s p, Wf_cf U s -> Forall (fun k => 0 <= ck_req k) (freed_cf s p).
Proof.
  intros U s p W. apply Forall_forall. intros x Hx. unfold freed_cf in Hx.
  destruct p as [|off|r off|cid pos]; [destruct Hx| | |];
    (match type of Hx with context [find_user ?l ?q] => destruct (find_user l q) as [k|] eqn:Hf end;
     [destruct (ck_n k <=? kQuarantineMax); [|destruct Hx]; destruct Hx as [<-|[]]; destruct (find_user_spec _ _ _ Hf) as [Hk _];
      exact (chunk_ok_cf_req s k (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk))
     | destruct Hx]).
Qed.

(* ================================================================ fact 3: the NULL arm *)
Definition ARM (x : astate) (c need : Z) : Prop := kFreeArrayOffset < rg_alloc_user (reg x c) + need * class_size c.
Definition RG (c : Z) (x y : astate) : Prop :=
  st_cache y = st_cache x /\ length (st_regions y) = length (st_regions x) /\
  rg_alloc_user (reg y c) = rg_alloc_user (reg x c) /\ rg_free (reg y c) = rg_free (reg x c).

Lemma efa_np : forall c need x ns, 0 <= c -> (Z.to_nat c < length (st_regions x))%nat ->
  rpost ns (ensure_free_array c need false x) (fun b r => RG c x (snd r) /\ (fst r = false -> b = false)).
Proof.
  intros c need x ns Hc Hl. unfold ensure_free_array. rgo.
  dif; rgo.
  { split; [unfold RG; repeat split; reflexivity | intros; discriminate]. }
  dif; rgo. intros z Hz. destruct (z =? 1) eqn:Ez; rgo.
  - split; [|intros; discriminate]. unfold RG, reg. rred. rewrite zupd_length, znth_zupd_same by assumption. rred.
    repeat split; reflexivity.
  - dif; rgo.
    + split; [|intros; reflexivity]. unfold RG, reg. rred. rewrite zupd_length, znth_zupd_same by assumption. rred.
      repeat split; reflexivity.
    + split; [unfold RG; repeat split; reflexivity | intros; reflexivity].
Qed.

Lemma mmu_np : forall c need x ns, 0 <= c -> (Z.to_nat c < length (st_regions x))%nat ->
  rpost ns (map_more_user c need x) (fun b r => RG c x (snd r) /\ (b = true -> fst r = false -> False) /\
    (fst r = true -> rg_alloc_user (reg x c) + need * class_size c <= rg_mapped_user (reg (snd r) c))).
Proof.
  intros c need x ns Hc Hl. unfold map_more_user. rgo.
  dlt Hlt; rgo.
  - dif; rgo. intros z Hz. destruct (z =? 1) eqn:Ez; rgo.
    + unfold RG, reg. rred. rewrite zupd_length, znth_zupd_same by assumption. rred.
      split; [repeat split; reflexivity|]. split; [intros; discriminate|]. intros _.
      pose proof (round_up_ge (rg_alloc_user (znth region0 c (st_regions x)) + need * class_size c -
        rg_mapped_user (znth region0 c (st_regions x))) kUserMapSize ltac:(unfold kUserMapSize; lia)) as [[Hr _] _].
      lia.
    + dif; rgo.
      * unfold RG, reg. rred. rewrite zupd_length, znth_zupd_same by assumption. rred.
        split; [repeat split; reflexivity|]. split; intros; discriminate.
      * split; [unfold RG; repeat split; reflexivity|]. split; intros; discriminate.
  - split; [unfold RG; repeat split; reflexivity|]. split; [intros; discriminate|]. intros _. unfold reg. lia.
Qed.

Lemma mmu_cf_np : forall c need x ns, c <> kBatchClass -> 0 <= c -> (Z.to_nat c < length (st_regions x))%nat ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 ->
  rpost ns (map_more_user_cf c need x) (fun b r => RG c x (snd r) /\ (b = true -> fst r = false -> ARM x c need) /\
    (fst r = true -> rg_alloc_user (reg x c) + need * class_size c <= rg_mapped_user (reg (snd r) c))).
Proof.
  intros c need x ns H24 Hc Hl Hal. unfold map_more_user_cf, set_exh_cf.
  destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|].
  rgo. unfold reg in Hal.
  dlt Hlt; rgo.
  - dle Hfit; rgo.
    + intros z Hz. destruct (z =? 1) eqn:Ez; rgo.
      * unfold RG, reg. rred. rewrite zupd_length, znth_zupd_same by assumption. rred.
        split; [repeat split; reflexivity|]. split; [intros; discriminate|]. intros _.
        pose proof (round_up_ge (rg_alloc_user (znth region0 c (st_regions x)) + need * class_size c -
          rg_mapped_user (znth region0 c (st_regions x))) kUserMapSize ltac:(unfold kUserMapSize; lia)) as [[Hr _] _].
        lia.
      * dif; rgo.
        -- unfold RG, reg. rred. rewrite zupd_length, znth_zupd_same by assumption. rred.
           split; [repeat split; reflexivity|]. split; intros; discriminate.
        -- split; [unfold RG; repeat split; reflexivity|]. split; intros; discriminate.
    + eapply rpost_mono; [|apply er_errb_report_cf]. cbv beta. intros b [u y] Hy. unfold ER, CQ in Hy.
      cbn [snd] in *. destruct Hy as (Ry & Cy & _). rgo.
      unfold RG, ARM, reg. rred. rewrite zupd_length, Ry, znth_zupd_same by assumption. rred.
      split; [split; [exact Cy|]; repeat split; reflexivity|].
      split; [intros _ _; eapply arm_of_full; eassumption | intros; discriminate].
  - split; [unfold RG; repeat split; reflexivity|]. split; [intros; discriminate|]. intros _. unfold reg. lia.
Qed.

Definition POP (c need : Z) (x : astate) (b : bool) (r : bool * astate) : Prop :=
  st_cache (snd r) = st_cache x /\ length (st_regions (snd r)) = length (st_regions x) /\
  (b = true -> fst r = false -> ARM x c need) /\
  (fst r = true -> fa_len (rg_free (reg x c)) + need <= fa_len (rg_free (reg (snd r) c))).

Ltac pop_ok_leaf need y c :=
  unfold POP, RG, reg in *; rred; dands; rewrite !zupd_length;
  repeat rewrite znth_zupd_same by (rewrite ?zupd_length; lia); rred; cbn [fa_len];
  split; [congruence|]; split; [congruence|]; split; [intros; discriminate|]; intros _;
  let Hnc := fresh "Hnc" in
  assert (Hnc : need <= (rg_mapped_user (znth region0 c (st_regions y)) -
    rg_alloc_user (znth region0 c (st_regions y))) / class_size c)
    by (apply Z.div_le_lower_bound; [lia | nia]);
  repeat match goal with H : rg_free _ = rg_free _ |- _ => rewrite H end;
  lia.

Lemma populate_cf_np : forall c need x ns, 1 <= c <= 31 -> (Z.to_nat c < length (st_regions x))%nat ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 -> rpost ns (populate_cf c need x) (POP c need x).
Proof.
  intros c need x ns Hc Hl Hal. pose proof (class_ok c Hc) as (Ks & _).
  unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E|Hne].
  - unfold populate. rgo.
    eapply rpost_mono; [|apply mmu_np; [lia | exact Hl]]. cbv beta. intros b [ok y] (HR & Hf & Ht).
    cbn [fst snd] in *. rgo. destruct ok; rgo.
    + pose proof HR as (_ & HRl & _).
      eapply rpost_mono; [|apply efa_np; [lia | rewrite HRl; exact Hl]]. cbv beta. intros b2 [ok2 y2] (HR2 & Hf2).
      cbn [fst snd] in *. rgo. destruct ok2; rgo.
      * specialize (Ht eq_refl). pop_ok_leaf need y c.
      * unfold POP, RG in *. cbn [fst snd] in *. dands. split; [congruence|]. split; [congruence|].
        split; [intros Hb; rewrite (Hf2 eq_refl) in Hb; discriminate | intros; discriminate].
    + unfold POP, RG in *. cbn [fst snd] in *. dands. split; [congruence|]. split; [congruence|].
      split; [intros Hb _; exfalso; exact (Hf Hb eq_refl) | intros; discriminate].
  - rgo. eapply rpost_mono; [|apply mmu_cf_np; [exact Hne | lia | exact Hl | exact Hal]]. cbv beta.
    intros b [ok y] (HR & Hf & Ht). cbn [fst snd] in *. rgo. destruct ok; rgo.
    + pose proof HR as (_ & HRl & _).
      eapply rpost_mono; [|apply efa_np; [lia | rewrite HRl; exact Hl]]. cbv beta. intros b2 [ok2 y2] (HR2 & Hf2).
      cbn [fst snd] in *. unfold clear_exh_cf. rgo. destruct ok2; rgo.
      * specialize (Ht eq_refl). pop_ok_leaf need y c.
      * unfold POP, RG in *. cbn [fst snd] in *. dands. split; [congruence|]. split; [congruence|].
        split; [intros Hb; rewrite (Hf2 eq_refl) in Hb; discriminate | intros; discriminate].
    + unfold POP, RG in *. cbn [fst snd] in *. dands. split; [congruence|]. split; [congruence|].
      split; [intros Hb _; exact (Hf Hb eq_refl) | intros; discriminate].
Qed.

Lemma gfa_cf_np : forall c n0 x ns, 1 <= c <= 31 -> 1 <= n0 -> (Z.to_nat c < length (st_regions x))%nat ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 ->
  rpost ns (get_from_allocator_cf c n0 x) (fun b r => st_cache (snd r) = st_cache x /\
    (b = true -> fst r = None -> ARM x c (n0 - fa_len (rg_free (reg x c)))) /\
    (forall tops, fst r = Some tops -> tops <> [])).
Proof.
  intros c n0 x ns Hc Hn0 Hl Hal. unfold get_from_allocator_cf. rgo.
  dlt Hlt.
  - eapply rpost_mono; [|apply populate_cf_np; assumption]. cbv beta. intros b [ok y] (Hcy & Hly & Hf & Ht).
    cbn [fst snd] in *. rgo. destruct ok; rgo.
    + dlt Hlt2; rgo.
      * split; [exact Hcy|]. split; [|intros ? H; discriminate]. intros _ _. exfalso.
        specialize (Ht eq_refl). unfold reg in Ht. lia.
      * match goal with |- context [fa_pop_n ?f ?sz ?n ?l ?a] =>
          destruct (fa_pop_n f sz n l a) as [[tops rest]|] eqn:Hp end; rgo.
        split; [exact Hcy|]. split; [intros _ H; discriminate|]. intros tops' H. injection H as <-.
        exact (fa_pop_n_nonempty _ _ _ _ _ _ _ Hp (or_intror Hn0)).
    + split; [exact Hcy|]. split; [|intros ? H; discriminate]. intros Hb _. exact (Hf Hb eq_refl).
  - rgo. dlt Hlt2; rgo.
    + split; [reflexivity|]. split; [|intros ? H; discriminate]. intros _ _. lia.
    + match goal with |- context [fa_pop_n ?f ?sz ?n ?l ?a] =>
        destruct (fa_pop_n f sz n l a) as [[tops rest]|] eqn:Hp end; rgo.
      split; [reflexivity|]. split; [intros _ H; discriminate|]. intros tops' H. injection H as <-.
      exact (fa_pop_n_nonempty _ _ _ _ _ _ _ Hp (or_intror Hn0)).
Qed.

Lemma cache_alloc_cf_np : forall c x ns, 1 <= c <= 31 -> length (st_cache x) = 32%nat ->
  (Z.to_nat c < length (st_regions x))%nat -> rg_mapped_user (reg x c) mod kUserMapSize = 0 ->
  (if st_cache_inited x then pc_max (cache x c) = max_cached c else cache x c = pclass0) ->
  rpost ns (cache_alloc_cf c x) (fun b r => b = true -> fst r = None ->
    pc_chunks (cache x c) = [] /\ ARM x c (max_cached c / 2 - fa_len (rg_free (reg x c)))).
Proof.
  intros c x ns Hc Hlc Hl Hal Hci. pose proof (class_ok c Hc) as (_ & _ & _ & Km & _).
  unfold cache_alloc_cf, init_cache_if_needed, refill_if_empty_cf. unfold cache in Hci.
  assert (Hc1 : st_cache_inited x = true -> pc_max (znth pclass0 c (st_cache x)) = max_cached c)
    by (intros E; rewrite E in Hci; exact Hci).
  assert (Hc2 : st_cache_inited x = false -> znth pclass0 c (st_cache x) = pclass0)
    by (intros E; rewrite E in Hci; exact Hci).
  clear Hci. rgo.
  destruct (st_cache_inited x) eqn:Ei; rgo.
  - destruct (pc_chunks (znth pclass0 c (st_cache x))) as [|o l] eqn:Hpc; rgo.
    + rewrite (Hc1 eq_refl).
      eapply rpost_mono; [|apply gfa_cf_np; [exact Hc | lia | exact Hl | exact Hal]].
      cbv beta. intros b [got y] (Hcy & Hn & Hs). cbn [fst snd] in *. rgo.
      destruct got as [tops|]; rgo.
      * rewrite Hcy, znth_zupd_same by lia. rred.
        destruct (cache_fill_order tops) as [|o2 l2] eqn:Hcf; rgo; [|intros _ H; discriminate].
        intros _ _. exfalso. apply (Hs tops eq_refl). unfold cache_fill_order in Hcf.
        apply (f_equal (@rev Z)) in Hcf. rewrite rev_involutive in Hcf. exact Hcf.
      * destruct (pc_chunks (znth pclass0 c (st_cache y))) as [|o2 l2]; rgo; [|intros _ H; discriminate].
        intros Hb _. unfold cache. rewrite Hpc. split; [reflexivity|]. exact (Hn Hb eq_refl).
    + rewrite Hpc. rgo. intros _ H. discriminate.
  - rewrite znth_init_caches by lia. rred. rewrite (Hc2 eq_refl). rgo.
    eapply rpost_mono; [|apply gfa_cf_np; [exact Hc | lia | exact Hl | exact Hal]].
    cbv beta. intros b [got y] (Hcy & Hn & Hs). cbn [fst snd] in *. rred in Hcy. rgo.
    destruct got as [tops|]; rgo.
    + rewrite Hcy, znth_zupd_same by (rewrite ?length_init_caches; lia). rred.
      destruct (cache_fill_order tops) as [|o2 l2] eqn:Hcf; rgo; [|intros _ H; discriminate].
      intros _ _. exfalso. apply (Hs tops eq_refl). unfold cache_fill_order in Hcf.
      apply (f_equal (@rev Z)) in Hcf. rewrite rev_involutive in Hcf. exact Hcf.
    + destruct (pc_chunks (znth pclass0 c (st_cache y))) as [|o2 l2]; rgo; [|intros _ H; discriminate].
      intros Hb _. unfold cache. rewrite (Hc2 eq_refl). split; [reflexivity|]. exact (Hn Hb eq_refl).
Qed.

Ltac rtriv := repeat (rred; first [ exact I
  | (intros _ Hnull; cbn [ck_user padd ck_beg] in Hnull; discriminate)
  | match goal with |- rpost _ (bind _ _ _) _ => apply rpost_bind end
  | (eapply rpost_mono; [|apply rpost_true]; cbv beta; intros ? [? ?] _) ]).

(* malloc_cf's NULL with a granted last answer: the class's cache was empty and the arm's test failed *)
Lemma malloc_cf_np : forall U s n tr ns, Wf_cf U s ->
  rpost ns (malloc_cf n tr s) (fun b r => b = true -> fst r = PNull -> from_primary n = true ->
    pc_chunks (cache s (chunk_class n)) = [] /\
    ARM s (chunk_class n) (max_cached (chunk_class n) / 2 - fa_len (rg_free (reg s (chunk_class n))))).
Proof.
  intros U s n tr ns W. unfold malloc_cf. rgo.
  dif; rgo.
  destruct (from_primary n) eqn:Hp; rgo.
  - pose proof (chunk_class_range n Hp) as Hcr.
    pose proof (wfc_classes _ _ _ _ _ W (chunk_class n) ltac:(lia)) as CL.
    eapply rpost_mono; [|apply cache_alloc_cf_np].
    + cbv beta. intros b [o y] Hca. cbn [fst snd] in *. rgo.
      destruct o as [off|]; rgo.
      * rtriv.
      * intros Hb _ _. exact (Hca Hb eq_refl).
    + lia.
    + exact (wfc_len_cache _ _ _ _ _ W).
    + rred. rewrite (wfc_len_regions _ _ _ _ _ W). lia.
    + exact (wrc_mapped_al _ _ _ _ _ _ CL).
    + pose proof (wrc_cache _ _ _ _ _ _ CL) as HC. revert HC. rred.
      destruct (st_cache_inited s); intros HC; [exact (proj1 HC) | exact HC].
  - apply rpost_all. intros b a. apply rpost_all. cbv beta. intros b0 a0 Hb Hr Hfp. congruence.
Qed.

Lemma chunk_offs_split : forall s (c : Z) l, Forall (chunk_ok_cf s) l ->
  (length (flat_map (fun k => match ck_beg k with
                              | PPrim off => if (prim_class off =? c)%Z then [(off - region_off c)%Z] else []
                              | _ => []
                              end) l)
   <= length (filter (PresetRoom.in_cls c) (map ck_req (filter is_alloc l))) +
      length (filter (fun k => negb (is_alloc k) && PresetRoom.in_cls c (ck_req k)) l))%nat.
Proof.
  intros s c l H. induction l as [|k t IH]; [cbn; lia|].
  apply Forall_cons_iff in H as [Hk Ht]. specialize (IH Ht).
  assert (Hk1 : (length (match ck_beg k with
                         | PPrim off => if (prim_class off =? c)%Z then [(off - region_off c)%Z] else []
                         | _ => []
                         end) <= if PresetRoom.in_cls c (ck_req k) then 1 else 0)%nat).
  { destruct Hk as [_ Hk]. revert Hk.
    destruct (ck_beg k) as [|off|r off|cid pos]; intros Hk; cbn [length];
      [apply Nat.le_0_l | | apply Nat.le_0_l | apply Nat.le_0_l].
    destruct (Z.eqb_spec (prim_class off) c) as [E|E]; cbn [length]; [|apply Nat.le_0_l].
    destruct Hk as (Hp & Hpc & _).
    assert (Hin : PresetRoom.in_cls c (ck_req k) = true).
    { unfold PresetRoom.in_cls. rewrite (cls_primary _ Hp), <- Hpc, E. cbn. apply Z.eqb_refl. }
    rewrite Hin. cbn. lia. }
  cbn [flat_map filter map]. rewrite length_app.
  revert Hk1. destruct (is_alloc k); cbn [negb andb map filter];
    destruct (PresetRoom.in_cls c (ck_req k)); cbn [length]; intros Hk1; lia.
Qed.

Lemma chunk_offs_le : forall U s c, Wf_cf U s -> qtight s ->
  Z.of_nat (length (chunk_offs s c)) <=
  Z.of_nat (PresetRoom.ccnt c (map snd (blocks s))) + Z.of_nat (PresetRoom.ccnt c (map ck_n (q_items s))).
Proof.
  intros U s c W T. pose proof (wfc_chunks _ _ _ _ _ W) as HC.
  pose proof (chunk_offs_split s c (st_chunks s) HC) as H1.
  set (A := filter (fun k => negb (is_alloc k) && PresetRoom.in_cls c (ck_req k)) (st_chunks s)) in *.
  assert (H2 : (length A <= PresetRoom.ccnt c (map ck_n (q_items s)))%nat).
  { unfold PresetRoom.ccnt. rewrite length_filter_map. apply NoDup_incl_length.
    - unfold A. apply NoDup_filter. exact (NoDup_map_inv _ _ (wfc_chunks_nodup _ _ _ _ _ W)).
    - intros x Hx. unfold A in Hx. apply filter_In in Hx as [Hx Hb]. apply andb_prop in Hb as [Ha Hcl].
      apply filter_In. split.
      + apply (quar_in_q U s W T x Hx). destruct (ck_state x) eqn:E; [|reflexivity].
        unfold is_alloc in Ha. rewrite E in Ha. cbn in Ha. discriminate.
      + pose proof (proj1 (Forall_forall _ _) HC x Hx) as [Hr _]. unfold ck_n.
        rewrite in_cls_req_size by lia. exact Hcl. }
  assert (E1 : PresetRoom.ccnt c (map snd (blocks s)) =
    length (filter (PresetRoom.in_cls c) (map ck_req (filter is_alloc (st_chunks s))))).
  { unfold PresetRoom.ccnt, blocks. rewrite map_map. reflexivity. }
  unfold chunk_offs. rewrite E1. lia.
Qed.

Lemma null_full_of_arm : forall U s c, Wf_cf U s -> qtight s -> 1 <= c <= 31 ->
  pc_chunks (cache s c) = [] -> ARM s c (max_cached c / 2 - fa_len (rg_free (reg s c))) ->
  Z.of_nat (PresetRoom.ccnt c (PresetRoom.rs_live (room_of_cf s))) +
  Z.of_nat (PresetRoom.ccnt c (PresetRoom.rs_quar (room_of_cf s))) +
  (if c =? PresetRoom.K_BATCH_CLASS then PresetRoom.rs_batches (room_of_cf s) else 0) +
  PresetRoom.refill c > PresetRoom.cap c.
Proof.
  intros U s c W T Hc Hpc HA.
  pose proof (wfc_compl0 _ _ _ _ _ W c Hc) as HC0. unfold cdef in HC0.
  pose proof (wfc_classes _ _ _ _ _ W c Hc) as CL.
  pose proof (fa_elems_length (class_size c) (rg_free (reg s c)) (wrc_runs _ _ _ _ _ _ CL)) as HF.
  rewrite class_elems_eq, !length_app, Hpc in HC0. cbn [length] in HC0. rewrite !Nat2Z.inj_add, HF in HC0.
  pose proof (class_ok c Hc) as (Ks & _).
  pose proof (chunk_offs_le U s c W T) as Hco.
  assert (Hbo : Z.of_nat (length (batch_offs s c)) =
    if c =? kBatchClass then Z.of_nat (length (all_batches s)) else 0).
  { unfold batch_offs. destruct (c =? kBatchClass); [rewrite length_map; reflexivity | reflexivity]. }
  rewrite refill_eq, cap_eq by exact Hc. unfold ARM in HA.
  unfold room_of_cf. cbn [PresetRoom.rs_live PresetRoom.rs_quar PresetRoom.rs_batches].
  unfold PresetRoom.K_BATCH_CLASS. unfold kBatchClass in Hbo.
  assert (Hmain : kFreeArrayOffset < class_size c *
    (Z.of_nat (length (chunk_offs s c)) + Z.of_nat (length (batch_offs s c)) + max_cached c / 2)) by nia.
  assert (Hcap : kFreeArrayOffset / class_size c <
    Z.of_nat (length (chunk_offs s c)) + Z.of_nat (length (batch_offs s c)) + max_cached c / 2)
    by (apply Z.div_lt_upper_bound; lia).
  revert Hbo. destruct (c =? 24); intros Hbo; lia.
Qed.

(* FACT 3. A NULL from malloc_cf whose last environment answer was a grant is a full class. *)
Theorem malloc_cf_null_full : forall U s n tr ns, Wf_cf U s -> room_inv_cf s ->
  rpost ns (malloc_cf n tr s) (fun b r => b = true -> fst r = PNull -> PresetRoom.null_full (room_of_cf s) n).
Proof.
  intros U s n tr ns W T. eapply rpost_mono; [|exact (malloc_cf_np U s n tr ns W)].
  cbv beta. intros b r H Hb Hr c Hc.
  destruct (from_primary n) eqn:Hp; [|rewrite (cls_secondary n Hp) in Hc; discriminate].
  rewrite (cls_primary n Hp) in Hc. injection Hc as <-.
  destruct (H Hb Hr eq_refl) as [Hpc HA].
  apply (null_full_of_arm U s); [exact W | exact T | pose proof (chunk_class_range n Hp); lia | exact Hpc | exact HA].
Qed.

(* ================================================================ fact 2: the FIFO suffix, per class *)
(* The quarantine's global part is at most Q_MAX accounted bytes and its thread part at most Q_CACHE
   (both measured on preset's two images: quarantine_size_mb = 256, thread_local_quarantine_size_kb = 1024,
   a Theorem Labs lane oomroom note, the internal file QCAP.txt). *)
Theorem quar_fifo_parts_cf : forall U s, Wf_cf U s -> room_inv_cf s ->
  items_n (flat_map b_items (qc_list (st_qglobal s))) + kBatchBytes * Z.of_nat (length (qc_list (st_qglobal s)))
    <= PresetRoom.Q_MAX /\
  items_n (flat_map b_items (qc_list (st_qthread s))) + kBatchBytes * Z.of_nat (length (qc_list (st_qthread s)))
    <= PresetRoom.Q_CACHE.
Proof.
  intros U s W (T1 & T2 & _). pose proof (wfc_quarantine _ _ _ _ _ W) as Q.
  pose proof (sum_bytes_items_rm (qc_list (st_qglobal s))) as Eg.
  pose proof (sum_bytes_items_rm (qc_list (st_qthread s))) as Et.
  rewrite <- (wq_bytes_g _ Q) in Eg. rewrite <- (wq_bytes_t _ Q) in Et.
  unfold PresetRoom.Q_MAX, PresetRoom.Q_CACHE, kQuarantineMax, kQuarantineCacheMax in *. lia.
Qed.

(* THE PER-CLASS COROLLARY. A caller that knows the free history hist (each free_cf appends freed_cf, which
   accounts at least one byte, freed_cf_pos) bounds the quarantine's class-c chunks by the class-c chunks of
   the last frees of hist up to Q_MAX + Q_CACHE accounted bytes, in bytes and in number. *)
Theorem quar_class_bound_cf : forall U hist s c, Wf_cf U s -> room_inv_cf s -> quar_fifo_cf hist s ->
  Forall (fun k => 0 <= ck_n k) hist ->
  cbytes c (q_items s) <= cbytes c (last_frees PresetRoom.QT hist) /\
  (ccount c (q_items s) <= ccount c (last_frees PresetRoom.QT hist))%nat.
Proof.
  intros U hist s c W T [pre Eh] Hpos. subst hist. apply Forall_app in Hpos as [Hpre Hq].
  assert (HT : items_n (q_fifo s) <= PresetRoom.QT).
  { pose proof (quar_bytes_ok_cf U s W T) as (_ & Hb0 & _ & Hz). unfold room_of_cf in Hb0, Hz.
    cbn [PresetRoom.rs_quar PresetRoom.rs_batches] in Hb0, Hz.
    rewrite zsum_map_ck_n, items_n_q in Hz. unfold PresetRoom.Q_BATCH_BYTES in Hz. lia. }
  unfold last_frees. rewrite rev_app_distr, take_within_app; [| apply Forall_rev; exact Hq | rewrite items_n_rev; exact HT].
  rewrite rev_app_distr, rev_involutive, cbytes_q, ccount_q, cbytes_app, ccount_app.
  assert (HX : Forall (fun x => 0 <= ck_n x) (rev (take_within (PresetRoom.QT - items_n (rev (q_fifo s))) (rev pre)))).
  { apply Forall_forall. intros x Hx. rewrite <- in_rev in Hx. apply take_within_incl in Hx.
    rewrite <- in_rev in Hx. exact (proj1 (Forall_forall _ _) Hpre x Hx). }
  pose proof (cbytes_nonneg c _ HX). split; lia.
Qed.

(* ================================================================ the call forms over atok_cf *)
Theorem malloc_cf_room_atok : forall U s n tr ns Q, Wf_cf U s -> room_inv_cf s ->
  atok_cf ns (malloc_cf n tr s) Q ->
  atok_cf ns (malloc_cf n tr s) (fun b r => Q b r /\
    ((room_inv_cf (snd r) /\ (q_fifo (snd r) = q_fifo s /\ all_batches (snd r) = all_batches s)) /\
     (b = true -> fst r = PNull -> PresetRoom.null_full (room_of_cf s) n))).
Proof.
  intros U s n tr ns Q W T HQ. apply atok_cf_rpost; [exact HQ|].
  apply rpost_and; [apply rpost_and|].
  - exact (malloc_cf_room_inv U s n tr ns W T).
  - exact (malloc_cf_fifo s n tr ns).
  - exact (malloc_cf_null_full U s n tr ns W T).
Qed.

Theorem free_cf_room_atok : forall U s p tr ns Q, Wf_cf U s -> room_inv_cf s ->
  atok_cf ns (free_cf p tr s) Q ->
  atok_cf ns (free_cf p tr s) (fun b r => Q b r /\
    (room_inv_cf (snd r) /\ exists P, q_fifo s ++ freed_cf s p = flat_map b_items P ++ q_fifo (snd r))).
Proof.
  intros U s p tr ns Q W T HQ. apply atok_cf_rpost; [exact HQ|].
  apply rpost_and.
  - exact (free_cf_room_inv U s p tr ns W T).
  - exact (free_cf_fifo p tr s ns).
Qed.

End ROOM.
