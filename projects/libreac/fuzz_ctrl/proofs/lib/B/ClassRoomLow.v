(* The pure theorems of the ASan class-accounting family (a Theorem Labs lane), over the definitions of lib/B/ClassConsDef.v.
   Each speaks only of an allocator state and the model's own functions (AZ/Spec/AsanCtrl.v), so none needs the W6
   heap field. They are here, below the field, because the W6 sites cannot see the field (W6/AHDef.v (not in this delivery) and
   W6/MallocCloseDef.v (not in this delivery) Require W6/MallocRoom.v (not in this delivery) directly), so a Theorem Labs lane's low lemma needs them as theorems, not as
   premises. This file Requires only AZ/Spec/{STree, AsanCtrl, AsanCtrlProps} and lib/A/ClassConsDef.v (STree adds no
   dependency: AsanCtrl already Requires it; do not prune it). NOTHING IN THIS FILE MAY EVER IMPORT THE HEAP FIELD.
   Do NOT Require AZ/Spec/AsanBudget.v (not in this delivery) either, not even to cite one lemma (a Theorem Labs lane, 2026-10-28 10:31Z): a per-unit
   tree may not have it (fuzz_ctrl does not), and it pulls MI_Inv, LB_Inv, LB_Sum, SizeHist, AZ/AS/BackingAlgebra and
   AsanInv behind it, while this low layer must stay at three AZ/Spec files so that other units can carry it. So
   crl_size2n_range and crl_size_le_2n (and ClassConsDef.v crl_size2n_chk) are deliberate local copies of
   AsanBudget's size2n_range, size_le_2n and size2n_chk, under other names so that a file that imports both sees
   one definition per name.

   - One refill: size_of_class_le, max_cached_half_le, cache_alloc_requested_le (cache_alloc asks at most 8 slots),
     refill_ums_le, pop_walk and refill_step_bound (along populate_free_array, only class c's user map grows, by
     pop_ums <= 2 * K_USER_MAP).
   - no_class_full: at a class_room state, a refill that cache_alloc can start does not take populate_free_array's
     class-full branch (UCheck 705). W6/ClassFullDead.v (not in this delivery) no_refill_full_of_room stays high: its statement cites
     W6/MallocClassRun.v (not in this delivery) refill_full_at, a site-level file of a Theorem Labs lane's; no_class_full is the stronger statement (it
     refutes the branch of populate_free_array itself, not the derived predicate).
   - class_room_of_live, class_room_of_live_per_class: class_room from class_cons, a bound on the live slots and a
     bound on the quarantined slots (one constant, or per class with QSLOT).
   - qwf_class_chunks_bound, qwf_quarantine_class_bound: the quarantine's slots from its user bytes over a_quar_wf
     (ported from the released AsanBudget.v, whose own forms, AZ/Spec/AsanBudget.v class_chunks_bound and
     quarantine_class_bound, ask more of a chunk and bound less tightly; see each lemma), through crl_size_le_2n;
     quar_slots_of_bytes_c: per class, from a_quar_wf and quar_sum <= Q <= Q_MAX + Q_CACHE, the quarantined slots
     are at most QSLOT_of Q c (W6/QSlot.v has the argument and the two refutations that show the premises are
     needed). qmin_of_class_lb reads the least request of a class off the List.find structurally; the vm_compute
     checks of the per-class constants stay in W6/QSlot.v. crl_size2n_range and qslot_qmin_24 are this file's
     vm_compute cost (crl_size_le_2n and the batch-class case of quar_slots_of_bytes_c need them).
   - The per-class live counts (two Theorem Labs lanes 08:02Z and 08:07Z): a_class_count / a_class_bytes over cons, snoc,
     append, removal from the middle, permutation and a duplicate-free selection (a_class_bytes_incl, for carrying a
     per-class bound across a call whose post says only which blocks survive); the count form and its upper-bound
     form; a_class_req_fits_of_count (the contract premise from per-class counts); a_class_bytes_le_total against the
     total slot bytes a_slot_bytes, and a_class_bytes_le_user against the user bytes a_user_bytes (both defined in
     lib/B/ClassConsDef.v; a_user_bytes is the same Fixpoint as Contract.v a_live_bytes); a_class_bytes_above: with
     every block at most K bytes, the classes above class_id (needed_size K) are empty. class_needed0_steps (8 ..
     64512, one class_id step at a time) is the vm_compute cost of a_class_bytes_above.
   - The per-class bound at an allocator call, for any unit (two Theorem Labs lanes 10:28Z): class_Bc N SP, the contracts'
     Bc from a unit's live count bound N and its slot's share SP; class_slot_entry and class_slot_entry_count (the
     slot's entry form); class_room_of_rows (the room row from a check over W6/QSlot.v qslot_table's rows);
     class_call_bound, class_call_pair, class_call_pair_l, class_free_pair (the contract premises over the call heap);
     in_class_max1 and a_class_req_fits_snoc (the heap after a request); a_class_req_fits_one_slot and
     a_class_bytes_one_le (the share SP = size_of_class). The section's comment has an example instantiation.
   - The per-class entry premise from a driver's fact (a Theorem Labs lane 12:47Z and 12:55Z: their one home is this file, which
     every unit reaches through the W6 hop; they were a Theorem Labs lane's lib/A/ClassEntry.v (not in this delivery), statements unchanged):
     a_class_count_le_length (with the counts: no class has more blocks than H), a_class_entry_arith (the
     arithmetic over an opaque class-byte value), a_class_entry_of_length (from (length H <= k)%nat),
     a_class_req_fits_entry (a_class_req_fits from the entry premise and a non-negative share that covers one slot
     of the requested class). ClassEntry.v's count form a_class_entry_of_count is retired for
     class_slot_entry_count. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrlProps.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ClassConsDef.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user
                         cls_set_count].

(* ---------- Arithmetic of one refill ---------- *)

Lemma size_of_class_le : forall c, 0 <= c < K_NUM_CLASSES -> 0 <= size_of_class c <= K_MAX_SIZE.
Proof.
  intros c Hc.
  assert (Hall : forallb size_chk (AsanCtrlProps.zseq 0 (Z.to_nat 32)) = true) by (vm_compute; reflexivity).
  pose proof (AsanCtrlProps.forallb_zseq size_chk 0 (Z.to_nat 32) Hall c
                ltac:(rewrite Z2Nat.id by lia; unfold K_NUM_CLASSES in Hc; lia)) as H.
  unfold size_chk in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma max_cached_half_le : forall c, max_cached c / 2 <= 8.
Proof.
  intros c. unfold max_cached. remember (1024 / size_of_class c) as q eqn:Eq. clear Eq.
  apply Z.div_le_upper_bound; lia.
Qed.

(* The request cache_alloc st c passes to populate_free_array (AsanCtrl.v:324: n - c_num_freed r1 with
   n = max_count st1 c / 2, r1 = get_cls st1 c, st1 = init_cache st) is at most 8 slots. *)
Lemma cache_alloc_requested_le : forall st c,
  0 <= c_num_freed (get_cls st c) ->
  max_count (init_cache st) c / 2 - c_num_freed (get_cls (init_cache st) c) <= 8.
Proof.
  intros st c Hnf. rewrite AsanCtrlProps.max_count_init_cache, AsanCtrlProps.get_cls_init_cache.
  pose proof (max_cached_half_le c). lia.
Qed.

Lemma rup_user_nonpos : forall x, x <= 0 -> rup x K_USER_MAP <= 0.
Proof.
  intros x Hx. unfold rup, K_USER_MAP.
  assert ((x + 262144 - 1) / 262144 < 1) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma refill_ums_le : forall st c req,
  0 <= c < K_NUM_CLASSES ->
  c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) ->
  req <= 8 ->
  pop_ums st c req <= 2 * K_USER_MAP.
Proof.
  intros st c req Hc Ham Hreq. unfold pop_ums.
  destruct (Z_lt_le_dec (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c) + req * size_of_class c))
    as [Hgt|Hle].
  - pose proof (size_of_class_le c Hc) as [S0 S1].
    assert (HrS : req * size_of_class c <= 8 * size_of_class c) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (EM : K_MAX_SIZE = 65536) by reflexivity. rewrite EM in S1.
    unfold rup. assert (EK : K_USER_MAP = 262144) by reflexivity. rewrite EK.
    assert (Hq : (c_allocated_user (get_cls st c) + req * size_of_class c - c_mapped_user (get_cls st c)
                  + 262144 - 1) / 262144 < 3) by (apply Z.div_lt_upper_bound; lia).
    lia.
  - eapply Z.le_trans; [apply rup_user_nonpos; lia | unfold K_USER_MAP; lia].
Qed.

(* ---------- One refill walked to its leaves ---------- *)

Lemma am_all_aundef : forall R (P : R -> Prop) u (k : AM R), am_all P (aundef_ u k).
Proof. intros. exact I. Qed.

Lemma mu_eq_refl : forall st, mu_eq st st.
Proof. intros st c. reflexivity. Qed.

Lemma mu_eq_put : forall st c r, c_mapped_user r = c_mapped_user (get_cls st c) -> mu_eq st (put_cls c r st).
Proof.
  intros st c r E c'. destruct (Z.eq_dec c c') as [<-|Hne].
  - rewrite AsanCtrlProps.get_put_eq. exact E.
  - rewrite AsanCtrlProps.get_put_ne by exact Hne. reflexivity.
Qed.

(* ensure_free_array moves only c_mapped_free_array. *)
Lemma am_all_ensure : forall R (P : R -> Prop) st c nf (k : astate -> bool -> AM R),
  (forall st' ok, mu_eq st st' -> am_all P (k st' ok)) ->
  am_all P (ensure_free_array st c nf k).
Proof.
  intros R P st c nf k Hk. unfold ensure_free_array. cbv beta zeta.
  destruct (nf * 4 <=? c_mapped_free_array (get_cls st c)); [apply Hk, mu_eq_refl |].
  destruct (K_FREEARR_MAX <? rup (nf * 4) K_FREEARR_MAP); [apply am_all_aundef |].
  unfold ev. intros x. cbv beta.
  destruct (negb (fixed_answer_ok _ x)); [apply am_all_aundef |].
  destruct (is_err x); [apply Hk, mu_eq_refl |].
  apply Hk. apply mu_eq_put. reflexivity.
Qed.

Lemma pop_leaf_refl : forall st c req, pop_leaf st c req st.
Proof. intros st c req. split; [intros; reflexivity | left; reflexivity]. Qed.

Lemma pop_walk : forall R (P : R -> Prop) st c req (k : astate -> bool -> AM R),
  (forall st' ok, pop_leaf st c req st' -> am_all P (k st' ok)) ->
  am_all P (populate_free_array st c req k).
Proof.
  intros R P st c req k Hk. unfold populate_free_array. cbv beta zeta.
  destruct (Z.leb_spec (c_allocated_user (get_cls st c) + req * size_of_class c) (c_mapped_user (get_cls st c)))
    as [Hle|Hgt].
  - (* no user map: carve from the mapped tail *)
    apply am_all_ensure. intros st2 ok E. cbv beta. destruct ok; cbn [negb]; apply Hk; split.
    + intros c' Hc'. rewrite AsanCtrlProps.get_put_ne by lia. exact (E c').
    + left. rewrite AsanCtrlProps.get_put_eq. cproj. exact (E c).
    + intros c' _. exact (E c').
    + left. exact (E c).
  - destruct (K_FREEARR_OFF <? _); [apply am_all_aundef |].
    unfold ev. intros a. cbv beta.
    destruct (negb (fixed_answer_ok _ a)); [apply am_all_aundef |].
    destruct (is_err a).
    { apply Hk. apply pop_leaf_refl. }
    apply am_all_ensure. intros st2 ok E. cbv beta. destruct ok; cbn [negb]; apply Hk; split.
    + intros c' Hc'. rewrite AsanCtrlProps.get_put_ne by lia. rewrite (E c').
      rewrite AsanCtrlProps.get_put_ne by lia. reflexivity.
    + right. split; [exact Hgt |]. rewrite AsanCtrlProps.get_put_eq. cproj. rewrite (E c).
      rewrite AsanCtrlProps.get_put_eq. cproj. reflexivity.
    + intros c' Hc'. rewrite (E c'). rewrite AsanCtrlProps.get_put_ne by lia. reflexivity.
    + right. split; [exact Hgt |]. rewrite (E c). rewrite AsanCtrlProps.get_put_eq. cproj. reflexivity.
Qed.

(* One refill: along populate_free_array st c req every other class keeps its user map, and class c keeps its user
   map or (the mapping branch) maps ums = pop_ums st c req more bytes, with ums <= 2 * K_USER_MAP. *)
Theorem refill_step_bound : forall R (P : R -> Prop) st c req (k : astate -> bool -> AM R),
  0 <= c < K_NUM_CLASSES ->
  c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) ->
  req <= 8 ->
  (forall st' ok,
     (forall c', c' <> c -> c_mapped_user (get_cls st' c') = c_mapped_user (get_cls st c')) ->
     c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c)
     \/ (pop_ums st c req <= 2 * K_USER_MAP
         /\ c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) + pop_ums st c req) ->
     am_all P (k st' ok)) ->
  am_all P (populate_free_array st c req k).
Proof.
  intros R P st c req k Hc Ham Hreq Hk. apply pop_walk. intros st' ok [HO HC]. apply Hk; [exact HO |].
  destruct HC as [E | [_ E]]; [left; exact E | right].
  split; [exact (refill_ums_le st c req Hc Ham Hreq) | exact E].
Qed.

(* ---------- class_room: no class-full abort ---------- *)

(* A refill of class c at st that cache_alloc can start (empty cache, fewer than max_cached c / 2 free slots) does not
   take the UCheck 705 branch of populate_free_array (AsanCtrl.v:302) for any request of at most 8 slots
   (cache_alloc_requested_le). *)
Theorem no_class_full : forall st c req,
  class_room st -> 0 <= c < K_NUM_CLASSES ->
  c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) ->
  c_count (get_cls st c) <= 0 -> c_num_freed (get_cls st c) < max_cached c / 2 ->
  req <= 8 ->
  (K_FREEARR_OFF <? c_mapped_user (get_cls st c) + pop_ums st c req) = false.
Proof.
  intros st c req HR Hc Ham Hcnt Hlt Hreq. apply Z.ltb_ge.
  pose proof (HR c Hc Hcnt Hlt) as Hroom. pose proof (refill_ums_le st c req Hc Ham Hreq) as Hu.
  lia.
Qed.

(* AsanBudget.v room_of_AINV (:134-148) in this tree: class_cons (ClassConsDef.v) bounds the allocated bytes of class
   c by its live, quarantined, batch, free and cached slots, and the mapped bytes by one slot more. At a refill
   (class_room's case) the free and cached slots number at most 7 (max_cached c / 2 <= 8), so with the carve slot they
   weigh at most 8 * K_MAX_SIZE. The released headroom is 2^20; here it is 2 * K_USER_MAP, the most one refill maps
   (refill_ums_le), because class_cons carries the carve tail as one slot. *)
Theorem class_room_of_live : forall H st B QS,
  class_cons H st -> a_class_live_bytes H B -> a_quar_slots st QS ->
  B + QS + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF ->
  class_room st.
Proof.
  intros H st B QS HC HL HQ HK c Hc Hcnt Hlt.
  destruct (HC c Hc) as [C1 C2]. specialize (HL c Hc). specialize (HQ c Hc).
  pose proof (size_of_class_le c Hc) as [S0 S1]. pose proof (max_cached_half_le c) as Hm.
  unfold c_reserved_user, POP_SLACK in C1, C2.
  assert (HnS : (c_num_freed (get_cls st c) + c_count (get_cls st c)) * size_of_class c <= 7 * size_of_class c)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

(* class_room_of_live with a live bound Bc c and the quarantine bound QSLOT c per class. class_room_of_live takes
   one B and one QS for all classes, so this lemma repeats its five-line proof class by class instead of calling it. *)
Lemma class_room_of_live_per_class : forall H st (Bc : Z -> Z),
  ClassConsDef.class_cons H st ->
  (forall c, 0 <= c < K_NUM_CLASSES -> ClassConsDef.a_class_bytes H c <= Bc c) ->
  (forall c, 0 <= c < K_NUM_CLASSES ->
     ClassConsDef.qprim_bytes st c + ClassConsDef.qbatch_bytes st c <= QSLOT c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF) ->
  ClassConsDef.class_room st.
Proof.
  intros H st Bc HC HL HQ HK c Hc Hcnt Hlt.
  destruct (HC c Hc) as [C1 C2]. specialize (HL c Hc). specialize (HQ c Hc). specialize (HK c Hc).
  pose proof (size_of_class_le c Hc) as [S0 S1]. pose proof (max_cached_half_le c) as Hm.
  unfold c_reserved_user, POP_SLACK in C1, C2.
  assert (HnS : (c_num_freed (get_cls st c) + c_count (get_cls st c)) * size_of_class c <= 7 * size_of_class c)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

(* ---------- The quarantine's slots from its bytes (ported from AsanBudget.v) ---------- *)

(* Deliberate local copy of AZ/Spec/AsanBudget.v size2n_range (this file must not Require AsanBudget: see header). *)
Lemma crl_size2n_range : forallb crl_size2n_chk (AsanCtrlProps.zseq 0 (Z.to_nat 64513)) = true.
Proof. vm_compute. reflexivity. Qed.

(* Deliberate local copy of AZ/Spec/AsanBudget.v size_le_2n: a primary request of n bytes takes at most 2 n + 32. *)
Lemma crl_size_le_2n : forall n, 0 <= n <= 64512 -> size_of_class (class_id (needed_size n)) <= 2 * n + 32.
Proof.
  intros. apply Z.leb_le. apply (AsanCtrlProps.forallb_zseq crl_size2n_chk 0 (Z.to_nat 64513) crl_size2n_range).
  rewrite Z2Nat.id; lia.
Qed.

Lemma qchunk_wf_nonneg : forall ch, qchunk_wf ch -> 0 <= chunk_size ch.
Proof. intros [c n | mb ms n] H; cbn [qchunk_wf chunk_size] in *; [destruct H as [H _] |]; lia. Qed.

Lemma cfd_zlen_app : forall {A} (l1 l2 : list A), cfd_zlen (l1 ++ l2) = cfd_zlen l1 + cfd_zlen l2.
Proof. intros. unfold cfd_zlen. rewrite List.length_app. lia. Qed.
Lemma cfd_zlen_cons : forall {A} (x : A) l, cfd_zlen (x :: l) = 1 + cfd_zlen l.
Proof. intros. unfold cfd_zlen. cbn [List.length]. lia. Qed.
Lemma cfd_zlen_nonneg : forall {A} (l : list A), 0 <= cfd_zlen l.
Proof. intros. unfold cfd_zlen. lia. Qed.
Lemma cfd_cntP_app : forall c l1 l2, cfd_cntP c (l1 ++ l2) = cfd_cntP c l1 + cfd_cntP c l2.
Proof. intros. unfold cfd_cntP. rewrite List.filter_app. apply cfd_zlen_app. Qed.
Lemma cfd_cntP_cons : forall c ch l, cfd_cntP c (ch :: l) = (if cfd_is_prim_of c ch then 1 else 0) + cfd_cntP c l.
Proof. intros. unfold cfd_cntP. cbn [List.filter]. destruct (cfd_is_prim_of c ch); [rewrite cfd_zlen_cons|]; lia. Qed.
Lemma cfd_qchunks_cons : forall b bs, cfd_qchunks (b :: bs) = b_chunks b ++ cfd_qchunks bs.
Proof. reflexivity. Qed.

(* AZ/Spec/AsanBudget.v zsumc_nonneg asks 0 <= chunk_size of each chunk; this one takes the quarantine's qchunk_wf. *)
Lemma qwf_zsumc_nonneg : forall l, Forall qchunk_wf l -> 0 <= cfd_zsumc l.
Proof.
  induction l as [|ch l IHl]; intros H; cbn; [lia|].
  apply Forall_cons_iff in H as [H1 H]. specialize (IHl H). pose proof (qchunk_wf_nonneg ch H1). lia.
Qed.

Lemma user_zsumc : forall l, fold_right Z.add 0 (map chunk_size l) = cfd_zsumc l.
Proof. induction l as [|ch l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma qsum_cons : forall b bs,
  qsum (b :: bs) = fold_right Z.add 0 (map chunk_size (b_chunks b)) + Q_BATCH_BYTES + qsum bs.
Proof. reflexivity. Qed.

Lemma qprim_count_cntP : forall st c, qprim_count st c = cfd_cntP c (cfd_qchunks (a_qloc st ++ a_qglob st)).
Proof.
  intros st c. unfold qprim_count, qbatch_chunks, cfd_cntP, cfd_zlen, cfd_qchunks, cfd_is_prim_of.
  rewrite List.flat_map_concat_map. reflexivity.
Qed.

(* AZ/Spec/AsanBudget.v class_chunks_bound asks chunk_wf ATOP (a secondary chunk 64512 < n <= 2^30, its map size and
   base) and 0 <= chunk_size; this one asks only qchunk_wf (a secondary chunk 0 <= n), so it is the stronger lemma. *)
Lemma qwf_class_chunks_bound : forall c l, 1 <= c <= 31 -> Forall qchunk_wf l ->
  size_of_class c * cfd_cntP c l <= 2 * cfd_zsumc l + 32 * cfd_zlen l.
Proof.
  intros c l Hc HW. induction l as [|ch l IH]; [unfold cfd_cntP, cfd_zlen; cbn; lia|].
  apply Forall_cons_iff in HW as [H1 HW]. specialize (IH HW).
  rewrite cfd_cntP_cons, cfd_zlen_cons. cbn [cfd_zsumc].
  destruct ch as [c' n|mb ms n]; cbn [cfd_is_prim_of chunk_size qchunk_wf] in *.
  - destruct H1 as [Hn ->]. destruct (Z.eqb_spec (class_id (needed_size n)) c) as [E|NE]; cbv beta iota.
    + subst c. pose proof (crl_size_le_2n n ltac:(lia)). nia.
    + nia.
  - nia.
Qed.

(* Released AsanBudget.v:123-133, with the batch slots of K_BATCH_CLASS (8192 bytes per batch) carried in the same
   bound: a batch's slots weigh at most 2 * user + 32 * Q_BATCH + 8192 <= 6 * (user + Q_BATCH_BYTES).
   AZ/Spec/AsanBudget.v quarantine_class_bound asks batch_wf and chunk_wf ATOP and concludes the three parts
   separately (slots <= 6 * bsum, 8192 * batches <= bsum, 0 <= bsum); summed they give 6 + 1 = 7 * bsum where this
   one gives 6, so this is the tighter bound; W6/ClassFullDead.v quar_slots_of_bytes's 6 * Q depends on it. *)
Lemma qwf_quarantine_class_bound : forall c bs, 1 <= c <= 31 -> Forall qbatch_wf bs ->
  size_of_class c * cfd_cntP c (cfd_qchunks bs) + 8192 * cfd_zlen bs <= 6 * qsum bs /\ 0 <= qsum bs.
Proof.
  intros c bs Hc HQW. induction bs as [|b bs IH]; [unfold cfd_cntP, cfd_zlen, qsum; cbn; lia|].
  apply Forall_cons_iff in HQW as [[Hlen Hw] HQW]. destruct (IH HQW) as [I1 I2].
  rewrite qsum_cons, user_zsumc, cfd_qchunks_cons, cfd_cntP_app, cfd_zlen_cons.
  pose proof (qwf_class_chunks_bound c (b_chunks b) Hc Hw) as C. pose proof (qwf_zsumc_nonneg _ Hw) as Hz0.
  unfold cfd_zlen in C. unfold Q_BATCH, Q_BATCH_BYTES in *.
  nia.
Qed.

(* ---------- Per class, with the least request of each class ---------- *)

Lemma qmin_of_class_pos : forall c, 1 <= qmin_of_class c.
Proof.
  intros c. unfold qmin_of_class.
  destruct (List.find (in_class c) (AsanCtrlProps.zseq 1 (Z.to_nat 64512))) as [n|] eqn:E; [| lia].
  apply List.find_some in E as [Hin _]. apply AsanCtrlProps.zseq_spec in Hin. lia.
Qed.

(* The first element of zseq lo k that meets p is at most every element of zseq lo k that meets p. *)
Lemma find_zseq_first : forall (p : Z -> bool) k lo x,
  In x (AsanCtrlProps.zseq lo k) -> p x = true ->
  exists m, List.find p (AsanCtrlProps.zseq lo k) = Some m /\ m <= x.
Proof.
  intros p k. induction k as [|k IH]; intros lo x Hin Hp; [destruct Hin |].
  cbn [AsanCtrlProps.zseq List.find] in *.
  destruct (p lo) eqn:Hlo.
  - exists lo. split; [reflexivity |].
    destruct Hin as [<- | Hin]; [lia |]. apply AsanCtrlProps.zseq_spec in Hin. lia.
  - destruct Hin as [<- | Hin]; [congruence |]. exact (IH (lo + 1) x Hin Hp).
Qed.

(* The form the counting lemmas use: every request of class c is at least qmin_of_class c. qmin_of_class is a List.find
   over the ascending 1 .. 64512, so its result is the least request of class c (find_zseq_first); no table is
   computed here (W6/QSlot.v qmin_of_class_min checks the same by vm_compute). *)
Lemma qmin_of_class_lb : forall c, 0 <= c < K_NUM_CLASSES ->
  forall n, 1 <= n <= 64512 -> class_id (needed_size n) = c -> qmin_of_class c <= n.
Proof.
  intros c _ n Hn Hcn.
  assert (Hp : is_primary n = true) by (rewrite AsanCtrlProps.is_primary_iff by lia; apply Z.leb_le; lia).
  assert (Hin : In n (AsanCtrlProps.zseq 1 (Z.to_nat 64512)))
    by (apply AsanCtrlProps.zseq_spec; rewrite Z2Nat.id; lia).
  assert (Hc : in_class c n = true) by (unfold in_class; rewrite Hp, Hcn, Z.eqb_refl; reflexivity).
  destruct (find_zseq_first (in_class c) _ 1 n Hin Hc) as (m & E & Hm).
  unfold qmin_of_class. rewrite E. exact Hm.
Qed.

Example qslot_qmin_24 : qmin_of_class K_BATCH_CLASS = 5889.
Proof. vm_compute. reflexivity. Qed.

Example qslot_size_24 : size_of_class K_BATCH_CLASS = 8192.
Proof. vm_compute. reflexivity. Qed.

(* In a list of well-formed chunks, the class-c primary chunks carry at least m bytes each when every request of
   class c is at least m, and they are no more than the list's length. *)
Lemma prim_chunks_lb : forall c m l, Forall qchunk_wf l ->
  (forall n, 1 <= n <= 64512 -> class_id (needed_size n) = c -> m <= n) ->
  m * cfd_cntP c l <= cfd_zsumc l /\ cfd_cntP c l <= cfd_zlen l.
Proof.
  intros c m l HW HM. induction l as [|ch l IH]; [unfold cfd_cntP, cfd_zlen; cbn; lia |].
  apply Forall_cons_iff in HW as [H1 HW]. destruct (IH HW) as [I1 I2].
  rewrite cfd_cntP_cons, cfd_zlen_cons. cbn [cfd_zsumc].
  destruct ch as [c' n | mb ms n]; cbn [cfd_is_prim_of chunk_size qchunk_wf] in *.
  - destruct H1 as [Hn Hc']. destruct (Z.eqb_spec c' c) as [E | NE]; cbv beta iota.
    + pose proof (HM n Hn (eq_trans (eq_sym Hc') E)). split; nia.
    + split; nia.
  - split; nia.
Qed.

(* Partial batches cost nothing extra: per batch, k class-c chunks with k <= Q_BATCH satisfy
   k * (m * Q_BATCH + Q_BATCH_BYTES) <= Q_BATCH * (their bytes + Q_BATCH_BYTES). *)
Lemma quar_count_bound : forall c m bs, Forall qbatch_wf bs ->
  (forall n, 1 <= n <= 64512 -> class_id (needed_size n) = c -> m <= n) ->
  cfd_cntP c (cfd_qchunks bs) * (m * Q_BATCH + Q_BATCH_BYTES) <= Q_BATCH * qsum bs.
Proof.
  intros c m bs HQW HM. induction bs as [|b bs IH]; [unfold cfd_cntP, cfd_zlen, qsum; cbn; lia |].
  apply Forall_cons_iff in HQW as [[Hlen Hw] HQW]. specialize (IH HQW).
  rewrite qsum_cons, user_zsumc, cfd_qchunks_cons, cfd_cntP_app.
  destruct (prim_chunks_lb c m (b_chunks b) Hw HM) as [L1 L2]. unfold cfd_zlen in L2.
  unfold Q_BATCH, Q_BATCH_BYTES in *. nia.
Qed.

(* With one metadata slot per batch as well (class K_BATCH_CLASS), when m <= Q_BATCH_BYTES:
   (k + 1) * (m * Q_BATCH + Q_BATCH_BYTES) <= (Q_BATCH + 1) * (k * m + Q_BATCH_BYTES), because
   (Q_BATCH - k) * (Q_BATCH_BYTES - m) >= 0. *)
Lemma quar_count_batches_bound : forall c m bs, m <= Q_BATCH_BYTES -> Forall qbatch_wf bs ->
  (forall n, 1 <= n <= 64512 -> class_id (needed_size n) = c -> m <= n) ->
  (cfd_cntP c (cfd_qchunks bs) + cfd_zlen bs) * (m * Q_BATCH + Q_BATCH_BYTES) <= (Q_BATCH + 1) * qsum bs.
Proof.
  intros c m bs Hm HQW HM. induction bs as [|b bs IH]; [unfold cfd_cntP, cfd_zlen, qsum; cbn; lia |].
  apply Forall_cons_iff in HQW as [[Hlen Hw] HQW]. specialize (IH HQW).
  rewrite qsum_cons, user_zsumc, cfd_qchunks_cons, cfd_cntP_app, cfd_zlen_cons.
  destruct (prim_chunks_lb c m (b_chunks b) Hw HM) as [L1 L2]. unfold cfd_zlen in L2.
  pose proof (Z.mul_nonneg_nonneg (Q_BATCH - cfd_cntP c (b_chunks b)) (Q_BATCH_BYTES - m)
                ltac:(lia) ltac:(lia)) as P.
  unfold Q_BATCH, Q_BATCH_BYTES in *. nia.
Qed.

(* The quarantine's slots per class from its bytes. The premise Q <= Q_MAX + Q_CACHE is NECESSARY, not a
   convenience: at c = K_BATCH_CLASS the batch slots exceed the + Q_BATCH term once Q > 1020 * 6020861. With 1022
   full batches of CPrim 24 5889, a_quar_wf holds, quar_sum = 6153319942 and the class-24 slots are
   8556412928 > QSLOT_of 6153319942 24 = 8556404736 (W6/QSlot.v qslot_of_needs_q_cap). Do not drop it. Every caller
   instantiates Q at Q_MAX + Q_CACHE, the cap the drain keeps. *)
Lemma quar_slots_of_bytes_c : forall st Q,
  ClassConsDef.a_quar_wf st ->
  ClassConsDef.quar_sum st <= Q ->
  Q <= Q_MAX + Q_CACHE ->
  forall c, 0 <= c < K_NUM_CLASSES ->
    ClassConsDef.qprim_bytes st c + ClassConsDef.qbatch_bytes st c <= QSLOT_of Q c.
Proof.
  intros st Q HW HQ HQM c Hc.
  unfold a_quar_wf in HW. unfold quar_sum in HQ.
  unfold qprim_bytes, qbatch_bytes, QSLOT_of. rewrite qprim_count_cntP.
  pose proof (qmin_of_class_lb c Hc) as HM.
  pose proof (qmin_of_class_pos c) as Hq1.
  pose proof (size_of_class_le c Hc) as [S0 _].
  destruct (Z.eqb_spec c K_BATCH_CLASS) as [-> | NE]; cbv beta iota.
  - (* the batch class: its chunks and one metadata slot per batch *)
    rewrite qslot_qmin_24 in HM |- *. rewrite qslot_size_24.
    pose proof (quar_count_batches_bound K_BATCH_CLASS 5889 _ ltac:(unfold Q_BATCH_BYTES; lia) HW HM) as HB.
    unfold cfd_zlen in HB.
    assert (HX : cfd_cntP K_BATCH_CLASS (cfd_qchunks (a_qloc st ++ a_qglob st))
                 + Z.of_nat (List.length (a_qloc st ++ a_qglob st)) - 1020
                 <= Q * Q_BATCH / (5889 * Q_BATCH + Q_BATCH_BYTES)).
    { apply Z.div_le_lower_bound; [unfold Q_BATCH, Q_BATCH_BYTES; lia |].
      unfold Q_MAX, Q_CACHE, Q_BATCH, Q_BATCH_BYTES in *. lia. }
    set (F := Q * Q_BATCH / (5889 * Q_BATCH + Q_BATCH_BYTES)) in *.
    unfold Q_BATCH in *. lia.
  - (* every other class: its chunks only *)
    pose proof (quar_count_bound c (qmin_of_class c) _ HW HM) as HB.
    assert (Hk : cfd_cntP c (cfd_qchunks (a_qloc st ++ a_qglob st))
                 <= Q * Q_BATCH / (qmin_of_class c * Q_BATCH + Q_BATCH_BYTES)).
    { apply Z.div_le_lower_bound; [unfold Q_BATCH, Q_BATCH_BYTES; lia |].
      unfold Q_BATCH, Q_BATCH_BYTES in *. lia. }
    set (F := Q * Q_BATCH / (qmin_of_class c * Q_BATCH + Q_BATCH_BYTES)) in *.
    set (k := cfd_cntP c (cfd_qchunks (a_qloc st ++ a_qglob st))) in *.
    pose proof (Z.mul_nonneg_nonneg (F + Q_BATCH - k) (size_of_class c) ltac:(unfold Q_BATCH; lia) S0).
    lia.
Qed.

(* ---------- Per-class live counts (a Theorem Labs lane 08:02Z, 08:07Z) ---------- *)

(* a_class_count's filter is in_class at the block's user size: for a primary request needed_size is needed0. *)
Lemma in_class_needed0 : forall c n, is_primary n && (class_id (needed0 n) =? c) = in_class c n.
Proof. intros c n. unfold in_class, needed_size. destruct (is_primary n); reflexivity. Qed.

Lemma needed_size_prim : forall n, is_primary n = true -> needed_size n = needed0 n.
Proof. intros n Hp. unfold needed_size. rewrite Hp. reflexivity. Qed.

(* Every request of at most 8 bytes (negative ones too) needs 24 bytes: class 1. *)
Lemma needed0_small : forall n, n <= 8 -> needed0 n = 24.
Proof.
  intros n Hn. unfold needed0, rounded_size, rz_size, rz_log.
  rewrite Z.max_r by lia. rewrite (proj2 (Z.leb_le n 48)) by lia. reflexivity.
Qed.

(* The same statement as W6/ClassCons.v size_of_class_nonneg, which this file cannot see. *)
Lemma class_size_nonneg : forall c, 0 <= c -> 0 <= size_of_class c.
Proof.
  intros c Hc. unfold size_of_class.
  destruct (Z.leb_spec c 16) as [_|_]; [lia|].
  destruct (Z.eqb_spec c 31) as [_|_]; [lia|].
  set (t := Z.shiftl 512 (Z.shiftr (c - 16) 1)).
  assert (Ht : 0 <= t) by (apply (proj2 (Z.shiftl_nonneg 512 _)); lia).
  destruct (Z.odd (c - 16)).
  - pose proof (proj2 (Z.shiftr_nonneg t 1) Ht). lia.
  - exact Ht.
Qed.

(* The count: the number of primary blocks of class c in H. *)
Lemma a_class_count_in_class : forall H c,
  a_class_count H c = Z.of_nat (List.length (List.filter (fun qm => in_class c (snd qm)) H)).
Proof.
  intros H c. unfold a_class_count. do 2 f_equal. apply List.filter_ext. intros qm. cbv beta.
  apply in_class_needed0.
Qed.

Lemma a_class_count_nonneg : forall H c, 0 <= a_class_count H c.
Proof. intros H c. unfold a_class_count. lia. Qed.

(* A filter of H is no longer than H, so no class holds more blocks than the heap has (from lib/A/ClassEntry.v (not in this delivery),
   a Theorem Labs lane 12:55Z; a_class_entry_of_length below needs it). *)
Lemma a_class_count_le_length : forall H c, a_class_count H c <= Z.of_nat (List.length H).
Proof.
  intros H c. rewrite a_class_count_in_class. apply Nat2Z.inj_le, List.filter_length_le.
Qed.

Lemma a_class_count_nil : forall c, a_class_count [] c = 0.
Proof. reflexivity. Qed.

Lemma a_class_count_app : forall H1 H2 c, a_class_count (H1 ++ H2) c = a_class_count H1 c + a_class_count H2 c.
Proof. intros H1 H2 c. unfold a_class_count. rewrite List.filter_app, List.length_app. lia. Qed.

Lemma a_class_count_cons : forall q k H c,
  a_class_count ((q, k) :: H) c = (if in_class c k then 1 else 0) + a_class_count H c.
Proof.
  intros q k H c. unfold a_class_count. cbn [List.filter snd]. rewrite in_class_needed0.
  destruct (in_class c k); cbn [List.length]; lia.
Qed.

Lemma a_class_count_perm : forall H H' c, Permutation H H' -> a_class_count H c = a_class_count H' c.
Proof.
  intros H H' c HP. induction HP as [| [q k] l l' _ IH | [q1 k1] [q2 k2] l | l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - rewrite !a_class_count_cons, IH. reflexivity.
  - rewrite !a_class_count_cons. lia.
  - congruence.
Qed.

(* A duplicate-free list whose blocks all occur in L has at most L's count in every class (List.NoDup on the pairs;
   List.NoDup on the addresses implies it, a_class_bytes_incl_addr). List.NoDup, not stdpp's NoDup, which is the one
   the bare name means below `From stdpp Require Import gmap`; stdpp's NoDup_ListNoDup converts. *)
Lemma a_class_count_incl : forall (H' L : list (Z * Z)) c,
  List.NoDup H' -> incl H' L -> a_class_count H' c <= a_class_count L c.
Proof.
  intros H' L c HN HI. unfold a_class_count.
  assert (Hl : Nat.le (List.length (List.filter (fun qm => is_primary (snd qm) && (class_id (needed0 (snd qm)) =? c)) H'))
                 (List.length (List.filter (fun qm => is_primary (snd qm) && (class_id (needed0 (snd qm)) =? c)) L))).
  { apply List.NoDup_incl_length; [apply List.NoDup_filter; exact HN |].
    intros x Hx. apply List.filter_In in Hx as [Hx Hp]. apply List.filter_In. split; [apply HI; exact Hx | exact Hp]. }
  lia.
Qed.

Lemma a_class_bytes_count : forall H c, a_class_bytes H c = a_class_count H c * size_of_class c.
Proof. reflexivity. Qed.

Lemma a_class_bytes_nonneg : forall H c, 0 <= c -> 0 <= a_class_bytes H c.
Proof.
  intros H c Hc. unfold a_class_bytes.
  apply Z.mul_nonneg_nonneg; [apply a_class_count_nonneg | apply class_size_nonneg; exact Hc].
Qed.

(* The inequality form: N or fewer blocks of class c weigh at most N slots of class c. *)
Lemma a_class_bytes_le_count : forall H c N, 0 <= c -> a_class_count H c <= N ->
  a_class_bytes H c <= N * size_of_class c.
Proof.
  intros H c N Hc HN. unfold a_class_bytes.
  apply Z.mul_le_mono_nonneg_r; [apply class_size_nonneg; exact Hc | exact HN].
Qed.

Lemma a_class_bytes_nil : forall c, a_class_bytes [] c = 0.
Proof. reflexivity. Qed.

Lemma a_class_bytes_app : forall H1 H2 c, a_class_bytes (H1 ++ H2) c = a_class_bytes H1 c + a_class_bytes H2 c.
Proof. intros H1 H2 c. unfold a_class_bytes. rewrite a_class_count_app. apply Z.mul_add_distr_r. Qed.

Lemma a_class_bytes_cons : forall q k H c,
  a_class_bytes ((q, k) :: H) c = a_class_bytes H c + (if in_class c k then size_of_class c else 0).
Proof. intros q k H c. unfold a_class_bytes. rewrite a_class_count_cons. destruct (in_class c k); lia. Qed.

Lemma a_class_bytes_snoc : forall H q k c,
  a_class_bytes (H ++ [(q, k)]) c = a_class_bytes H c + (if in_class c k then size_of_class c else 0).
Proof.
  intros H q k c. rewrite a_class_bytes_app, a_class_bytes_cons, a_class_bytes_nil.
  destruct (in_class c k); lia.
Qed.

(* The addition form: the block (q, k) between H1 and H2 adds its slot to its class. *)
Lemma a_class_bytes_remove : forall H1 H2 q k c,
  a_class_bytes (H1 ++ (q, k) :: H2) c = a_class_bytes (H1 ++ H2) c + (if in_class c k then size_of_class c else 0).
Proof.
  intros H1 H2 q k c. rewrite !a_class_bytes_app, a_class_bytes_cons.
  destruct (in_class c k); lia.
Qed.

Lemma a_class_bytes_perm : forall H H' c, Permutation H H' -> a_class_bytes H c = a_class_bytes H' c.
Proof. intros H H' c HP. unfold a_class_bytes. rewrite (a_class_count_perm H H' c HP). reflexivity. Qed.

(* After a call, the heap H' is a duplicate-free selection from the entry heap H and the blocks T' the call
   allocated: per class, its slot bytes are at most those of H plus those of T'. List.NoDup is on the (address, size)
   pairs; incl may drop blocks of H ++ T', and List.NoDup lets H' repeat none. *)
Lemma a_class_bytes_incl : forall (H' H T' : list (Z * Z)) c,
  List.NoDup H' -> incl H' (H ++ T') -> 0 <= c < K_NUM_CLASSES ->
  a_class_bytes H' c <= a_class_bytes H c + a_class_bytes T' c.
Proof.
  intros H' H T' c HN HI Hc. rewrite <- a_class_bytes_app. unfold a_class_bytes.
  apply Z.mul_le_mono_nonneg_r; [apply class_size_nonneg; lia | exact (a_class_count_incl H' (H ++ T') c HN HI)].
Qed.

(* a_class_bytes_incl from duplicate-free addresses. *)
Lemma a_class_bytes_incl_addr : forall (H' H T' : list (Z * Z)) c,
  List.NoDup (List.map fst H') -> incl H' (H ++ T') -> 0 <= c < K_NUM_CLASSES ->
  a_class_bytes H' c <= a_class_bytes H c + a_class_bytes T' c.
Proof.
  intros H' H T' c HN HI Hc.
  apply a_class_bytes_incl; [eapply List.NoDup_map_inv; exact HN | exact HI | exact Hc].
Qed.

(* The contract premise a_class_req_fits from per-class counts: the live blocks of class c and the request's slot,
   counted in slots of class c. *)
Lemma a_class_req_fits_of_count : forall (Bc : Z -> Z) H n,
  (forall c, 0 <= c < K_NUM_CLASSES ->
     (a_class_count H c + (if in_class c n then 1 else 0)) * size_of_class c <= Bc c) ->
  a_class_req_fits Bc H n.
Proof.
  intros Bc H n HB c Hc. specialize (HB c Hc). unfold a_class_bytes.
  destruct (in_class c n); nia.
Qed.

(* The total slot bytes and user bytes of the live blocks (ClassConsDef.v a_slot_of, a_slot_bytes, a_user_bytes). *)
Lemma a_slot_of_nonneg : forall n, 0 <= a_slot_of n.
Proof.
  intros n. unfold a_slot_of. destruct (is_primary n) eqn:Hp; [| lia].
  destruct (Z_le_gt_dec 0 n) as [H0 | H0].
  - pose proof (AsanCtrlProps.primary_class_facts n H0 Hp) as P. cbn zeta in P. lia.
  - rewrite (needed_size_prim n Hp), (needed0_small n ltac:(lia)).
    assert (E : size_of_class (class_id 24) = 32) by reflexivity. rewrite E. lia.
Qed.

Lemma a_slot_of_le : forall n, 0 <= n -> a_slot_of n <= 2 * n + 32.
Proof.
  intros n Hn. unfold a_slot_of. destruct (is_primary n) eqn:Hp; [| lia].
  assert (Hn' : n <= 64512).
  { destruct (Z_le_gt_dec n 64512) as [Hle | Hgt]; [exact Hle |].
    rewrite (AsanCtrlProps.large_not_primary n ltac:(lia)) in Hp. discriminate. }
  apply crl_size_le_2n. lia.
Qed.

(* Per class, at most the total: the lemma for a unit that bounds only the total. *)
Lemma a_class_bytes_le_total : forall H c, a_class_bytes H c <= a_slot_bytes H.
Proof.
  intros H c. induction H as [| [q k] H IH].
  - rewrite a_class_bytes_nil. cbn [a_slot_bytes]. lia.
  - rewrite a_class_bytes_cons. cbn [a_slot_bytes].
    destruct (in_class c k) eqn:E.
    + unfold in_class in E. apply andb_prop in E as [Hp Hc]. apply Z.eqb_eq in Hc.
      unfold a_slot_of. rewrite Hp, Hc. lia.
    + pose proof (a_slot_of_nonneg k). lia.
Qed.

(* The total slot bytes from the user bytes: a primary slot of n bytes is at most 2 n + 32 (crl_size_le_2n). *)
Lemma a_slot_bytes_le_user : forall H, Forall (fun b => 0 <= snd b) H ->
  a_slot_bytes H <= 2 * a_user_bytes H + 32 * Z.of_nat (List.length H).
Proof.
  induction H as [| [q k] H IH]; intros HF; cbn [a_slot_bytes a_user_bytes List.length]; [lia |].
  apply Forall_cons_iff in HF as [Hk HF]. cbn [snd] in Hk. specialize (IH HF).
  pose proof (a_slot_of_le k Hk). lia.
Qed.

Lemma a_class_bytes_le_user : forall H c, Forall (fun b => 0 <= snd b) H ->
  a_class_bytes H c <= 2 * a_user_bytes H + 32 * Z.of_nat (List.length H).
Proof.
  intros H c HF. pose proof (a_class_bytes_le_total H c). pose proof (a_slot_bytes_le_user H HF). lia.
Qed.

(* class_id (needed0 n) is monotone over the primary requests: constant (class 1) up to 8 bytes (needed0_small), and
   checked one step at a time over 8 .. 64512. *)
Lemma class_needed0_steps :
  forallb (fun n => class_id (needed0 n) <=? class_id (needed0 (n + 1))) (AsanCtrlProps.zseq 8 (Z.to_nat 64504))
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_needed0_step : forall m, 8 <= m < 64512 -> class_id (needed0 m) <= class_id (needed0 (m + 1)).
Proof.
  intros m Hm. apply Z.leb_le.
  apply (AsanCtrlProps.forallb_zseq (fun n => class_id (needed0 n) <=? class_id (needed0 (n + 1))) 8
           (Z.to_nat 64504) class_needed0_steps).
  rewrite Z2Nat.id; lia.
Qed.

Lemma class_needed0_mono : forall d n, 8 <= n -> n + Z.of_nat d <= 64512 ->
  class_id (needed0 n) <= class_id (needed0 (n + Z.of_nat d)).
Proof.
  induction d as [| d IH]; intros n Hn Hd.
  - replace (n + Z.of_nat 0) with n by lia. lia.
  - pose proof (IH n Hn ltac:(lia)) as I.
    pose proof (class_needed0_step (n + Z.of_nat d) ltac:(lia)) as Hst.
    replace (n + Z.of_nat (S d)) with (n + Z.of_nat d + 1) by lia. lia.
Qed.

Lemma class_needed0_le : forall n m, n <= m <= 64512 -> class_id (needed0 n) <= class_id (needed0 m).
Proof.
  intros n m Hnm.
  destruct (Z_le_gt_dec n 8) as [Hn | Hn].
  - rewrite (needed0_small n Hn).
    destruct (Z_le_gt_dec m 8) as [Hm | Hm].
    + rewrite (needed0_small m Hm). lia.
    + assert (Hp : is_primary m = true) by (rewrite AsanCtrlProps.is_primary_iff by lia; apply Z.leb_le; lia).
      pose proof (AsanCtrlProps.primary_class_facts m ltac:(lia) Hp) as P. cbn zeta in P.
      rewrite (needed_size_prim m Hp) in P. change (class_id 24) with 1. lia.
  - pose proof (class_needed0_mono (Z.to_nat (m - n)) n ltac:(lia) ltac:(lia)) as M.
    rewrite Z2Nat.id in M by lia. replace (n + (m - n)) with m in M by lia. exact M.
Qed.

(* A secondary request's needed size is above 65536, and every size from 65536 up is in class 30 or above. *)
Lemma class_id_ge_30 : forall s, 65536 <= s -> 30 <= class_id s.
Proof.
  intros s Hs. unfold class_id. rewrite (proj2 (Z.leb_gt s 512)) by lia. cbv beta iota zeta.
  assert (Hl : 16 <= Z.log2 s) by (change 16 with (Z.log2 65536); apply Z.log2_le_mono; exact Hs).
  rewrite (Z.shiftl_mul_pow2 (Z.log2 s - 9) 1) by lia. change (2 ^ 1) with 2.
  assert (Hh : 0 <= Z.land (Z.shiftr s (Z.log2 s - 1)) 1) by (apply Z.land_nonneg; right; lia).
  destruct (Z.land s (Z.shiftl 1 (Z.log2 s - 1) - 1) =? 0); lia.
Qed.

(* The class of a primary request of n <= K bytes is at most the class of K's needed size, for every K: no side
   condition. For K <= 64512 (K primary) it is class_needed0_le; for K > 64512 (K secondary) the primary classes are
   at most class_id (needed0 64512) = 30 and class_id (needed_size K) >= 30 (class_id_ge_30). *)
Lemma class_prim_le : forall n K, n <= K -> is_primary n = true ->
  class_id (needed0 n) <= class_id (needed_size K).
Proof.
  intros n K HnK Hp.
  assert (Hn : n <= 64512).
  { destruct (Z_le_gt_dec n 64512) as [Hle | Hgt]; [exact Hle |].
    rewrite (AsanCtrlProps.large_not_primary n ltac:(lia)) in Hp. discriminate. }
  destruct (Z_le_gt_dec K 64512) as [HK | HK].
  - assert (HpK : is_primary K = true).
    { destruct (Z_le_gt_dec 0 K).
      - rewrite AsanCtrlProps.is_primary_iff by lia. apply Z.leb_le. exact HK.
      - unfold is_primary. rewrite needed0_small by lia. reflexivity. }
    rewrite (needed_size_prim K HpK). apply class_needed0_le. lia.
  - assert (HK0 : is_primary K = false) by (apply AsanCtrlProps.large_not_primary; lia).
    assert (Hs : 65536 <= needed_size K).
    { unfold needed_size. rewrite HK0. unfold is_primary, K_MAX_SIZE in HK0. apply Z.leb_gt in HK0.
      assert (0 <= rz_size K) by (unfold rz_size; apply Z.shiftl_nonneg; lia). lia. }
    pose proof (class_id_ge_30 _ Hs) as H30.
    pose proof (class_needed0_le n 64512 ltac:(lia)) as Hle.
    change (class_id (needed0 64512)) with 30 in Hle. lia.
Qed.

Lemma in_class_above : forall c n K, n <= K -> class_id (needed_size K) < c -> in_class c n = false.
Proof.
  intros c n K HnK Hc. rewrite <- in_class_needed0.
  destruct (is_primary n) eqn:Hp; [| reflexivity]. cbn [andb]. apply Z.eqb_neq.
  pose proof (class_prim_le n K HnK Hp). lia.
Qed.

(* The bridge: when every block of H has at most K user bytes, every class above class_id (needed_size K) is empty. *)
Lemma a_class_count_above : forall H K c,
  Forall (fun b => snd b <= K) H -> class_id (needed_size K) < c -> a_class_count H c = 0.
Proof.
  intros H K c HF Hc. revert HF. induction H as [| [q k] H IH]; intros HF; [reflexivity |].
  apply Forall_cons_iff in HF as [Hk HF]. cbn [snd] in Hk.
  rewrite a_class_count_cons, (IH HF), (in_class_above c k K Hk Hc). reflexivity.
Qed.

Theorem a_class_bytes_above : forall H K c,
  Forall (fun b => snd b <= K) H -> class_id (needed_size K) < c -> a_class_bytes H c = 0.
Proof. intros H K c HF Hc. unfold a_class_bytes. rewrite (a_class_count_above H K c HF Hc). reflexivity. Qed.

(* ---------- The per-class bound at an allocator call, for any unit (two Theorem Labs lanes 10:28Z) ---------- *)

(* A unit instantiates these lemmas with its own measured inputs instead of proving them again:
   - N c: the most live blocks of class c in the heap H0 at the slot's entry (a count, as a_class_count counts);
   - SP c: the slot's share, the slot bytes of class c that the blocks X the slot allocated, with the request, take.
   class_Bc N SP c = N c * size_of_class c + SP c is the per-class bound Bc of the allocator contracts (Contract.v
   amalloc_at, afree_at and the others). The pair lemmas need only the entry form a_class_bytes H0 c + SP c <= Bc c, so
   they take any Bc: class_slot_entry_count gives that form for Bc = class_Bc N SP from the count bound, and a unit
   whose live bound is in bytes gives its own Bc. The room row (the contracts' second per-class premise) is a
   hypothesis; class_room_of_rows discharges it with one vm_compute over the rows of W6/QSlot.v qslot_table. These are
   a Theorem Labs lane's fm_ lemmas (a working branch 38bbb9a757, fuzz_manifest's lib/A/Prog/slot_class_live.v) for any N, SP, Bc.

   For N c = 1 and SP c = size_of_class c (at most one live block per class at entry, one slot block at a time):
     Definition U_Bc : Z -> Z := class_Bc (fun _ => 1) size_of_class.
     Lemma U_room : forall c, 0 <= c < K_NUM_CLASSES ->
       U_Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF.
     Proof. apply class_room_of_rows. rewrite QSlot.qslot_table. vm_compute. reflexivity. Qed.
     (* malloc of n at the call heap H0 ++ [], from HN : forall c, 0 <= c < K_NUM_CLASSES -> a_class_count H0 c <= 1 *)
     class_call_pair U_Bc size_of_class H0 [] n (class_slot_entry_count (fun _ => 1) size_of_class H0 HN)
       (a_class_req_fits_one_slot n) U_room *)

Definition class_Bc (N SP : Z -> Z) (c : Z) : Z := N c * size_of_class c + SP c.

(* fm_slot_entry: the entry bound N c slots of class c is the slot's entry form for Bc = class_Bc N SP. *)
Lemma class_slot_entry : forall (N SP : Z -> Z) H,
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H c <= N c * size_of_class c) <->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H c + SP c <= class_Bc N SP c).
Proof. intros N SP H. unfold class_Bc. split; intros HE c Hc; specialize (HE c Hc); lia. Qed.

(* The same from the count bound (a_class_bytes_le_count). *)
Lemma class_slot_entry_count : forall (N SP : Z -> Z) H,
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_count H c <= N c) ->
  forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H c + SP c <= class_Bc N SP c.
Proof.
  intros N SP H HN. apply (proj1 (class_slot_entry N SP H)). intros c Hc.
  apply a_class_bytes_le_count; [lia | exact (HN c Hc)].
Qed.

(* fm_Bc_room: the room row of every class from a check over W6/QSlot.v qslot_table's rows (c, qmin_of_class c,
   QSLOT c, BC_MAX c). A unit proves the check by `rewrite QSlot.qslot_table. vm_compute. reflexivity.`; plain
   vm_compute also works, but it runs qmin_of_class's search for all 32 classes again. The check reads the row's
   QSLOT c, not BC_MAX c: the proof then never converts QSLOT c or BC_MAX c to its body at a variable c. Such a
   conversion makes the kernel walk qmin_of_class's search (W6/QSlot.v); a proof through BC_MAX c took 577 s at Qed. *)
Lemma class_room_of_rows : forall Bc : Z -> Z,
  forallb (fun r : Z * Z * Z * Z => let '(c, _, qs, _) := r in
             Bc c + qs + 8 * K_MAX_SIZE + 2 * K_USER_MAP <=? K_FREEARR_OFF)
    (map (fun c => (c, qmin_of_class c, QSLOT c, BC_MAX c)) (AsanCtrlProps.zseq 0 (Z.to_nat 32))) = true ->
  forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF.
Proof.
  intros Bc HB c Hc.
  assert (Hin : In (c, qmin_of_class c, QSLOT c, BC_MAX c)
                  (map (fun c => (c, qmin_of_class c, QSLOT c, BC_MAX c)) (AsanCtrlProps.zseq 0 (Z.to_nat 32)))).
  { apply (in_map (fun c => (c, qmin_of_class c, QSLOT c, BC_MAX c))). apply AsanCtrlProps.zseq_spec.
    unfold K_NUM_CLASSES in Hc. rewrite Z2Nat.id by lia. lia. }
  pose proof (proj1 (forallb_forall _ _) HB _ Hin) as HR. cbv beta iota in HR. apply Z.leb_le in HR. exact HR.
Qed.

(* fm_slot_call_bound: the entry form on the slot's entry heap H0 and the share SP on the slot's blocks X bound every
   class of the heap H0 ++ X by Bc (afree_null_contract's premise, class_room_of_live_per_class's live bound). *)
Lemma class_call_bound : forall (Bc SP : Z -> Z) H0 X,
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H0 c + SP c <= Bc c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes X c <= SP c) ->
  forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes (H0 ++ X) c <= Bc c.
Proof.
  intros Bc SP H0 X HE HX c Hc. rewrite a_class_bytes_app. specialize (HE c Hc). specialize (HX c Hc). lia.
Qed.

(* fm_call_pair: malloc of n at the call heap H0 ++ X. The contract's a_class_req_fits Bc and the room row, from the
   entry form and the share SP on X with the request's slot. *)
Lemma class_call_pair : forall (Bc SP : Z -> Z) H0 X n,
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H0 c + SP c <= Bc c) ->
  a_class_req_fits SP X n ->
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF) ->
  a_class_req_fits Bc (H0 ++ X) n /\
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF).
Proof.
  intros Bc SP H0 X n HE HX HR. split; [| exact HR].
  unfold a_class_req_fits in *. intros c Hc. rewrite a_class_bytes_app.
  specialize (HE c Hc). specialize (HX c Hc). lia.
Qed.

(* The block malloc of n records is (q, Z.max n 1) (Contract.v a_size). Below 1 byte every request needs 24 bytes
   (needed0_small), so the block is in the class of n. *)
Lemma in_class_max1 : forall c n, in_class c (Z.max n 1) = in_class c n.
Proof.
  intros c n. destruct (Z.le_gt_cases 1 n) as [H1 | H1].
  - rewrite Z.max_l by lia. reflexivity.
  - rewrite Z.max_r by lia. unfold in_class, needed_size, is_primary.
    rewrite (needed0_small 1), (needed0_small n) by lia. reflexivity.
Qed.

(* fm_req_fits_iff: a_class_req_fits Bc H n is the bound Bc on the heap after the request, H ++ [(q, Z.max n 1)],
   for every address q. *)
Lemma a_class_req_fits_snoc : forall (Bc : Z -> Z) H q n,
  a_class_req_fits Bc H n <->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes (H ++ [(q, Z.max n 1)]) c <= Bc c).
Proof.
  intros Bc H q n. unfold a_class_req_fits.
  split; intros HF c Hc; specialize (HF c Hc); rewrite a_class_bytes_snoc, in_class_max1 in *; exact HF.
Qed.

(* fm_call_pair_l: class_call_pair with the share SP on the slot's blocks after the request, X ++ [(q, Z.max n 1)],
   as one list. *)
Lemma class_call_pair_l : forall (Bc SP : Z -> Z) H0 X q n,
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H0 c + SP c <= Bc c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes (X ++ [(q, Z.max n 1)]) c <= SP c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF) ->
  a_class_req_fits Bc (H0 ++ X) n /\
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF).
Proof.
  intros Bc SP H0 X q n HE HX HR.
  exact (class_call_pair Bc SP H0 X n HE (proj2 (a_class_req_fits_snoc SP X q n) HX) HR).
Qed.

(* fm_free_pair: free of (p, n) at the call heap (H0 ++ X1) ++ (p, n) :: X2 (afree_at's H1 ++ (p, n) :: H2, the block
   one of the slot's): the bound Bc on the call heap and the room row. *)
Lemma class_free_pair : forall (Bc SP : Z -> Z) H0 X1 p n X2,
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H0 c + SP c <= Bc c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes (X1 ++ (p, n) :: X2) c <= SP c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes ((H0 ++ X1) ++ (p, n) :: X2) c <= Bc c) /\
  (forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF).
Proof.
  intros Bc SP H0 X1 p n X2 HE HX HR. rewrite <- app_assoc.
  exact (conj (class_call_bound Bc SP H0 (X1 ++ (p, n) :: X2) HE HX) HR).
Qed.

(* The share SP = size_of_class (one slot block at a time): the request alone, and one live block. *)
Lemma a_class_req_fits_one_slot : forall n, a_class_req_fits size_of_class [] n.
Proof.
  intros n c Hc. rewrite a_class_bytes_nil. pose proof (class_size_nonneg c (proj1 Hc)).
  destruct (in_class c n); lia.
Qed.

Lemma a_class_bytes_one_le : forall q k c, 0 <= c < K_NUM_CLASSES -> a_class_bytes [(q, k)] c <= size_of_class c.
Proof.
  intros q k c Hc. rewrite a_class_bytes_cons, a_class_bytes_nil. pose proof (class_size_nonneg c (proj1 Hc)).
  destruct (in_class c k); lia.
Qed.

(* The per-class room row as one shared definition (a Theorem Labs lane 14:06Z, a Theorem Labs lane 14:07Z): the inline premise
   `forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF` above, by name.
   Additive: no statement in this file changes. *)
Definition bc_row (Bc : Z -> Z) : Prop :=
  forall c, 0 <= c < K_NUM_CLASSES -> Bc c + QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP <= K_FREEARR_OFF.
Definition cap_row (CAP : Z -> Z) : Prop := bc_row (fun c => CAP c * size_of_class c).

(* A class index outside [0, K_NUM_CLASSES) holds no live bytes: every primary request's class is in [1, 30]
   (a Theorem Labs lane 14:18Z; proof by a_class_bytes_out_check.v (not in this delivery)). Additive. *)
Lemma crl_prim_class_in : forall n, is_primary n = true -> 1 <= class_id (needed0 n) <= 30.
Proof.
  intros n Hp. destruct (Z_le_dec 0 n) as [Hn | Hn].
  - pose proof (AsanCtrlProps.primary_class_facts n Hn Hp) as P. cbn zeta in P.
    unfold needed_size in P. rewrite Hp in P. lia.
  - assert (E : needed0 n = 24).
    { unfold needed0, rounded_size, rz_size, rz_log. rewrite Z.max_r by lia.
      rewrite (proj2 (Z.leb_le n 48)) by lia. reflexivity. }
    rewrite E. vm_compute. split; discriminate.
Qed.

Lemma a_class_bytes_out : forall H c, ~ (0 <= c < K_NUM_CLASSES) -> a_class_bytes H c = 0.
Proof.
  intros H c Hc. unfold a_class_bytes, a_class_count.
  replace (List.filter _ H) with (@nil (Z * Z)); [reflexivity |].
  induction H as [| [q k] H IH]; [reflexivity |]. cbn [List.filter snd].
  destruct (is_primary k) eqn:Hp; cbn [andb]; [| exact IH].
  pose proof (crl_prim_class_in k Hp) as R. unfold K_NUM_CLASSES in Hc.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. exact IH.
Qed.

(* ---------- The per-class entry premise from a driver's fact (a Theorem Labs lane 12:47Z, from ClassEntry.v (not in this delivery)) ---------- *)

(* The arithmetic core, over an OPAQUE class-byte value acb, so a unit whose a_class_bytes is a Section parameter
   (pcap) instantiates acb with it. It is not stated over a_class_bytes, so no lemma above applies: lia. *)
Lemma a_class_entry_arith : forall (acb Kc sc SPc Bcc : Z),
  acb <= Kc * sc -> Bcc = Kc * sc + SPc -> acb + SPc <= Bcc.
Proof. intros acb Kc sc SPc Bcc Hb HB. lia. Qed.

(* The length form, the shape a driver proves (fuzz_disco: (length H0 <= 2)%nat): a_class_count_le_length, then
   a_class_bytes_le_count and a_class_entry_arith. One class c with only 0 <= c, so not class_slot_entry_count, which
   asks the count bound at every class below K_NUM_CLASSES. *)
Lemma a_class_entry_of_length : forall (SP Bc : Z -> Z) H c k,
  0 <= c ->
  (List.length H <= k)%nat ->
  Bc c = Z.of_nat k * size_of_class c + SP c ->
  a_class_bytes H c + SP c <= Bc c.
Proof.
  intros SP Bc H c k Hc Hlen HB.
  refine (a_class_entry_arith (a_class_bytes H c) (Z.of_nat k) (size_of_class c) (SP c) (Bc c) _ HB).
  apply a_class_bytes_le_count; [exact Hc |].
  etransitivity; [apply a_class_count_le_length | apply Nat2Z.inj_le, Hlen].
Qed.

(* What the allocator contracts consume for a request of size n: the entry premise and a share SP that covers one
   slot of the requested class give a_class_req_fits at the same Bc. The share must be non-negative: at a class the
   request is not in, the contract asks a_class_bytes H c + 0 <= Bc c. Through the heap after the request
   (a_class_req_fits_snoc, both ways) and class_call_bound with X the request's one block. *)
Lemma a_class_req_fits_entry : forall (SP Bc : Z -> Z) H n,
  (forall c, 0 <= c < K_NUM_CLASSES -> 0 <= SP c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H c + SP c <= Bc c) ->
  (forall c, 0 <= c < K_NUM_CLASSES -> in_class c n = true -> size_of_class c <= SP c) ->
  a_class_req_fits Bc H n.
Proof.
  intros SP Bc H n Hsp Hentry Hslot.
  apply (proj2 (a_class_req_fits_snoc Bc H 0 n)).
  apply (class_call_bound Bc SP H [(0, Z.max n 1)] Hentry).
  apply (proj1 (a_class_req_fits_snoc SP [] 0 n)).
  intros c Hc. rewrite a_class_bytes_nil. specialize (Hsp c Hc). specialize (Hslot c Hc).
  destruct (in_class c n); [specialize (Hslot eq_refl) |]; lia.
Qed.
