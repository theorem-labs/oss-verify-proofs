(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/SpecA/AsanCtrl.v; 229 of its 252 lines of code are new or changed and 366 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, Spec: P8 part C, the allocator interface the per-class room bound needs (h-hpreset-7's
   port of asan_halts, piece P8; c-frame-alloc).

   WHAT IT SAYS. An allocation of a primary request r (needed size <= 64 KiB) of class c returns NULL only when every
   slot of c's region is taken: live chunks of c, chunks of c in the quarantine, the quarantine's batch records (they
   are class-24 chunks, K_BATCH_CLASS), and the refill a cache takes at once. The quarantine holds at most
   Q_MAX + Q_CACHE accounted bytes, a chunk of request q accounting q bytes and its batch's share of 8192 bytes per
   at most 1021 chunks, so at least q + 8. So a class-c count of quarantined chunks is at most QT / (lo_c + 8), lo_c the
   least request of c, and the batch records at most QT / 8192 + 1.

   It is stated over an abstract allocator state (room_state): the instance is the port's allocator model (h-mani-a8's
   lib/Reusable/YG0dcf.v record type when it lands; the kit's lib/AZ/Spec/AsanCtrl.v enqueue / drain / recycle /
   cache_alloc / populate_free_array is the lineage). The class map below is AsanCtrl.v's text (size_of_class,
   class_id, rz_log, rz_size, rounded_size, needed0, is_primary, max_cached, K_FREEARR_OFF, Q_MAX, Q_CACHE).

   Secondary allocations (needed size > 64 KiB) are outside this interface: their NULL is an mmap refusal of the
   environment, not a full class.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Permutation.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ the class map (AsanCtrl.v) *)

Definition K_FREEARR_OFF : Z := 0xE0000000.
Definition K_MAX_SIZE : Z := 0x10000.
Definition K_BATCH_CLASS : Z := 24.
Definition Q_MAX : Z := 0x10000000.
Definition Q_CACHE : Z := 0x100000.
Definition Q_BATCH : Z := 1021.
Definition Q_BATCH_BYTES : Z := 8192.
Definition QT : Z := Q_MAX + Q_CACHE.

Definition rup (x a : Z) : Z := ((x + a - 1) / a) * a.
Definition size_of_class (c : Z) : Z :=
  if c <=? 16 then 32 * c
  else if c =? 31 then 64
  else let t := Z.shiftl 512 (Z.shiftr (c - 16) 1) in
       if Z.odd (c - 16) then t + Z.shiftr t 1 else t.
Definition class_id (s : Z) : Z :=
  if s <=? 512 then Z.shiftr (s + 31) 5
  else let l := Z.log2 s in
       let hbits := Z.land (Z.shiftr s (l - 1)) 1 in
       let lbits := Z.land s (Z.shiftl 1 (l - 1) - 1) in
       16 + Z.shiftl (l - 9) 1 + hbits + (if lbits =? 0 then 0 else 1).
Definition max_cached (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / size_of_class c)).
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := Z.shiftl 16 (rz_log n).
Definition rounded_size (n : Z) : Z := rup (Z.max n 8) 8.
Definition needed0 (n : Z) : Z := rounded_size n + rz_size n.
Definition is_primary (n : Z) : bool := needed0 n <=? K_MAX_SIZE.

(* the class of request n, when primary *)
Definition cls (n : Z) : option Z := if is_primary n then Some (class_id (needed0 n)) else None.
Definition in_cls (c n : Z) : bool := match cls n with Some c' => c' =? c | None => false end.

(* slots of class c: user part K_FREEARR_OFF of its 4 GiB region (populate_free_array refuses beyond it) *)
Definition cap (c : Z) : Z := K_FREEARR_OFF / size_of_class c.
(* the chunks a cache refill takes from the free array or the carve (cache_alloc: max_count / 2) *)
Definition refill (c : Z) : Z := max_cached c / 2.

(* ================================================================ the least request of a class *)

(* lo c: the least request in class c, found by a scan of 1 .. K_MAX_SIZE (every primary request is there) *)
Fixpoint scan_lo (c : Z) (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => K_MAX_SIZE + 1
  | S f => if in_cls c n then n else scan_lo c (n + 1) f
  end.
Definition lo (c : Z) : Z := scan_lo c 1 (Z.to_nat K_MAX_SIZE).

Lemma scan_lo_le : forall c f n m, n <= m < n + Z.of_nat f -> in_cls c m = true -> scan_lo c n f <= m.
Proof.
  intros c f. induction f as [|f IH]; intros n m Hm Hc; [lia|].
  cbn [scan_lo]. destruct (in_cls c n) eqn:E; [lia|].
  destruct (Z.eq_dec m n) as [->|Hne]; [congruence|]. apply IH; [lia|exact Hc].
Qed.

Lemma cls_small : forall n, 1 <= n -> is_primary n = true -> n <= K_MAX_SIZE.
Proof.
  intros n Hn H. unfold is_primary, needed0, rounded_size, rz_size, rup in H. apply Z.leb_le in H.
  assert (0 <= Z.shiftl 16 (rz_log n)) by (rewrite Z.shiftl_nonneg; lia).
  assert (Z.max n 8 <= (Z.max n 8 + 8 - 1) / 8 * 8).
  { pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
  lia.
Qed.

Lemma lo_le : forall c n, 1 <= n -> in_cls c n = true -> lo c <= n.
Proof.
  intros c n Hn H. unfold lo. apply scan_lo_le; [|exact H].
  unfold in_cls, cls in H. destruct (is_primary n) eqn:Ep; [|discriminate].
  pose proof (cls_small n Hn Ep). rewrite Z2Nat.id by (unfold K_MAX_SIZE; lia). lia.
Qed.

(* ================================================================ the interface *)

Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | z :: r => z + zsum r end.
Definition ccnt (c : Z) (l : list Z) : nat := length (filter (in_cls c) l).

(* an allocator state as the room bound sees it: the live requests (RAW sizes), the quarantined chunks (ACCOUNTED
   sizes, acct_size below: ASan's Allocate serves malloc(0) as a 1-byte request) and the number of batch records the
   quarantine holds. The class of a request is the class of its accounted size (cls_acct), so every class count below
   is the same over raw or accounted sizes; only the byte sums differ. *)
Record room_state : Type := { rs_live : list Z; rs_quar : list Z; rs_batches : Z }.

Definition acct_size (n : Z) : Z := Z.max n 1.

(* the facts the instance proves of its model (h-mani-a8, lib/Reusable/YGcfRoom.v, 2026-10-28). The quarantine's
   accounted bytes at an allocation's entry (every earlier free done, with its drain and recycle): the quarantined
   chunks plus Q_BATCH_BYTES per batch record, at most Q_MAX (the global part, after a recycle at most Q_MIN) plus
   Q_CACHE (the thread's part, drained above it); and a batch holds at most Q_BATCH chunks. *)
Definition quar_bytes_ok (s : room_state) : Prop :=
  Forall (fun q => 1 <= q) (rs_quar s) /\ 0 <= rs_batches s /\
  Z.of_nat (length (rs_quar s)) <= Q_BATCH * rs_batches s /\
  zsum (rs_quar s) + Q_BATCH_BYTES * rs_batches s <= QT.
(* class n's class is full. The instance proves it of a primary NULL ONLY UNDER THE GRANT FLAG g = true (atok_cf's
   flag: the last environment answer of the call was a grant; a call that asks nothing keeps its entry flag):
     g = true -> (the call returned NULL) -> null_full s n          (YGcfRoom.malloc_cf_null_full)
   Without the flag it is FALSE: a refused KMapUser or KMapFreeArray also returns NULL, with room in the class. So the
   theorems below conclude g = false (the NULL is an environment refusal), and a consumer rules the NULL out with a
   grant fact (c-asan's sec_grant_exists / forced_only). *)
Definition null_full (s : room_state) (n : Z) : Prop :=
  forall c, cls n = Some c ->
  Z.of_nat (ccnt c (rs_live s)) + Z.of_nat (ccnt c (rs_quar s)) +
  (if c =? K_BATCH_CLASS then rs_batches s else 0) + refill c > cap c.

(* every request up to 8 bytes has the same needed size, so the same class *)
Lemma cls_le8 : forall n, n <= 8 -> cls n = cls 1.
Proof.
  intros n Hn. unfold cls, is_primary, needed0, rounded_size, rz_size, rz_log.
  rewrite (Z.max_r n 8) by lia. replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma cls_acct : forall n, cls (acct_size n) = cls n.
Proof.
  intros n. unfold acct_size. destruct (Z.le_gt_cases n 1).
  - rewrite Z.max_r by lia. rewrite (cls_le8 n) by lia. reflexivity.
  - rewrite Z.max_l by lia. reflexivity.
Qed.

Lemma in_cls_acct : forall c n, in_cls c (acct_size n) = in_cls c n.
Proof. intros c n. unfold in_cls. rewrite (cls_acct n). reflexivity. Qed.

(* the per-class room a consumer allocation of class c needs: live count plus the quarantine's most plus the batch
   records' most plus the refill *)
Definition room_ok (c : Z) (live : Z) : Prop :=
  live + QT / (lo c + 8) + (if c =? K_BATCH_CLASS then QT / Q_BATCH_BYTES else 0) + refill c <= cap c.

Lemma ccnt_quar_le : forall c l, Forall (fun q => 1 <= q) l ->
  Z.of_nat (ccnt c l) * (lo c + 8) <= zsum (map (fun q => q + 8) l).
Proof.
  intros c l. induction l as [|q l IH]; intros HF; [cbn; lia|].
  inversion HF as [|? ? Hq HF']; subst. unfold ccnt in *. cbn [filter map zsum].
  destruct (in_cls c q) eqn:E.
  - cbn [length]. pose proof (lo_le c q Hq E). specialize (IH HF'). lia.
  - specialize (IH HF'). assert (0 <= q + 8) by lia. lia.
Qed.

Lemma lo_pos : forall c, 1 <= lo c.
Proof.
  intros c. unfold lo. generalize (Z.to_nat K_MAX_SIZE). intros f.
  assert (H : forall f n, 1 <= n -> 1 <= scan_lo c n f).
  { induction f0 as [|f0 IH]; intros n Hn; cbn [scan_lo]; [unfold K_MAX_SIZE; lia|].
    destruct (in_cls c n); [lia|apply IH; lia]. }
  apply H. lia.
Qed.

Lemma zsum_map8 : forall l, zsum (map (fun q => q + 8) l) = zsum l + 8 * Z.of_nat (length l).
Proof. induction l as [|q l IH]; cbn [map zsum length]; [lia|]. rewrite IH. lia. Qed.

Lemma zsum_nonneg : forall l, Forall (fun q => 1 <= q) l -> 0 <= zsum l.
Proof. induction l as [|q l IH]; intros H; cbn; [lia|]. inversion H; subst. specialize (IH H3). lia. Qed.

(* room_ok at a consumer allocation and quar_bytes_ok: the class is not full *)
Lemma not_full_of_room : forall s n c,
  quar_bytes_ok s -> null_full s n -> cls n = Some c ->
  room_ok c (Z.of_nat (ccnt c (rs_live s))) -> False.
Proof.
  intros s n c (Hq1 & Hb0 & Hqn & Hq) Hn Hc Hr. specialize (Hn c Hc). unfold room_ok in Hr.
  pose proof (ccnt_quar_le c (rs_quar s) Hq1) as Hcq. pose proof (lo_pos c) as Hlo.
  rewrite zsum_map8 in Hcq. pose proof (zsum_nonneg _ Hq1) as Hz.
  assert (H8 : zsum (rs_quar s) + 8 * Z.of_nat (length (rs_quar s)) <= QT)
    by (unfold Q_BATCH, Q_BATCH_BYTES in *; lia).
  assert (Hqc : Z.of_nat (ccnt c (rs_quar s)) <= QT / (lo c + 8)) by (apply Z.div_le_lower_bound; lia).
  assert (Hbc : rs_batches s <= QT / Q_BATCH_BYTES)
    by (apply Z.div_le_lower_bound; unfold Q_BATCH_BYTES in *; lia).
  destruct (c =? K_BATCH_CLASS); lia.
Qed.

(* THE COMPOSITION, in the instance's flag form: room_ok at a consumer allocation and the instance's facts leave only
   an environment refusal (g = false) as the cause of a NULL *)
Theorem no_null_of_room : forall (g : bool) (null : Prop) s n c,
  quar_bytes_ok s -> (g = true -> null -> null_full s n) -> cls n = Some c ->
  room_ok c (Z.of_nat (ccnt c (rs_live s))) -> null -> g = false.
Proof.
  intros g null s n c Hq Hn Hc Hr Hnull. destruct g; [|reflexivity].
  exfalso. exact (not_full_of_room s n c Hq (Hn eq_refl Hnull) Hc Hr).
Qed.

(* ================================================================ D2: the quarantine is a FIFO window of the frees

   The third fact the instance proves: the quarantine is a SUFFIX of the history of frees (oldest first, each free's
   ACCOUNTED size acct_size; YGcfRoom.quar_fifo_cf). In the kit's model it is: enqueue appends to the newest batch,
   drain appends whole batches, recycle removes the OLDEST batches (dequeue_while on the head of a_qglob), and a chunk
   above Q_MAX is never quarantined. With quar_bytes_ok (each quarantined chunk accounts at least q + 8), a flush F
   (frees of no class-17 chunk) that lies between the older frees A and the newer frees X leaves room in the window for
   only (QT - bytes (F) - bytes (X)) / (lo 17 + 8) older class-17 chunks: that is P8's flush argument at the round
   trips, with F a NAMED term (the harness fix #396 changes what F is, not this lemma). quar17_flush states it over
   the accounted history; quar17_flush_raw over the RAW free sizes (accounted bytes are at least the raw bytes, and
   the classes are the same), which is the form the model's frees and PresetFlush's byte bounds have. *)

Definition fifo_ok (hist quar : list Z) : Prop := exists pre suf, hist = pre ++ suf /\ Permutation.Permutation suf quar.

Definition zsum8 (l : list Z) : Z := zsum (map (fun q => q + 8) l).

Lemma ccnt_app : forall c a b, ccnt c (a ++ b) = (ccnt c a + ccnt c b)%nat.
Proof. intros c a b. unfold ccnt. rewrite filter_app, length_app. reflexivity. Qed.

Lemma ccnt_perm : forall c a b, Permutation.Permutation a b -> ccnt c a = ccnt c b.
Proof.
  intros c a b H. unfold ccnt. induction H as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; cbn [filter].
  - reflexivity.
  - destruct (in_cls c x); cbn [length]; lia.
  - destruct (in_cls c x), (in_cls c y); cbn [length]; lia.
  - lia.
Qed.

Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a as [|x a IH]; intros b; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma zsum8_app : forall a b, zsum8 (a ++ b) = zsum8 a + zsum8 b.
Proof. intros a b. unfold zsum8. rewrite map_app. apply zsum_app. Qed.

Lemma zsum_perm : forall a b, Permutation.Permutation a b -> zsum a = zsum b.
Proof. intros a b H. induction H; cbn; lia. Qed.

Lemma zsum8_nonneg : forall l, Forall (fun q => 1 <= q) l -> 0 <= zsum8 l.
Proof. intros l H. unfold zsum8. rewrite zsum_map8. pose proof (zsum_nonneg l H). lia. Qed.

Lemma ccnt_none : forall c l, Forall (fun q => in_cls c q = false) l -> ccnt c l = 0%nat.
Proof.
  intros c l H. unfold ccnt. induction H as [|q l Hq _ IH]; [reflexivity|]. cbn [filter]. rewrite Hq. exact IH.
Qed.

(* a suffix of A ++ F ++ X is a suffix of X, or (a suffix of F) ++ X, or (a suffix of A) ++ F ++ X *)
Lemma suffix3 : forall A F X pre suf : list Z, A ++ F ++ X = pre ++ suf ->
  (exists p, X = p ++ suf) \/ (exists f1 f2, F = f1 ++ f2 /\ suf = f2 ++ X) \/
  (exists a1 a2, A = a1 ++ a2 /\ suf = a2 ++ F ++ X).
Proof.
  intros A F X pre suf H. apply app_eq_app in H as [l [[H1 H2] | [H1 H2]]].
  - (* A = pre ++ l, suf = l ++ F ++ X *)
    right; right. exists pre, l. split; [exact H1|exact H2].
  - (* pre = A ++ l, F ++ X = l ++ suf *)
    apply app_eq_app in H2 as [m [[H3 H4] | [H3 H4]]].
    + right; left. exists l, m. split; [exact H3|exact H4].
    + left. exists m. exact H4.
Qed.

(* THE FLUSH LEMMA *)
Theorem quar17_flush : forall hist quar A F X,
  fifo_ok hist quar -> Forall (fun q => 1 <= q) hist -> zsum8 quar <= QT ->
  hist = A ++ F ++ X -> Forall (fun q => in_cls 17 q = false) F ->
  Z.of_nat (ccnt 17 quar) <= Z.of_nat (ccnt 17 X) + Z.max 0 (QT - zsum8 F - zsum8 X) / (lo 17 + 8).
Proof.
  intros hist quar A F X (pre & suf & Hh & Hp) Hpos Hq Hd HF.
  rewrite <- (ccnt_perm 17 suf quar Hp).
  assert (Hq' : zsum8 suf <= QT).
  { unfold zsum8 in *. rewrite (zsum_perm (map (fun q => q + 8) suf) (map (fun q => q + 8) quar))
      by (apply Permutation.Permutation_map; exact Hp). exact Hq. }
  clear Hq. rename Hq' into Hq. rewrite Hh in Hd. pose proof (lo_pos 17) as Hlo.
  assert (Hdiv : forall a, 0 <= Z.max 0 a / (lo 17 + 8)) by (intros a; apply Z.div_pos; lia).
  assert (HposX : Forall (fun q => 1 <= q) suf) by (rewrite Hh in Hpos; apply Forall_app in Hpos; tauto).
  destruct (suffix3 A F X pre suf (eq_sym Hd)) as [(p & HX) | [(f1 & f2 & HF1 & Hs) | (a1 & a2 & HA & Hs)]].
  - (* the window is inside X *)
    assert (ccnt 17 suf <= ccnt 17 X)%nat by (rewrite HX, ccnt_app; lia).
    specialize (Hdiv (QT - zsum8 F - zsum8 X)). lia.
  - (* the window is a part of F, then X *)
    subst suf. rewrite ccnt_app.
    rewrite HF1 in HF. apply Forall_app in HF as [_ HF2]. rewrite (ccnt_none 17 f2 HF2).
    specialize (Hdiv (QT - zsum8 F - zsum8 X)). lia.
  - (* the window reaches into A: F and X are all in it *)
    subst suf. rewrite !ccnt_app, (ccnt_none 17 F HF). rewrite !zsum8_app in Hq.
    apply Forall_app in HposX as [Ha2 _].
    pose proof (ccnt_quar_le 17 a2 Ha2) as Hc. fold (zsum8 a2) in Hc.
    assert (Z.of_nat (ccnt 17 a2) <= Z.max 0 (QT - zsum8 F - zsum8 X) / (lo 17 + 8)).
    { apply Z.div_le_lower_bound; [lia|]. rewrite Z.max_r by (pose proof (zsum8_nonneg a2 Ha2); lia). lia. }
    lia.
Qed.

(* quar_bytes_ok gives the window's byte bound used above *)
Lemma quar_zsum8 : forall s, quar_bytes_ok s -> zsum8 (rs_quar s) <= QT.
Proof.
  intros s (Hq1 & Hb0 & Hqn & Hq). unfold zsum8. rewrite zsum_map8. unfold Q_BATCH, Q_BATCH_BYTES in *. lia.
Qed.

Lemma Forall_acct_pos : forall l, Forall (fun q => 1 <= q) (map acct_size l).
Proof. induction l as [|q l IH]; cbn; constructor; [unfold acct_size; lia|exact IH]. Qed.

Lemma ccnt_acct : forall c l, ccnt c (map acct_size l) = ccnt c l.
Proof.
  intros c l. unfold ccnt. induction l as [|q l IH]; [reflexivity|].
  cbn [map filter]. rewrite (in_cls_acct c q). destruct (in_cls c q); cbn [length]; lia.
Qed.

Lemma zsum8_acct_ge : forall l, zsum8 l <= zsum8 (map acct_size l).
Proof.
  unfold zsum8. induction l as [|q l IH]; cbn [map zsum]; [lia|]. unfold acct_size at 1. lia.
Qed.

Lemma zsum8_acct_nonneg : forall l, 0 <= zsum8 (map acct_size l).
Proof. intros l. apply zsum8_nonneg, Forall_acct_pos. Qed.

(* THE FLUSH LEMMA over the raw free sizes; the instance's history is their accounted sizes. The window term keeps
   the flush F raw (PresetFlush bounds its raw bytes) and the later frees X accounted (at least their raw bytes, and
   never negative). *)
Theorem quar17_flush_raw : forall frees quar A F X,
  fifo_ok (map acct_size frees) quar -> zsum8 quar <= QT ->
  frees = A ++ F ++ X -> Forall (fun q => in_cls 17 q = false) F ->
  Z.of_nat (ccnt 17 quar) <= Z.of_nat (ccnt 17 X) + Z.max 0 (QT - zsum8 F - zsum8 (map acct_size X)) / (lo 17 + 8).
Proof.
  intros frees quar A F X Hf Hq Hd HF. subst frees.
  assert (HF' : Forall (fun q => in_cls 17 q = false) (map acct_size F)).
  { apply Forall_map. apply Forall_forall. intros q Hin.
    rewrite (in_cls_acct 17 q). exact (proj1 (Forall_forall _ _) HF q Hin). }
  pose proof (quar17_flush (map acct_size (A ++ F ++ X)) quar (map acct_size A) (map acct_size F) (map acct_size X)
    Hf (Forall_acct_pos _) Hq ltac:(rewrite !map_app; reflexivity) HF') as H.
  rewrite (ccnt_acct 17 X) in H.
  pose proof (zsum8_acct_ge F). pose proof (lo_pos 17).
  assert (Z.max 0 (QT - zsum8 (map acct_size F) - zsum8 (map acct_size X)) / (lo 17 + 8) <=
          Z.max 0 (QT - zsum8 F - zsum8 (map acct_size X)) / (lo 17 + 8)) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* ================================================================ the state-shaped consumption point

   room_at s c is what a consumer of P8 states at the ENTRY STATE of an allocating call: a free slot of class c, i.e.
   live plus quarantined plus (for the batch class) the quarantine's batch records plus the refill within the cap. It
   is exactly the negation of null_full, so no_null_of_room_at needs no quarantine arithmetic; it takes the
   instance's NULL fact in its flag form and concludes that the NULL was an environment refusal (g = false). P8's
   theorems conclude room_at at every consumer allocation of the model run (PresetRun.hruns / hcons), from the
   instance's three facts (quar_bytes_ok, fifo_ok of its accounted free history, its live requests = the model's plus
   the driver's blocks). *)
Definition room_at (s : room_state) (c : Z) : Prop :=
  Z.of_nat (ccnt c (rs_live s)) + Z.of_nat (ccnt c (rs_quar s)) +
  (if c =? K_BATCH_CLASS then rs_batches s else 0) + refill c <= cap c.

Theorem no_null_of_room_at : forall (g : bool) (null : Prop) s n c,
  (g = true -> null -> null_full s n) -> cls n = Some c -> room_at s c -> null -> g = false.
Proof.
  intros g null s n c Hn Hc Hr Hnull. destruct g; [|reflexivity].
  exfalso. specialize (Hn eq_refl Hnull c Hc). unfold room_at in Hr. lia.
Qed.

(* the crude form gives room_at for every class whose room_ok holds *)
Theorem room_at_of_room_ok : forall s c, quar_bytes_ok s -> room_ok c (Z.of_nat (ccnt c (rs_live s))) -> room_at s c.
Proof.
  intros s c (Hq1 & Hb0 & Hqn & Hq) Hr. unfold room_ok, room_at in *.
  pose proof (ccnt_quar_le c (rs_quar s) Hq1) as Hcq. pose proof (lo_pos c) as Hlo.
  rewrite zsum_map8 in Hcq. pose proof (zsum_nonneg _ Hq1) as Hz.
  assert (H8 : zsum (rs_quar s) + 8 * Z.of_nat (length (rs_quar s)) <= QT)
    by (unfold Q_BATCH, Q_BATCH_BYTES in *; lia).
  assert (Hqc : Z.of_nat (ccnt c (rs_quar s)) <= QT / (lo c + 8)) by (apply Z.div_le_lower_bound; lia).
  assert (Hbc : rs_batches s <= QT / Q_BATCH_BYTES)
    by (apply Z.div_le_lower_bound; unfold Q_BATCH_BYTES in *; lia).
  destruct (c =? K_BATCH_CLASS); lia.
Qed.
