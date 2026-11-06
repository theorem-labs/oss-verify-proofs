(* omx-clap-core/fuzz_preset, Spec: P8 part (a) close (h-hpreset-7's port of asan_halts / agrees, piece P8;
   c-frame-alloc): no consumer allocation of a primary class other than 17 returns NULL in the new harness.

   WHAT IT SAYS. gate_not17: at every position of target_run's calls (PresetRun.hruns, any number of calls, any
   grants of the three check_no_overread readings), for every primary class c in 1 .. 30 but 17, the class-c live
   requests plus the driver's DRV blocks leave room (PresetRoom.room_ok: the quarantine's most, the class-24 batch
   records, the refill). no_null_not17: so a consumer malloc / realloc of a class-c request (c <> 17) at a position
   whose allocator state holds the model's live requests and at most 3 more, if it returns NULL, returns it on an
   environment refusal (grant flag g = false; PresetRoom.no_null_of_room, the instance's flag form).

   HOW. PresetRun.hruns_live bounds the live count of a class f by KH + max (3 A) (A + 2 B + KB), A bounding the
   f-requests of one reading of x and B those of the file tree's trace and of its rewritten copy. Per class c:
   - A = (MAXB + 3 MAXD) / m_A, m_A = min (m_G, m_S): every reader event of class c charges at least m_A input bytes
     (PjCharge.jr_run_cnt), m_S = max (lo c - 17) 1 for the allocations, m_G the least charge of a class-c grow
     (checked by PjCharge.chk_minG over j <= 9; 2048 when no grow of the reader is in class c);
   - B = (MAXB + 3 MAXD) / m_G + (3 MAXB + 3 MAXD) / m_S + 4: the grows of the tree's trace are those of the parse of x
     (PjCharge.jr_run_grows_tree), its other events those of the parse of wdoc t false (PjRoundTrip.G9_trace), at
     most 3 |x| bytes long (SlotSizes.wlen_false_read); the copy's trace has at most 4 class-c requests more
     (g_nprod_copy: pj_set replaces one member's value by a string, or appends one member).
   g_core proves the live bound for any charges with these properties; g_table checks, by computation, the grows'
   charges and room_ok at that bound for each class but 17. The 768-byte class 17 fails this bound (its requests
   include the 448-byte kids arrays of capacity 8, which charge 2 bytes each); it has its own proof.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss PjCharge PresetRun PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
Import ListNotations.
Local Open Scope Z_scope.

(* the driver's blocks, live across every call (main's two buffers, the payload copy): DEFINED in the leaf
   PresetLiveBounds.v (which keeps lib/Prog/*_c.v out of the kit's closure; do not fold it back), re-exported here as the
   same term, so `unfold DRV` and every use below are unchanged *)
Notation DRV := PresetLiveBounds.DRV.

(* ================================================================ hruns_live for any number of calls
   (PresetRun.hruns_live's proof; its bound on the number of calls is not used there) *)

Lemma g_hruns_live : forall sm x os f A B,
  (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (forall t, fst (jr_run sm x []) = Some t -> (nprodR f (rd_hevs (ttrace t)) <= B)%nat) ->
  (forall ms, fst (jr_run sm x []) = Some (JObj ms) -> (nprodR f (rd_hevs (ttrace (copy_set ms))) <= B)%nat) ->
  forall i, (cnt f (hlive (firstn i (hruns sm x os))) <= KH + Nat.max (3 * A) (A + 2 * B + KB))%nat.
Proof.
  intros sm x os f A B HA HB HB' i.
  assert (Hpk : (pkR f [] (hruns sm x os) <= KH + Nat.max (3 * A) (A + 2 * B + KB))%nat).
  { induction os as [|[[o1 o2] o0] os IH].
    - cbn [hruns map concat pkR]. assert (C0 : cnt f [] = 0%nat) by reflexivity. lia.
    - rewrite hruns_cons, (pkR_app f (call_evs sm x o1 o2 o0)).
      destruct (call_ok sm x o1 o2 o0) as [_ E]. unfold hlive in E. rewrite E.
      pose proof (pkR_call sm f x o1 o2 o0 A B HA HB HB'). lia. }
  pose proof (pkR_prefix f (hruns sm x os) [] i). unfold hlive. lia.
Qed.

(* ================================================================ the reader's requests, as PjCharge counts them *)

Lemma g_rd_cons : forall e t, rd_hevs (e :: t) = rd_hev e ++ rd_hevs t.
Proof. reflexivity. Qed.

Lemma g_rd_app : forall a b, rd_hevs (a ++ b) = rd_hevs a ++ rd_hevs b.
Proof. intros a b. unfold rd_hevs. apply flat_map_app. Qed.

(* step 1, the bridge: rd_hev makes the request n + 16 of EAlloc n / EGrow m n, as PjCharge.req_ev *)
Lemma g_nprod_cntR : forall f tr, nprodR f (rd_hevs tr) = cntR (fun r => f (Z.of_nat r)) tr.
Proof.
  intros f tr. induction tr as [|e tr IH]; [reflexivity|].
  rewrite g_rd_cons, nprodR_app, IH.
  destruct e as [n|[|m] n|n|n]; cbn [rd_hev nprodR prod_evR cntR req_ev];
    try (rewrite Nat2Z.inj_add; change (Z.of_nat 16) with HEAD; destruct (f (Z.of_nat n + HEAD)));
    lia.
Qed.

(* the class of a request, on PjCharge's nat requests *)
Definition g_pcl (c : Z) (r : nat) : bool := in_cls c (Z.of_nat r).

Lemma g_nprod_pcl : forall c tr, nprodR (in_cls c) (rd_hevs tr) = cntR (g_pcl c) tr.
Proof. intros c tr. rewrite g_nprod_cntR. reflexivity. Qed.

(* ================================================================ the per-class charges

   The lemmas below take the charges m and the least request L as variables: the kernel must never unfold a
   constant whose value holds lo c (scan_lo over Z.to_nat K_MAX_SIZE) against that value (that conversion
   overflows the kernel's stack). g_table states its facts on lo c and g_mG c as booleans. *)

Definition g_hi : nat := Z.to_nat K_MAX_SIZE.

Lemma g_hi_z : Z.of_nat g_hi = K_MAX_SIZE.
Proof. vm_compute. reflexivity. Qed.

(* the least charge of a class-c grow of capacity 8 * 2 ^ j (kids 448 * 2 ^ j, keys 64 * 2 ^ j bytes), 2048 if none *)
Definition g_min (c : Z) (j : nat) : nat :=
  Nat.min (if g_pcl c (448 * 2 ^ j + 16)%nat then chg_ev (EGrow 0 (448 * 2 ^ j)%nat) else 2048%nat)
          (if g_pcl c (64 * 2 ^ j + 16)%nat then chg_ev (EGrow 0 (64 * 2 ^ j)%nat) else 2048%nat).
Definition g_mG (c : Z) : nat := fold_right Nat.min 2048%nat (map (g_min c) (List.seq 0 10)).

Lemma g_minS : forall c (L : Z) m, (forall n, 1 <= n -> in_cls c n = true -> L <= n) ->
  (m <= Nat.max (Z.to_nat L - 17) 1)%nat -> forall e, ev_shape e -> is_grow e = false ->
  match req_ev e with Some r => g_pcl c r = true -> (m <= chg_ev e)%nat | None => True end.
Proof.
  intros c L m HL Hm e _ Hg.
  destruct e as [n|m0 n|n|n]; cbn [is_grow] in Hg; try discriminate; cbn [req_ev]; try exact I.
  intros HP. unfold g_pcl in HP. pose proof (HL (Z.of_nat (n + 16)) ltac:(lia) HP) as Hl.
  cbn [chg_ev]. lia.
Qed.

Lemma g_minG : forall c m hi, Z.of_nat hi = K_MAX_SIZE -> chk_minG (g_pcl c) m hi 9%nat = true ->
  forall e, ev_shape e -> is_grow e = true ->
  match req_ev e with Some r => g_pcl c r = true -> (m <= chg_ev e)%nat | None => True end.
Proof.
  intros c m hi Hhi H. apply (chk_minG_ok (g_pcl c) m hi 9 H).
  intros r Hr. unfold g_pcl, in_cls, cls in Hr.
  destruct (is_primary (Z.of_nat r)) eqn:Ep; [|discriminate].
  destruct r as [|r']; [lia|].
  pose proof (cls_small (Z.of_nat (S r')) ltac:(lia) Ep). lia.
Qed.

Lemma g_minA : forall c mG mS mA, chk_minG (g_pcl c) mG g_hi 9%nat = true -> (mA <= mG)%nat -> (mA <= mS)%nat ->
  (mS <= Nat.max (Z.to_nat (lo c) - 17) 1)%nat -> forall e, ev_shape e ->
  match req_ev e with Some r => g_pcl c r = true -> (mA <= chg_ev e)%nat | None => True end.
Proof.
  intros c mG mS mA H HG HS HSl e He. destruct (is_grow e) eqn:Eg.
  - pose proof (g_minG c mG g_hi g_hi_z H e He Eg) as G.
    destruct (req_ev e); [|exact I]. intros HP. specialize (G HP). lia.
  - exact (g_minS c (lo c) mA (lo_le c) (Nat.le_trans _ _ _ HS HSl) e He Eg).
Qed.

(* a PjCharge count bound, in Z, at the input bound Lz *)
Lemma g_cnt_z : forall (k L m : nat) (Lz : Z), (0 < m)%nat -> Z.of_nat L <= Lz ->
  (k <= (L + 3 * MAXD) / m)%nat -> Z.of_nat k <= (Lz + 96) / Z.of_nat m.
Proof.
  intros k L m Lz Hm HL Hk. apply Nat2Z.inj_le in Hk.
  rewrite Nat2Z.inj_div, Nat2Z.inj_add in Hk.
  replace (Z.of_nat (3 * MAXD)) with 96 in Hk by reflexivity.
  eapply Z.le_trans; [exact Hk|]. apply Z.div_le_mono; lia.
Qed.

(* ================================================================ the rewrite's copy: at most 4 requests more *)

Lemma g_nprod_rd_le : forall f l, (nprodR f (rd_hevs l) <= length l)%nat.
Proof. intros f l. eapply Nat.le_trans; [apply nprodR_len|apply rd_hevs_lenR]. Qed.

Lemma g_nprod_hev : forall f e, (nprodR f (rd_hev e) <= 1)%nat.
Proof. intros f e. pose proof (nprodR_len f (rd_hev e)). pose proof (rd_hev_lenR e). lia. Qed.

Lemma g_nprod_grow : forall f o n cp, (nprodR f (rd_hevs (grow_ev o n cp)) <= 2)%nat.
Proof.
  intros f o n cp. eapply Nat.le_trans; [apply g_nprod_rd_le|].
  unfold grow_ev. destruct (Nat.ltb n cp); [cbn; lia|]. destruct o; cbn [length]; lia.
Qed.

Lemma g_nprod_str : forall f s, (nprodR f (rd_hevs (ttrace (JStr s))) <= 1)%nat.
Proof. intros f s. eapply Nat.le_trans; [apply g_nprod_rd_le|]. cbn [ttrace length]. lia. Qed.

Ltac g_split := repeat first [rewrite g_rd_app | rewrite g_rd_cons]; rewrite ?nprodR_app.

Lemma g_nprod_set : forall f ms n cp,
  (nprodR f (rd_hevs (tgo_obj n cp (pj_set_model ms MOD_KEY (JStr MOD_VAL)))) <=
   nprodR f (rd_hevs (tgo_obj n cp ms)) + 4)%nat.
Proof.
  intros f ms. induction ms as [|[k u] r IH]; intros n cp; cbn [pj_set_model].
  - (* appended: the grows, the name, the value *)
    cbn [tgo_obj]. rewrite ?app_nil_r. g_split.
    pose proof (g_nprod_grow f true n cp). pose proof (g_nprod_hev f (EAlloc (S (length (flat_map ech MOD_KEY))))).
    pose proof (g_nprod_str f MOD_VAL). lia.
  - destruct (list_eq_dec Z.eq_dec k MOD_KEY) as [E|E]; cbn [tgo_obj]; g_split.
    + (* replaced: the value's trace is one string's *)
      pose proof (g_nprod_str f MOD_VAL). lia.
    + pose proof (IH (S n) (gcap n cp)). lia.
Qed.

Lemma g_nprod_copy : forall f ms,
  (nprodR f (rd_hevs (ttrace (copy_set ms))) <= nprodR f (rd_hevs (ttrace (JObj ms))) + 4)%nat.
Proof. intros f ms. unfold copy_set. rewrite !tt_obj. apply g_nprod_set. Qed.

(* ================================================================ the gate, for any charges the table checks *)

Lemma g_room_le : forall c l l1,
  l1 + QT / (lo c + 8) + (if c =? K_BATCH_CLASS then QT / Q_BATCH_BYTES else 0) + refill c <= cap c ->
  l <= l1 -> room_ok c l.
Proof.
  intros c l l1 H Hl. unfold room_ok. revert H.
  generalize (QT / (lo c + 8)) (if c =? K_BATCH_CLASS then QT / Q_BATCH_BYTES else 0) (refill c) (cap c).
  intros. lia.
Qed.

Lemma g_room_mono : forall c l l1, room_ok c l -> l1 <= l -> room_ok c l1.
Proof. unfold room_ok. intros c l l1 H Hl. destruct (c =? K_BATCH_CLASS); lia. Qed.

(* steps 2-3: one reading of x, under any grants, produces at most (MAXB + 3 MAXD) / mA class-c requests; the file's
   tree's trace at most (MAXB + 3 MAXD) / mG + (3 MAXB + 3 MAXD) / mS (its grows are the parse of x's, its other
   events the parse of wdoc t false's) *)
Lemma g_reads : forall sm x c (mG mS mA : nat), Z.of_nat (length x) <= MAXB ->
  chk_minG (g_pcl c) mG g_hi 9%nat = true -> (0 < mA)%nat -> (mA <= mG)%nat -> (mA <= mS)%nat ->
  (mS <= Nat.max (Z.to_nat (lo c) - 17) 1)%nat ->
  (forall ok, Z.of_nat (nprodR (in_cls c) (rd_hevs (rtr sm ok x))) <= (MAXB + 96) / Z.of_nat mA) /\
  (forall t, fst (jr_run sm x []) = Some t ->
     Z.of_nat (nprodR (in_cls c) (rd_hevs (ttrace t))) <=
     (MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS).
Proof.
  intros sm x c mG mS mA Hx HG Hpos HAG HAS HSl.
  assert (HmG : (0 < mG)%nat) by lia.
  assert (HmS : (0 < mS)%nat) by lia.
  split.
  - intros ok. rewrite g_nprod_pcl. unfold rtr.
    apply (g_cnt_z _ (length x)); [exact Hpos|exact Hx|].
    apply jr_run_cnt; [exact Hpos|exact (g_minA c mG mS mA HG HAG HAS HSl)].
  - intros t Ht. rewrite g_nprod_pcl, cntR_split, Nat2Z.inj_add.
    assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ht).
    pose proof (jr_run_cntG sm (g_pcl c) mG x [] HmG (g_minG c mG g_hi g_hi_z HG)) as G1.
    rewrite (jr_run_grows_tree sm x [] t Ht (g_pcl c)) in G1.
    pose proof (g_cnt_z _ _ _ MAXB HmG Hx G1) as ZG.
    pose proof (jr_run_cntS sm (g_pcl c) mS (wdoc t false) [] HmS (g_minS c (lo c) mS (lo_le c) HSl)) as S1.
    rewrite (G9_trace sm t Hw false) in S1.
    assert (Hlw : Z.of_nat (length (wdoc t false)) <= 3 * MAXB).
    { pose proof (SlotSizes.wlen_false_read sm x t Ht) as W. unfold PjWriteHyp.wlen in W. lia. }
    pose proof (g_cnt_z _ _ _ (3 * MAXB) HmS Hlw S1) as ZS.
    lia.
Qed.

(* steps 2-4: A = (MAXB + 3 MAXD) / mA, B = (MAXB + 3 MAXD) / mG + (3 MAXB + 3 MAXD) / mS + 4, and hruns_live *)
Lemma g_core : forall sm x os c (mG mS mA : nat), Z.of_nat (length x) <= MAXB ->
  chk_minG (g_pcl c) mG g_hi 9%nat = true -> (0 < mA)%nat -> (mA <= mG)%nat -> (mA <= mS)%nat ->
  (mS <= Nat.max (Z.to_nat (lo c) - 17) 1)%nat ->
  forall i, Z.of_nat (cnt (in_cls c) (hlive (firstn i (hruns sm x os)))) <=
    3 + Z.max (3 * ((MAXB + 96) / Z.of_nat mA))
              ((MAXB + 96) / Z.of_nat mA + 2 * ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4) + 2).
Proof.
  intros sm x os c mG mS mA Hx HG Hpos HAG HAS HSl i.
  assert (HmG : (0 < mG)%nat) by lia.
  assert (HmS : (0 < mS)%nat) by lia.
  assert (Hz0 : 0 <= (MAXB + 96) / Z.of_nat mA) by (apply Z.div_pos; unfold MAXB; lia).
  assert (Hz1 : 0 <= (MAXB + 96) / Z.of_nat mG) by (apply Z.div_pos; unfold MAXB; lia).
  assert (Hz2 : 0 <= (3 * MAXB + 96) / Z.of_nat mS) by (apply Z.div_pos; unfold MAXB; lia).
  destruct (g_reads sm x c mG mS mA Hx HG Hpos HAG HAS HSl) as [HA HBt].
  (* step 4 *)
  assert (HA' : forall ok, (nprodR (in_cls c) (rd_hevs (rtr sm ok x)) <= Z.to_nat ((MAXB + 96) / Z.of_nat mA))%nat)
    by (intros ok; specialize (HA ok); lia).
  assert (HB : forall t, fst (jr_run sm x []) = Some t ->
               (nprodR (in_cls c) (rd_hevs (ttrace t)) <=
                Z.to_nat ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4))%nat)
    by (intros t Ht; specialize (HBt t Ht); lia).
  assert (HB' : forall ms, fst (jr_run sm x []) = Some (JObj ms) ->
                (nprodR (in_cls c) (rd_hevs (ttrace (copy_set ms))) <=
                 Z.to_nat ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4))%nat)
    by (intros ms Hms; specialize (HBt (JObj ms) Hms); pose proof (g_nprod_copy (in_cls c) ms); lia).
  pose proof (g_hruns_live sm x os (in_cls c) _ _ HA' HB HB' i) as Hl.
  unfold KH, KB in Hl. lia.
Qed.

(* ================================================================ the table (step 5) *)

Definition g_classes : list Z := map Z.of_nat (List.seq 1 30).

(* every class but 17: the grows' charge check, and room_ok at g_core's bound plus DRV, with
   m_G = g_mG c, m_S = max (lo c - 17) 1 (the least charge of a class-c allocation), m_A = min m_G m_S *)
Lemma g_table : forallb (fun c => (c =? 17) ||
  (let L := lo c in let mG := g_mG c in let mS := Nat.max (Z.to_nat L - 17) 1 in let mA := Nat.min mG mS in
   chk_minG (g_pcl c) mG g_hi 9%nat && Nat.ltb 0 mA &&
   (3 + Z.max (3 * ((MAXB + 96) / Z.of_nat mA))
              ((MAXB + 96) / Z.of_nat mA + 2 * ((MAXB + 96) / Z.of_nat mG + (3 * MAXB + 96) / Z.of_nat mS + 4) + 2) +
    DRV + QT / (L + 8) + (if c =? K_BATCH_CLASS then QT / Q_BATCH_BYTES else 0) + refill c <=? cap c)))
  g_classes = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ the gate *)

Theorem gate_not17 : forall sm x os, (Z.of_nat (length x) <= MAXB) ->
  forall c, 1 <= c <= 30 -> c <> 17 ->
  forall i, room_ok c (Z.of_nat (cnt (in_cls c) (hlive (firstn i (hruns sm x os)))) + DRV).
Proof.
  intros sm x os Hx c Hc Hc17 i.
  pose proof g_table as T. rewrite forallb_forall in T.
  assert (Hin : In c g_classes).
  { unfold g_classes. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  specialize (T c Hin). apply orb_true_iff in T as [T|R]; [apply Z.eqb_eq in T; contradiction|].
  cbv zeta in R.
  apply andb_true_iff in R as [R Hroom]. apply andb_true_iff in R as [HG Hpos].
  apply Nat.ltb_lt in Hpos. apply Z.leb_le in Hroom.
  pose proof (g_core sm x os c (g_mG c) (Nat.max (Z.to_nat (lo c) - 17) 1)
                (Nat.min (g_mG c) (Nat.max (Z.to_nat (lo c) - 17) 1)) Hx HG Hpos
                (Nat.le_min_l _ _) (Nat.le_min_r _ _) (Nat.le_refl _) i) as Hl.
  apply (g_room_le c _ _ Hroom). apply (proj1 (Z.add_le_mono_r _ _ DRV)). exact Hl.
Qed.

(* ================================================================ the consumer corollary *)

Fixpoint g_cid (s : Z) (f : nat) : bool :=
  match f with
  | O => true
  | S g => (1 <=? class_id s) && (class_id s <=? 30) && g_cid (s + 1) g
  end.

Lemma g_cid_ok : forall f s k, g_cid s f = true -> s <= k < s + Z.of_nat f -> 1 <= class_id k <= 30.
Proof.
  induction f as [|f IH]; intros s k H Hk; [lia|].
  cbn [g_cid] in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1, H2. destruct (Z.eq_dec k s) as [->|Hne]; [lia|].
  apply (IH (s + 1)); [exact H3|lia].
Qed.

Lemma g_cid_table : g_cid 1 (Z.to_nat K_MAX_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g_cls_range : forall n c, cls n = Some c -> 1 <= c <= 30.
Proof.
  intros n c H. unfold cls in H. destruct (is_primary n) eqn:Ep; [|discriminate]. injection H as <-.
  apply (g_cid_ok (Z.to_nat K_MAX_SIZE) 1); [exact g_cid_table|].
  unfold is_primary in Ep. apply Z.leb_le in Ep.
  assert (Hz : 0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_nonneg; lia).
  assert (Hr : 8 <= rounded_size n).
  { unfold rounded_size, rup.
    pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
  unfold needed0 in *. rewrite Z2Nat.id by (unfold K_MAX_SIZE; lia). unfold K_MAX_SIZE in *. lia.
Qed.

Lemma g_ccnt_len : forall c l, (ccnt c l <= length l)%nat.
Proof.
  intros c l. unfold ccnt. induction l as [|z l IH]; cbn [filter length]; [lia|].
  destruct (in_cls c z); cbn [length]; lia.
Qed.

Corollary no_null_not17 : forall sm x os i e b s n c (g : bool) (null : Prop), (Z.of_nat (length x) <= MAXB) ->
  nth_error (combine (hruns sm x os) (hcons sm x os)) i = Some (e, b) -> b = true ->
  (e = HMal n \/ exists m, e = HRe m n) -> cls n = Some c -> c <> 17 ->
  (* the instance's state at that allocation: its live requests are the model's plus the driver's blocks *)
  (exists d, (length d <= 3)%nat /\ Permutation (rs_live s) (hlive (firstn i (hruns sm x os)) ++ d)) ->
  quar_bytes_ok s -> (g = true -> null -> null_full s n) -> null -> g = false.
Proof.
  intros sm x os i e b s n c g null Hx _ _ _ Hc Hc17 (d & Hd & Hp) Hq Hn Hnull.
  pose proof (gate_not17 sm x os Hx c (g_cls_range n c Hc) Hc17 i) as G.
  apply (no_null_of_room g null s n c Hq Hn Hc); [|exact Hnull].
  apply (g_room_mono c _ _ G).
  rewrite (ccnt_perm c _ _ Hp), ccnt_app.
  pose proof (g_ccnt_len c d).
  change (ccnt c (hlive (firstn i (hruns sm x os)))) with (cnt (in_cls c) (hlive (firstn i (hruns sm x os)))).
  unfold DRV. lia.
Qed.
