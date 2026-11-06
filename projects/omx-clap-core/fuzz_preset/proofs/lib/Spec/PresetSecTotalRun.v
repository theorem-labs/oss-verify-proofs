(* omx-clap-core/fuzz_preset, Spec: the run bounds of the secondary meter (row A17 of a Theorem Labs lane's Part 4 plan, owner
   a Theorem Labs lane). Nothing here is a function's proof (rule 24); kind: model bound.

   WHAT IT SAYS. For every input x and every grants of check_no_overread's readings (PresetRun.call_evs), one call
   makes at most NCALL = 25,127 secondary requests (nsec_call) whose mapped sizes sum to at most TCALL =
   10,520,122,619 (tsec_call); above MAXB the call makes no event. target_run's at most 4 calls (PresetRun.hruns)
   make at most 4 NCALL / 4 TCALL (nsec_run, tsec_run), and so does every prefix of them (nsec_run_prefix,
   tsec_run_prefix: the meter is needed at each allocator call's entry and post). PresetSecTotal.sec_n_fits /
   sec_t_fits close the count against 2 ^ 17 and 2 ^ 36. sec_witness_call / sec_witness_run: the meter is not
   vacuous (a 64 KiB input already makes 3 secondaries in every call).

   HOW. treq evs is the sum of the secondary requests themselves; tsec evs <= treq evs + 12,294 nsec evs
   (tsec_treq: sec_map_size r <= r + 12,294 for a secondary r). NT evs n b says nsec evs <= n and treq evs <= b, and
   the call is bounded segment by segment over PresetRun.call_evs_blocks:
   - a reading of x (any grants): count PresetLiveSec.w_reads (JT_SEC weights); bytes: every secondary reader event
     asks for at most 225 times its JT_SEC weight (rqZ_225), and a reading weighs at most |x| + 96
     (PresetLiveSec.jr_run_wcharge);
   - a read-back of the file's tree t (ttrace t): its grows are the reading's (PjCharge.jr_run_grows_eq), its other
     events those of reading the compact text (PjRoundTrip.G9_trace, |wdoc t false| <= 3 |x|), each asking for at most
     twice its charge;
   - the rewritten copy's read-back and pj_set's grow: the tree's trace plus the top object's one more grow, whose
     capacity is at most |x| + 8 (every kids grow of ttrace t is a grow of the reading of x: PjGrammar.jr_esize_bound);
   - the writer and rendered () chains: the capacities at least double (geo: WriterSpec.grow_calls / newcap,
     PresetReqAt.tx_caps) and stay below PresetLiveBytes.WCAP / RCAP <= 112 MAXB (pretty) or 6 MAXB + 2 (compact), so
     a chain sums to at most 2 U and holds at most 13 (pretty) or 9 (compact) secondary capacities (geo_cnt).

   CLOSURE: Requires PresetLiveSec / PresetGate (lib/Prog/SlotSizes.v) and PresetLiveBytes (PresetRoomPos); the
   definitions it bounds are in PresetSecTotal.v, which the kit's PresetRoomPos.v may Require. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss PjCharge PresetRun PresetLiveSec PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetGate PresetLiveBytes PresetRoom.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ part 1: the secondary request bytes *)

Lemma nsec_nprod : forall evs, nsec evs = nprodR sec_req evs.
Proof. reflexivity. Qed.

(* the request of an event when it is secondary *)
Definition sec_rq (e : hev) : Z :=
  match e with
  | HMal r | HRe _ r => if sec_req r then r else 0
  | _ => 0
  end.

Fixpoint treq (evs : list hev) : Z :=
  match evs with
  | [] => 0
  | e :: es => sec_rq e + treq es
  end.

Lemma treq_app : forall a b, treq (a ++ b) = treq a + treq b.
Proof. induction a as [|e a IH]; intros b; cbn [app treq]; [lia|]. rewrite IH. lia. Qed.

Lemma sec_req_lo : forall r, sec_req r = true -> 64513 <= r.
Proof. intros r H. rewrite sec_req_iff in H. apply Z.leb_le in H. exact H. Qed.

Lemma sec_rq_nn : forall e, 0 <= sec_rq e.
Proof.
  intros [r | m r | r | L]; cbn [sec_rq]; try lia;
    destruct (sec_req r) eqn:E; try lia; pose proof (sec_req_lo r E); lia.
Qed.

Lemma treq_nn : forall evs, 0 <= treq evs.
Proof. induction evs as [|e es IH]; cbn [treq]; [lia|]. pose proof (sec_rq_nn e). lia. Qed.

Lemma round_up_le : forall x a, 0 < a -> YG00.round_up x a <= x + a - 1.
Proof.
  intros x a Ha. unfold YG00.round_up.
  pose proof (Z.div_mod (x + a - 1) a ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + a - 1) a Ha) as M.
  set (q := (x + a - 1) / a) in *. set (m := (x + a - 1) mod a) in *. clearbody q m.
  rewrite (Z.mul_comm q a). lia.
Qed.

(* a secondary's map: the request rounded to 8, two 2048-byte red zones, rounded to a page, plus a page *)
Lemma sec_map_size_le : forall r, 64513 <= r -> YG00.sec_map_size r <= r + SEC_MAP_OVH.
Proof.
  intros r Hr.
  assert (Hz : YG00.rz_size r = 2048) by exact (rz_size_hi r Hr).
  unfold YG00.sec_map_size, YG00.needed_size, YG00.needed_primary, YG00.rounded_size, YG00.kPage, SEC_MAP_OVH.
  rewrite Hz.
  pose proof (round_up_le (Z.max r 8) 8 ltac:(lia)).
  destruct (YG00.from_primary r).
  - pose proof (round_up_le (YG00.round_up (Z.max r 8) 8 + 2048) 4096 ltac:(lia)). lia.
  - pose proof (round_up_le (YG00.round_up (Z.max r 8) 8 + 2048 + 2048) 4096 ltac:(lia)). lia.
Qed.

Lemma sec_mapped_le : forall e, sec_mapped e <= sec_rq e + SEC_MAP_OVH * Z.of_nat (prod_evR sec_req e).
Proof.
  intros [r | m r | r | L]; cbn [sec_mapped sec_rq prod_evR]; unfold SEC_MAP_OVH; try lia;
    change (negb (PresetRoom.is_primary r)) with (sec_req r);
    destruct (sec_req r) eqn:E; try lia;
    pose proof (sec_map_size_le r (sec_req_lo r E)); unfold SEC_MAP_OVH in *; lia.
Qed.

(* the mapped bytes are the requests plus SEC_MAP_OVH per secondary *)
Lemma tsec_treq : forall evs, tsec evs <= treq evs + SEC_MAP_OVH * Z.of_nat (nsec evs).
Proof.
  intros evs. rewrite nsec_nprod. induction evs as [|e es IH]; cbn [tsec treq nprodR]; [unfold SEC_MAP_OVH; lia|].
  pose proof (sec_mapped_le e). rewrite Nat2Z.inj_add. unfold SEC_MAP_OVH in *. lia.
Qed.

(* ---------------------------------------------------------------- the bound pairs *)

Definition NT (evs : list hev) (n b : Z) : Prop := Z.of_nat (nsec evs) <= n /\ treq evs <= b.

Lemma NT_app : forall a b n1 n2 b1 b2, NT a n1 b1 -> NT b n2 b2 -> NT (a ++ b) (n1 + n2) (b1 + b2).
Proof.
  intros a b n1 n2 b1 b2 [A1 A2] [B1 B2]. split; [rewrite nsec_app, Nat2Z.inj_add | rewrite treq_app]; lia.
Qed.

Lemma NT_weak : forall evs n b n' b', NT evs n b -> n <= n' -> b <= b' -> NT evs n' b'.
Proof. intros evs n b n' b' [H1 H2] Hn Hb. split; lia. Qed.

Lemma NT_nn : forall evs n b, NT evs n b -> 0 <= n /\ 0 <= b.
Proof. intros evs n b [H1 H2]. pose proof (treq_nn evs). lia. Qed.

Lemma NT_nil : NT [] 0 0.
Proof. split; cbn; lia. Qed.

Lemma NT_free : forall r, NT [HFr r] 0 0.
Proof. intros r. unfold NT. rewrite nsec_nprod. cbn [nprodR prod_evR treq sec_rq]. lia. Qed.

Lemma NT_bulk : forall L, NT [HBulk L] 0 0.
Proof. intros L. unfold NT. rewrite nsec_nprod. cbn [nprodR prod_evR treq sec_rq]. lia. Qed.

Lemma NT_mal : forall r, 0 <= r -> NT [HMal r] 1 r.
Proof.
  intros r Hr. unfold NT. rewrite nsec_nprod. cbn [nprodR prod_evR treq sec_rq].
  destruct (sec_req r); cbn [Z.of_nat]; lia.
Qed.

Lemma NT_mal3 : forall r, 0 <= r -> NT [HMal r; HMal r; HMal r] 3 (3 * r).
Proof.
  intros r Hr. eapply NT_weak;
    [apply (NT_app [HMal r]); [apply NT_mal; exact Hr | apply (NT_app [HMal r]); apply NT_mal; exact Hr] | lia | lia].
Qed.

Lemma NT_fr3 : forall r, NT [HFr r; HFr r; HFr r] 0 0.
Proof. intros r. unfold NT. rewrite nsec_nprod. cbn [nprodR prod_evR treq sec_rq]. lia. Qed.

Lemma consts_nn : 0 <= RD_N /\ 0 <= RB_N /\ 0 <= CH_P /\ 0 <= CH_C /\ 0 <= RD_T /\ 0 <= RB_T /\
  0 <= TOP_GROW_T /\ 0 <= CHP_T /\ 0 <= CHC_T /\ 0 <= MAXB.
Proof. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ================================================================ part 2: a reader trace *)

(* the request of a reader event when it is secondary (rd_hev asks for PjCharge.req_ev's n + 16) *)
Definition rqZ (e : ev) : Z :=
  match req_ev e with Some r => if sec_req (Z.of_nat r) then Z.of_nat r else 0 | None => 0 end.

Fixpoint rsum (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => rqZ e + rsum r
  end.

Lemma rsum_app : forall a b, rsum (a ++ b) = rsum a + rsum b.
Proof. induction a as [|e a IH]; intros b; cbn [app rsum]; [lia|]. rewrite IH. lia. Qed.

Lemma rqZ_nn : forall e, 0 <= rqZ e.
Proof. intros e. unfold rqZ. destruct (req_ev e) as [r|]; [destruct (sec_req (Z.of_nat r)); lia | lia]. Qed.

Lemma rsum_nn : forall tr, 0 <= rsum tr.
Proof. induction tr as [|e tr IH]; cbn [rsum]; [lia|]. pose proof (rqZ_nn e). lia. Qed.

Lemma rqZ_le : forall e, rqZ e <= match req_ev e with Some r => Z.of_nat r | None => 0 end.
Proof. intros e. unfold rqZ. destruct (req_ev e) as [r|]; [destruct (sec_req (Z.of_nat r)); lia | lia]. Qed.

Lemma treq_rd1 : forall e, treq (rd_hev e) = rqZ e.
Proof.
  intros [n | [|m] n | n | n]; cbn [rd_hev treq sec_rq]; unfold rqZ; cbn [req_ev]; try reflexivity;
    unfold HEAD; rewrite Nat2Z.inj_add; change (Z.of_nat 16) with 16; rewrite Z.add_0_r; reflexivity.
Qed.

Lemma treq_rd : forall tr, treq (rd_hevs tr) = rsum tr.
Proof.
  induction tr as [|e tr IH]; [reflexivity|].
  rewrite rd_hevs_cons, treq_app, IH, treq_rd1. reflexivity.
Qed.

(* every secondary reader event asks for at most 225 times its JT_SEC weight *)
Lemma rqZ_225 : forall e, ev_shape e -> rqZ e <= 225 * Z.of_nat (wev JT_SEC e).
Proof.
  intros e He. unfold rqZ. destruct e as [n|m n|n|n]; cbn [req_ev]; try lia.
  - destruct (sec_req (Z.of_nat (n + 16))) eqn:E; [|lia]. apply sec_req_lo in E. cbn [wev]. lia.
  - destruct (sec_req (Z.of_nat (n + 16))) eqn:E; [|lia]. apply sec_req_lo in E.
    destruct He as (j & [-> | ->]).
    + (* kids, 448 * 2 ^ j bytes: a secondary only from capacity 2048 (j >= 8) *)
      replace (448 * 2 ^ j)%nat with (56 * (8 * 2 ^ j))%nat in * by lia. rewrite wchg_kids.
      assert (Hj : (8 <= j)%nat).
      { destruct (Nat.le_gt_cases 8 j) as [Hj|Hj]; [exact Hj|].
        assert (Hp : (2 ^ j <= 2 ^ 7)%nat) by (apply Nat.pow_le_mono_r; lia).
        change (2 ^ 7)%nat with 128%nat in Hp. lia. }
      destruct (Nat.eq_dec j 8) as [->|Hne].
      * apply Z.leb_le. vm_compute. reflexivity.
      * assert (Hq : (2 ^ 9 <= 2 ^ j)%nat) by (apply Nat.pow_le_mono_r; lia).
        change (2 ^ 9)%nat with 512%nat in Hq.
        unfold Wc, wT, JT_SEC. change (2 ^ 8)%nat with 256%nat.
        set (p := (2 ^ j)%nat) in *. clearbody p.
        destruct (Nat.ltb_spec (8 * p) (8 * 256)); [lia|].
        destruct (Nat.eqb_spec (8 * p) (8 * 256)); [lia|].
        unfold PjCharge.gchg. eqbs; dm; lia.
    + (* keys, 64 * 2 ^ j bytes: a secondary only from capacity 8192 (j >= 10) *)
      assert (Hc : capok (8 * 2 ^ j)%nat) by (right; exists j; reflexivity).
      pose proof (pow2_pos j) as Hp0.
      replace (64 * 2 ^ j)%nat with (8 * (8 * 2 ^ j))%nat in * by lia.
      rewrite (wchg_keys JT_SEC m (8 * 2 ^ j)%nat Hc ltac:(lia)).
      assert (Hj : (10 <= j)%nat).
      { destruct (Nat.le_gt_cases 10 j) as [Hj|Hj]; [exact Hj|].
        assert (Hp : (2 ^ j <= 2 ^ 9)%nat) by (apply Nat.pow_le_mono_r; lia).
        change (2 ^ 9)%nat with 512%nat in Hp. lia. }
      assert (Hq : (2 ^ 10 <= 2 ^ j)%nat) by (apply Nat.pow_le_mono_r; lia).
      change (2 ^ 10)%nat with 1024%nat in Hq.
      unfold Wc, wT, JT_SEC. change (2 ^ 8)%nat with 256%nat.
      set (p := (2 ^ j)%nat) in *. clearbody p.
      destruct (Nat.ltb_spec (8 * p) (8 * 256)); [lia|].
      destruct (Nat.eqb_spec (8 * p) (8 * 256)); [lia|].
      unfold PjCharge.gchg. eqbs; dm; lia.
Qed.

(* a non-grow secondary (an allocation of n >= 64,497 bytes) asks for at most twice its charge *)
Lemma rqZ_nongrow : forall e, is_grow e = false -> rqZ e <= 2 * Z.of_nat (wev JT_SEC e).
Proof.
  intros [n|m n|n|n] H; cbn [is_grow] in H; try discriminate; unfold rqZ; cbn [req_ev wev]; try lia.
  destruct (sec_req (Z.of_nat (n + 16))) eqn:E; [|lia]. apply sec_req_lo in E. lia.
Qed.

Lemma rsum_wchg : forall tr, Forall ev_shape tr -> rsum tr <= 225 * Z.of_nat (wchg JT_SEC tr).
Proof.
  induction tr as [|e tr IH]; intros H; cbn [rsum wchg]; [lia|].
  apply Forall_cons_iff in H as [He H]. pose proof (rqZ_225 e He). pose proof (IH H). lia.
Qed.

Lemma rsum_filter_le : forall f tr, rsum (filter f tr) <= rsum tr.
Proof.
  intros f. induction tr as [|e tr IH]; cbn [filter rsum]; [lia|].
  pose proof (rqZ_nn e). destruct (f e); cbn [rsum]; lia.
Qed.

Lemma rsum_split : forall tr, rsum tr = rsum (filter is_grow tr) + rsum (filter (fun e => negb (is_grow e)) tr).
Proof.
  induction tr as [|e tr IH]; [reflexivity|]. cbn [filter rsum]. destruct (is_grow e); cbn [negb rsum]; lia.
Qed.

Lemma rsum_nongrow : forall tr, rsum (filter (fun e => negb (is_grow e)) tr) <= 2 * Z.of_nat (wchg JT_SEC tr).
Proof.
  induction tr as [|e tr IH]; cbn [filter rsum wchg]; [lia|].
  destruct (is_grow e) eqn:G; cbn [negb rsum].
  - lia.
  - pose proof (rqZ_nongrow e G). lia.
Qed.

(* one reading of y, under any grants *)
Lemma rsum_read : forall sm y ok, rsum (snd (jr_run sm y ok)) <= 225 * (Z.of_nat (length y) + 96).
Proof.
  intros sm y ok. pose proof (rsum_wchg _ (jr_run_shape sm y ok)) as H1.
  pose proof (jr_run_wcharge JT_SEC sm y ok) as H2. unfold MAXD in H2. lia.
Qed.

(* the trace of the file's tree t: its grows are the reading of x's, its other events the compact text's *)
Lemma rsum_tt : forall sm x t, fst (jr_run sm x []) = Some t ->
  rsum (ttrace t) <= 225 * (Z.of_nat (length x) + 96) + 2 * (Z.of_nat (length (wdoc t false)) + 96).
Proof.
  intros sm x t Ht.
  assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ht).
  rewrite rsum_split.
  rewrite <- (jr_run_grows_eq sm x [] t Ht).
  pose proof (rsum_filter_le is_grow (snd (jr_run sm x []))) as H1.
  pose proof (rsum_read sm x []) as H2.
  rewrite <- (G9_trace sm t Hw false).
  pose proof (rsum_nongrow (snd (jr_run sm (wdoc t false) []))) as H3.
  pose proof (jr_run_wcharge JT_SEC sm (wdoc t false) []) as H4. unfold MAXD in H4.
  lia.
Qed.

(* every kids grow of the file's tree is a grow of the reading of x, so its capacity is at most |x| + 8 *)
Lemma kids_le : forall sm x t, fst (jr_run sm x []) = Some t ->
  forall m c, In (EGrow m (56 * c)) (ttrace t) -> (c <= length x + 8)%nat.
Proof.
  intros sm x t Ht m c Hin.
  assert (Hg : In (EGrow m (56 * c)) (filter is_grow (snd (jr_run sm x [])))).
  { rewrite (jr_run_grows_eq sm x [] t Ht). apply filter_In. split; [exact Hin | reflexivity]. }
  apply filter_In in Hg as [Hg _].
  pose proof (jr_esize_bound sm x [] _ Hg) as B. cbn [esize] in B. lia.
Qed.

(* ---------------------------------------------------------------- the top object's one more grow *)

Lemma gcap_bound : forall n cp, (gcap n cp <= 2 * cp + 8)%nat.
Proof. intros n cp. unfold gcap. destruct (Nat.ltb n cp); [lia|]. destruct (Nat.eqb cp 0); lia. Qed.

Lemma rsum_grow : forall o n cp, rsum (grow_ev o n cp) <= 64 * Z.of_nat (gcap n cp) + 32.
Proof.
  intros o n cp. unfold grow_ev. destruct (Nat.ltb n cp); [cbn [rsum]; lia|].
  pose proof (rqZ_le (EGrow (56 * cp) (56 * gcap n cp))) as H1.
  pose proof (rqZ_le (EGrow (8 * cp) (8 * gcap n cp))) as H2. cbn [req_ev] in H1, H2.
  pose proof (rqZ_nn (EGrow (8 * cp) (8 * gcap n cp))).
  destruct o; cbn [rsum]; lia.
Qed.

Lemma rsum_modkey : rqZ (EAlloc (S (length (flat_map ech MOD_KEY)))) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma rsum_modval : rsum (ttrace (JStr MOD_VAL)) = 0.
Proof. vm_compute. reflexivity. Qed.

(* PresetGate.g_nprod_set's byte twin: pj_set adds at most the top object's grow, of capacity at most M *)
Lemma rsum_set : forall ms n cp (M : nat), (cp <= M)%nat ->
  (forall m c, In (EGrow m (56 * c)) (tgo_obj n cp ms) -> (c <= M)%nat) ->
  rsum (tgo_obj n cp (pj_set_model ms MOD_KEY (JStr MOD_VAL))) <= rsum (tgo_obj n cp ms) + 128 * Z.of_nat M + 544.
Proof.
  induction ms as [|[k u] r IH]; intros n cp M Hcp HM; cbn [pj_set_model].
  - (* appended: the grows, the name, the value *)
    cbn [tgo_obj]. rewrite rsum_app. cbn [rsum app]. rewrite rsum_app, rsum_modkey, rsum_modval.
    pose proof (rsum_grow true n cp). pose proof (gcap_bound n cp). cbn [rsum]. lia.
  - destruct (list_eq_dec Z.eq_dec k MOD_KEY) as [E|E]; cbn [tgo_obj]; rewrite !rsum_app; cbn [rsum];
      rewrite !rsum_app.
    + (* replaced: the value's trace is one short string's *)
      rewrite rsum_modval. pose proof (rsum_nn (ttrace u)). lia.
    + assert (Hg : (gcap n cp <= M)%nat).
      { destruct (Nat.ltb n cp) eqn:El.
        - unfold gcap. rewrite El. exact Hcp.
        - apply (HM (56 * cp)%nat (gcap n cp)). cbn [tgo_obj]. apply in_or_app. left.
          unfold grow_ev. rewrite El. left. reflexivity. }
      assert (HM' : forall m c, In (EGrow m (56 * c)) (tgo_obj (S n) (gcap n cp) r) -> (c <= M)%nat).
      { intros m c Hin. apply (HM m c). cbn [tgo_obj]. apply in_or_app. right. right.
        apply in_or_app. right. exact Hin. }
      pose proof (IH (S n) (gcap n cp) M Hg HM'). lia.
Qed.

(* PresetReqAt.ncap after the members of an object: unchanged, or reached by a kids grow of its trace *)
Lemma ncap_in : forall ms n, PresetReqAt.ncap (n + length ms) = PresetReqAt.ncap n \/
  exists m, In (EGrow m (56 * PresetReqAt.ncap (n + length ms))) (tgo_obj n (PresetReqAt.ncap n) ms).
Proof.
  induction ms as [|[k u] r IH]; intros n.
  - left. rewrite Nat.add_0_r. reflexivity.
  - replace (n + length ((k, u) :: r))%nat with (S n + length r)%nat by (cbn [length]; lia).
    cbn [tgo_obj].
    destruct (IH (S n)) as [E | (m & Hm)].
    + rewrite E. change (PresetReqAt.ncap (S n)) with (gcap n (PresetReqAt.ncap n)).
      destruct (Nat.ltb n (PresetReqAt.ncap n)) eqn:El.
      * left. unfold gcap. rewrite El. reflexivity.
      * right. exists (56 * PresetReqAt.ncap n)%nat. apply in_or_app. left.
        unfold grow_ev. rewrite El. left. reflexivity.
    + right. exists m. apply in_or_app. right. right. apply in_or_app. right. exact Hm.
Qed.

Lemma ncap_top : forall sm x ms, fst (jr_run sm x []) = Some (JObj ms) ->
  (PresetReqAt.ncap (length ms) <= length x + 8)%nat.
Proof.
  intros sm x ms H. destruct (ncap_in ms 0) as [E | (m & Hm)].
  - cbn [Nat.add PresetReqAt.ncap] in E. rewrite E. lia.
  - apply (kids_le sm x (JObj ms) H m). rewrite tt_obj. exact Hm.
Qed.

(* ================================================================ part 3: the doubling chains *)

(* every capacity at least twice the one before (the first at least twice p) *)
Fixpoint geo (p : Z) (cs : list Z) : Prop :=
  match cs with
  | [] => True
  | c :: r => 2 * p <= c /\ geo c r
  end.

Lemma geo_firstn : forall cs p k, geo p cs -> geo p (firstn k cs).
Proof.
  induction cs as [|c cs IH]; intros p k H; destruct k as [|k]; cbn [firstn geo] in *; try exact I.
  destruct H as [H1 H2]. split; [exact H1 | exact (IH c k H2)].
Qed.

Lemma dbl_step : forall f c need, dbl (S f) c need = if need <=? c then c else dbl f (2 * c) need.
Proof. reflexivity. Qed.

(* pj_write's buffer: newcap doubles (from 4096) until the text fits *)
Lemma geo_grow_calls : forall ls x0 c, 0 <= c -> geo c (grow_calls x0 c ls).
Proof.
  induction ls as [|l ls IH]; intros x0 c Hc; cbn [grow_calls]; [exact I|].
  destruct (c <? x0 + l + 1) eqn:E; [|apply IH; exact Hc].
  apply Z.ltb_lt in E.
  assert (Hn : 2 * c <= newcap c (x0 + l + 1) /\ 0 <= newcap c (x0 + l + 1)).
  { unfold newcap. destruct (Z.eqb_spec c 0) as [Hc0|Hc0].
    - pose proof (PresetLiveBytes.dbl_ge 64 4096 (x0 + l + 1) ltac:(lia)). lia.
    - rewrite dbl_step. destruct (Z.leb_spec (x0 + l + 1) c); [lia|].
      pose proof (PresetLiveBytes.dbl_ge 63 (2 * c) (x0 + l + 1) ltac:(lia)). lia. }
  cbn [geo]. split; [lia | apply IH; lia].
Qed.

(* rendered ()'s buffer: tx_put's (n + k + 1) * 2 when the text outgrows cap *)
Lemma geo_tx_caps : forall ls n cap, geo cap (tx_caps n cap ls).
Proof.
  induction ls as [|k ls IH]; intros n cap; cbn [tx_caps]; [exact I|].
  destruct (cap <? n + k + 1) eqn:E; [|apply IH].
  apply Z.ltb_lt in E. cbn [geo]. split; [lia | apply IH].
Qed.

Lemma geo_ge : forall r c, 0 <= c -> geo c r -> Forall (fun z => 2 * c <= z) r.
Proof.
  induction r as [|z r IH]; intros c Hc H; [constructor|]. destruct H as [H1 H2]. constructor; [exact H1|].
  pose proof (IH z ltac:(lia) H2) as H. eapply Forall_impl; [|exact H]. cbv beta. intros w Hw. lia.
Qed.

(* a doubling list below U sums to at most 2 U *)
Lemma geo_sum : forall cs p U, 0 <= p <= U -> geo p cs -> Forall (fun c => c <= U) cs ->
  PresetLiveBytes.zsum cs <= 2 * U - 2 * p.
Proof.
  induction cs as [|c cs IH]; intros p U Hp Hg HU; [rewrite PresetLiveBytes.zsum_nil; lia|].
  destruct Hg as [H1 H2]. apply Forall_cons_iff in HU as [Hc HU].
  rewrite PresetLiveBytes.zsum_cons. pose proof (IH c U ltac:(lia) H2 HU). lia.
Qed.

Lemma cnt_all : forall f l, Forall (fun z => f z = true) l -> cnt f l = length l.
Proof.
  intros f l H. induction H as [|z l Hz H IH]; [reflexivity|].
  rewrite cnt_cons_eqR, Hz, IH. reflexivity.
Qed.

Lemma cnt_imp : forall f g l, (forall z, f z = true -> g z = true) -> (cnt f l <= cnt g l)%nat.
Proof.
  intros f g l H. induction l as [|z l IH]; [cbn; lia|]. rewrite !cnt_cons_eqR.
  destruct (f z) eqn:Ef; [rewrite (H z Ef); lia|]. destruct (g z); lia.
Qed.

(* a doubling list below U holds at most k capacities >= L when U < L * 2 ^ k *)
Lemma geo_cnt : forall cs p L U (k : nat), 0 <= p -> geo p cs -> Forall (fun c => c <= U) cs -> 0 < L ->
  U < L * 2 ^ Z.of_nat k -> (cnt (fun c => (L <=? c)%Z) cs <= k)%nat.
Proof.
  induction cs as [|c cs IH]; intros p L U k Hp Hg HU HL Hk; [cbn; lia|].
  destruct Hg as [H1 H2]. apply Forall_cons_iff in HU as [Hc HU].
  rewrite cnt_cons_eqR. cbv beta. destruct (Z.leb_spec L c) as [HLc|HLc].
  - destruct k as [|k].
    + change (Z.of_nat 0) with 0 in Hk. rewrite Z.pow_0_r in Hk. lia.
    + pose proof (geo_ge cs c ltac:(lia) H2) as G.
      assert (G1 : Forall (fun z => (L <=? z) = true) cs)
        by (eapply Forall_impl; [|exact G]; cbv beta; intros w Hw; apply Z.leb_le; lia).
      assert (G2 : Forall (fun z => (2 * L <=? z) = true) cs)
        by (eapply Forall_impl; [|exact G]; cbv beta; intros w Hw; apply Z.leb_le; lia).
      assert (E : cnt (fun c0 => L <=? c0) cs = cnt (fun c0 => 2 * L <=? c0) cs)
        by (rewrite (cnt_all (fun c0 => L <=? c0) cs G1), (cnt_all (fun c0 => 2 * L <=? c0) cs G2); reflexivity).
      assert (Hk' : U < 2 * L * 2 ^ Z.of_nat k).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hk by lia.
        replace (2 * L * 2 ^ Z.of_nat k) with (L * (2 * 2 ^ Z.of_nat k)) by ring. exact Hk. }
      rewrite E. pose proof (IH c (2 * L) U k ltac:(lia) H2 HU ltac:(lia) Hk'). lia.
  - pose proof (IH c L U k ltac:(lia) H2 HU HL Hk). lia.
Qed.

Lemma nsec_chain : forall hd cs old, nsec (chain hd old cs) = cnt (fun c => sec_req (c + hd)) cs.
Proof.
  intros hd cs. induction cs as [|c cs IH]; intros old; [reflexivity|].
  rewrite nsec_nprod in *. cbn [chain].
  destruct (old =? 0); cbn [nprodR prod_evR]; rewrite cnt_cons_eqR, IH; reflexivity.
Qed.

Lemma treq_chain : forall hd cs old, 0 <= hd -> Forall (fun c => 0 <= c) cs ->
  treq (chain hd old cs) <= PresetLiveBytes.zsum cs + hd * Z.of_nat (cnt (fun c => sec_req (c + hd)) cs).
Proof.
  intros hd cs. induction cs as [|c cs IH]; intros old Hhd Hcs; [cbn; lia|].
  apply Forall_cons_iff in Hcs as [Hc Hcs].
  cbn [chain]. rewrite PresetLiveBytes.zsum_cons, cnt_cons_eqR. cbv beta.
  pose proof (IH c Hhd Hcs).
  destruct (old =? 0); cbn [treq sec_rq]; destruct (sec_req (c + hd)); rewrite ?Nat2Z.inj_add; cbn [Z.of_nat];
    lia.
Qed.

(* a buffer grown through doubling capacities below U (head hd <= 16) *)
Lemma chain_nt : forall hd cs U (k : nat), 0 <= hd <= 16 -> 0 <= U -> geo 0 cs ->
  Forall (fun c => 0 < c <= U) cs -> U < 64497 * 2 ^ Z.of_nat k ->
  NT (chain hd 0 cs) (Z.of_nat k) (2 * U + 16 * Z.of_nat k).
Proof.
  intros hd cs U k Hhd HU Hg Hcs Hk.
  assert (Hle : Forall (fun c => c <= U) cs) by (eapply Forall_impl; [|exact Hcs]; cbv beta; intros z Hz; lia).
  assert (Hn : (cnt (fun c => sec_req (c + hd)%Z) cs <= k)%nat).
  { eapply Nat.le_trans; [apply (cnt_imp _ (fun c => 64497 <=? c))|].
    - intros z Hz. cbv beta in *. apply sec_req_lo in Hz. apply Z.leb_le. lia.
    - exact (geo_cnt cs 0 64497 U k ltac:(lia) Hg Hle ltac:(lia) Hk). }
  split.
  - rewrite nsec_chain. lia.
  - pose proof (treq_chain hd cs 0 ltac:(lia)
                  ltac:(eapply Forall_impl; [|exact Hcs]; cbv beta; intros z Hz; lia)) as T.
    pose proof (geo_sum cs 0 U ltac:(lia) Hg Hle) as S.
    assert (Hm : hd * Z.of_nat (cnt (fun c => sec_req (c + hd)) cs) <= 16 * Z.of_nat k).
    { apply Z.le_trans with (16 * Z.of_nat (cnt (fun c => sec_req (c + hd)) cs)); [|lia].
      apply Z.mul_le_mono_nonneg_r; lia. }
    lia.
Qed.

Lemma NT_wchain : forall t p U (k : nat), PresetLiveBytes.WCAP t p <= U -> U < 64497 * 2 ^ Z.of_nat k ->
  NT (w_evs t p) (Z.of_nat k) (2 * U + 16 * Z.of_nat k) /\
  (forall j, NT (w_starved t p j) (Z.of_nat k) (2 * U + 16 * Z.of_nat k)).
Proof.
  intros t p U k HW Hk. pose proof (PresetLiveBytes.WCAP_ge t p) as H4.
  assert (Hg : geo 0 (wcaps t p)) by (unfold wcaps; apply geo_grow_calls; lia).
  assert (Hc : Forall (fun c => 0 < c <= U) (wcaps t p)).
  { eapply Forall_impl; [|exact (PresetLiveBytes.wcaps_le t p)]. cbv beta. intros z Hz. lia. }
  split.
  - unfold w_evs. apply chain_nt; [unfold HEAD; lia | lia | exact Hg | exact Hc | exact Hk].
  - intros j. unfold w_starved.
    pose proof (chain_nt HEAD (firstn j (wcaps t p)) U k ltac:(unfold HEAD; lia) ltac:(lia)
                  (geo_firstn _ _ j Hg) (firstn_forall _ _ _ j Hc) Hk) as C.
    destruct j as [|j]; cbn beta iota.
    + rewrite app_nil_r. exact C.
    + eapply NT_weak; [exact (NT_app _ _ _ _ _ _ C (NT_free _)) | lia | lia].
Qed.

Lemma NT_rchain : forall t p U (k : nat), PresetLiveBytes.RCAP t p <= U -> U < 64497 * 2 ^ Z.of_nat k ->
  NT (r_evs t p) (Z.of_nat k) (2 * U + 16 * Z.of_nat k).
Proof.
  intros t p U k HR Hk. pose proof (PresetLiveBytes.RCAP_ge t p) as H2.
  unfold r_evs. apply chain_nt; [lia | lia | unfold rcaps; apply geo_tx_caps | | exact Hk].
  eapply Forall_impl; [|exact (PresetLiveBytes.rcaps_le t p)]. cbv beta. intros z Hz. lia.
Qed.

Lemma k13 : 112 * MAXB < 64497 * 2 ^ Z.of_nat 13.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma k9 : 6 * MAXB + 2 < 64497 * 2 ^ Z.of_nat 9.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Lemma NT_P : forall evs, NT evs (Z.of_nat 13) (2 * (112 * MAXB) + 16 * Z.of_nat 13) -> NT evs CH_P CHP_T.
Proof. intros evs H. eapply NT_weak; [exact H | unfold CH_P; lia | unfold CHP_T, CH_P; lia]. Qed.

Lemma NT_C : forall evs, NT evs (Z.of_nat 9) (2 * (6 * MAXB + 2) + 16 * Z.of_nat 9) -> NT evs CH_C CHC_T.
Proof. intros evs H. eapply NT_weak; [exact H | unfold CH_C; lia | unfold CHC_T, CH_C; lia]. Qed.

(* ================================================================ part 4: the segments of a call *)

Lemma reads_n : forall sm x, Z.of_nat (length x) <= MAXB ->
  (forall ok, Z.of_nat (nprodR sec_req (rd_hevs (rtr sm ok x))) <= RD_N) /\
  (forall t, fst (jr_run sm x []) = Some t -> Z.of_nat (nprodR sec_req (rd_hevs (ttrace t))) <= RB_N).
Proof.
  intros sm x Hx.
  assert (HG : forall e, ev_shape e -> is_grow e = true ->
     match req_ev e with Some r => sec_req (Z.of_nat r) = true -> (1024 <= wev JT_SEC e)%nat | None => True end)
    by (intros e He _; exact (sec_min e He)).
  assert (HS : forall e, ev_shape e -> is_grow e = false ->
     match req_ev e with Some r => sec_req (Z.of_nat r) = true -> (Z.to_nat 64496 <= chg_ev e)%nat | None => True end).
  { intros e _ Hg. destruct e as [n|m n|n|n]; cbn [req_ev is_grow] in *; try discriminate; try exact I.
    intros H. rewrite sec_req_iff in H. apply Z.leb_le in H. cbn [chg_ev]. lia. }
  destruct (w_reads JT_SEC sm x sec_req 1024 (Z.to_nat 64496) 1024 Hx ltac:(lia) ltac:(lia) ltac:(lia) HG HS)
    as [A B].
  rewrite Z2Nat.id in B by lia. change (Z.of_nat 1024) with 1024 in A, B.
  split; [exact A | exact B].
Qed.

Lemma NT_parse : forall sm x ok, Z.of_nat (length x) <= MAXB -> NT (parse_evs sm x ok) RD_N RD_T.
Proof.
  intros sm x ok Hx. split.
  - rewrite nsec_nprod, nprodR_parse. exact (proj1 (reads_n sm x Hx) ok).
  - unfold parse_evs. rewrite treq_app, treq_rd. unfold rtr. pose proof (rsum_read sm x ok).
    destruct (fst (jr_run sm x ok)); cbn [treq sec_rq]; unfold RD_T; lia.
Qed.

Lemma NT_starved : forall sm x k, Z.of_nat (length x) <= MAXB -> NT (starved_parse sm x k) RD_N RD_T.
Proof.
  intros sm x [|k] Hx; unfold starved_parse; [|apply NT_parse; exact Hx].
  pose proof consts_nn. eapply NT_weak; [exact NT_nil | lia | lia].
Qed.

Lemma NT_tfree : forall sm x o, NT (p1_tfree sm x o) 0 0.
Proof. intros sm x o. unfold p1_tfree. destruct (fst (jr_run sm x (okof o))); [apply NT_bulk | exact NT_nil]. Qed.

Lemma NT_tt : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (rd_hevs (ttrace t)) RB_N RB_T.
Proof.
  intros sm x t Hx Ht. split.
  - rewrite nsec_nprod. exact (proj2 (reads_n sm x Hx) t Ht).
  - rewrite treq_rd. pose proof (rsum_tt sm x t Ht).
    pose proof (PresetLiveBytes.SlotSizesPort.wlen_false_read sm x t Ht). unfold RB_T, RD_T. lia.
Qed.

Lemma NT_copy : forall sm x ms, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some (JObj ms) ->
  NT (rd_hevs (ttrace (copy_set ms))) (RB_N + 4) (RB_T + TOP_GROW_T).
Proof.
  intros sm x ms Hx H. split.
  - rewrite nsec_nprod. pose proof (PresetGate.g_nprod_copy sec_req ms).
    pose proof (proj2 (reads_n sm x Hx) _ H). lia.
  - rewrite treq_rd. destruct (NT_tt sm x (JObj ms) Hx H) as [_ T]. rewrite treq_rd in T.
    assert (HM : forall m c, In (EGrow m (56 * c)) (tgo_obj 0 0 ms) -> (c <= length x + 8)%nat).
    { intros m c Hin. rewrite <- tt_obj in Hin. exact (kids_le sm x _ H m c Hin). }
    pose proof (rsum_set ms 0 0 (length x + 8) ltac:(lia) HM) as R.
    unfold copy_set. rewrite tt_obj. rewrite tt_obj in T. unfold TOP_GROW_T. lia.
Qed.

Lemma NT_set : forall sm x ms, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some (JObj ms) ->
  NT (set_evs ms) 4 TOP_GROW_T.
Proof.
  intros sm x ms Hx H. split.
  - rewrite nsec_nprod. pose proof (set_evs_nprodR sec_req ms). lia.
  - pose proof (ncap_top sm x ms H) as Hc.
    unfold set_evs. cbn [treq].
    assert (E0 : sec_rq (HMal (Z.of_nat (S (length MOD_VAL)) + HEAD)) = 0) by (vm_compute; reflexivity).
    rewrite E0.
    pose proof consts_nn as (_ & _ & _ & _ & _ & _ & C7 & _).
    destruct (mfind ms) as [u|]; [cbn [treq sec_rq]; lia|].
    rewrite treq_rd, rsum_app. cbn [rsum].
    assert (E1 : rqZ (EAlloc (S (length MOD_KEY))) = 0) by (vm_compute; reflexivity). rewrite E1.
    pose proof (rsum_grow true (length ms) (PresetReqAt.ncap (length ms))).
    pose proof (gcap_bound (length ms) (PresetReqAt.ncap (length ms))). unfold TOP_GROW_T. lia.
Qed.

(* the file's tree t of x: its writer and rendered () chains *)
Lemma NT_wP : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (w_evs t true) CH_P CHP_T /\ forall j, NT (w_starved t true j) CH_P CHP_T.
Proof.
  intros sm x t Hx Ht.
  pose proof (PresetLiveBytes.SlotSizesPort.wlen_true_read sm x t Ht) as L.
  assert (HW : PresetLiveBytes.WCAP t true <= 112 * MAXB) by (unfold PresetLiveBytes.WCAP, MAXB in *; lia).
  destruct (NT_wchain t true _ 13 HW k13) as [A B]. split; [apply NT_P; exact A | intros j; apply NT_P; apply B].
Qed.

Lemma NT_rP : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (r_evs t true) CH_P CHP_T.
Proof.
  intros sm x t Hx Ht.
  pose proof (PresetLiveBytes.SlotSizesPort.wlen_true_read sm x t Ht) as L.
  assert (HR : PresetLiveBytes.RCAP t true <= 112 * MAXB) by (unfold PresetLiveBytes.RCAP, MAXB in *; lia).
  apply NT_P. exact (NT_rchain t true _ 13 HR k13).
Qed.

Lemma NT_wC : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (w_evs t false) CH_C CHC_T /\ forall j, NT (w_starved t false j) CH_C CHC_T.
Proof.
  intros sm x t Hx Ht.
  pose proof (PresetLiveBytes.SlotSizesPort.wlen_false_read sm x t Ht) as L.
  assert (HW : PresetLiveBytes.WCAP t false <= 6 * MAXB + 2) by (unfold PresetLiveBytes.WCAP, MAXB in *; lia).
  destruct (NT_wchain t false _ 9 HW k9) as [A B]. split; [apply NT_C; exact A | intros j; apply NT_C; apply B].
Qed.

Lemma NT_rC : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (r_evs t false) CH_C CHC_T.
Proof.
  intros sm x t Hx Ht.
  pose proof (PresetLiveBytes.SlotSizesPort.wlen_false_read sm x t Ht) as L.
  assert (HR : PresetLiveBytes.RCAP t false <= 6 * MAXB + 2) by (unfold PresetLiveBytes.RCAP, MAXB in *; lia).
  apply NT_C. exact (NT_rchain t false _ 9 HR k9).
Qed.

Lemma NT_rt_text : forall sm x t p nw bw, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (w_evs t p) nw bw -> NT (r_evs t p) nw bw -> NT (rt_text sm t p) (2 * nw + RB_N) (2 * bw + RB_T).
Proof.
  intros sm x t p nw bw Hx Ht Hw Hr.
  assert (Hwf : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ht).
  unfold rt_text. rewrite (parse_wf sm t p Hwf). unfold r_free, w_free.
  eapply NT_weak;
    [apply NT_app; [exact Hw | apply NT_app; [exact Hr | apply NT_app; [exact (NT_tt sm x t Hx Ht) |
       apply NT_app; apply NT_free]]] | lia | lia].
Qed.

Lemma NT_round_trip : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (round_trip sm t) (3 * RB_N + 8 + 3 * CH_P + 2 * CH_C) (3 * RB_T + 2 * TOP_GROW_T + 3 * CHP_T + 2 * CHC_T).
Proof.
  intros sm x t Hx Ht. pose proof consts_nn as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (Hwf : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ht).
  pose proof (NT_rt_text sm x t false _ _ Hx Ht (proj1 (NT_wC sm x t Hx Ht)) (NT_rC sm x t Hx Ht)) as RTf.
  pose proof (NT_rt_text sm x t true _ _ Hx Ht (proj1 (NT_wP sm x t Hx Ht)) (NT_rP sm x t Hx Ht)) as RTt.
  unfold round_trip.
  destruct t as [| | | txt bits | z | items | ms]; cbv beta iota;
    try (eapply NT_weak; [apply NT_app; [exact RTf | apply NT_app; [exact RTt | apply NT_app; apply NT_bulk]]
                         | lia | lia]).
  (* an object: the rewrite's pj_string / pj_set, writer, read-back of the copy *)
  assert (Hc : pj_wf sm (copy_set ms)) by exact (wf_copy sm ms Hwf).
  pose proof (PresetLiveBytes.SlotSizesPort.wlen_true_read sm x _ Ht) as L.
  pose proof (PresetLiveBytes.copy_len_true ms) as Lc.
  assert (HW : PresetLiveBytes.WCAP (copy_set ms) true <= 112 * MAXB)
    by (unfold PresetLiveBytes.WCAP, MAXB in *; lia).
  pose proof (NT_P _ (proj1 (NT_wchain (copy_set ms) true _ 13 HW k13))) as Wc.
  unfold rw_evs. rewrite (parse_wf sm (copy_set ms) true Hc). unfold w_free.
  eapply NT_weak;
    [apply NT_app; [exact RTf | apply NT_app; [exact RTt | apply NT_app; [apply NT_bulk |
       apply NT_app; [apply NT_app; [exact (NT_set sm x ms Hx Ht) | apply NT_app; [exact Wc |
         apply NT_app; [exact (NT_copy sm x ms Hx Ht) | apply NT_app; [apply NT_free | apply NT_bulk]]]]
       | apply NT_bulk]]]] | lia | lia].
Qed.

Lemma NT_starved_write : forall x t p rest n b nr br, NT (w_evs t p) n b ->
  (forall j, NT (w_starved t p j) n b) -> NT rest nr br -> NT (starved_write x t p rest) (2 * n + nr) (2 * b + br).
Proof.
  intros x t p rest n b nr br Hw Hs Hr. pose proof (NT_nn _ _ _ Hw). pose proof (NT_nn _ _ _ Hr).
  unfold starved_write, w_free.
  destruct (wcalls t p) as [|w]; cbv beta iota.
  - eapply NT_weak; [apply NT_app; [exact Hw | apply NT_app; [apply NT_free | exact NT_nil]] | lia | lia].
  - eapply NT_weak; [apply NT_app; [exact Hw | apply NT_app; [apply NT_free | apply NT_app; [apply Hs | exact Hr]]]
                    | lia | lia].
Qed.

Lemma NT_starved_writes : forall sm x t, Z.of_nat (length x) <= MAXB -> fst (jr_run sm x []) = Some t ->
  NT (starved_writes x t) (2 * CH_P + 2 * CH_C) (2 * CHP_T + 2 * CHC_T).
Proof.
  intros sm x t Hx Ht. unfold starved_writes.
  destruct (NT_wP sm x t Hx Ht) as [WP SP]. destruct (NT_wC sm x t Hx Ht) as [WC SC].
  eapply NT_weak; [eapply NT_starved_write; [exact WP | exact SP |
                   eapply NT_starved_write; [exact WC | exact SC | exact NT_nil]] | lia | lia].
Qed.

(* after check_no_overread: the main parse, expected ()'s scratch, the tail *)
Lemma NT_tail : forall sm x, Z.of_nat (length x) <= MAXB ->
  NT (call_tail sm x) (RD_N + 3 * RB_N + 8 + 5 * CH_P + 4 * CH_C)
                      (RD_T + 3 * RB_T + 2 * TOP_GROW_T + 5 * CHP_T + 4 * CHC_T).
Proof.
  intros sm x Hx. pose proof consts_nn as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  unfold call_tail. destruct (fst (jr_run sm x [])) as [t|] eqn:Ej.
  - eapply NT_weak;
      [apply NT_app; [exact (NT_round_trip sm x t Hx Ej) | apply NT_app; [apply NT_starved; exact Hx |
         apply NT_app; [exact (NT_starved_writes sm x t Hx Ej) | apply NT_bulk]]] | lia | lia].
  - eapply NT_weak; [apply NT_starved; exact Hx | lia | lia].
Qed.

Lemma NT_rest : forall sm x, Z.of_nat (length x) <= MAXB ->
  NT (call_rest sm x) (2 * RD_N + 3 * RB_N + 9 + 5 * CH_P + 4 * CH_C)
                      (2 * RD_T + (MAXB + 1) + 3 * RB_T + 2 * TOP_GROW_T + 5 * CHP_T + 4 * CHC_T).
Proof.
  intros sm x Hx. pose proof consts_nn as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  unfold call_rest. cbv zeta.
  eapply NT_weak;
    [apply NT_app; [apply NT_parse; exact Hx | apply NT_app; [apply (NT_app [HMal _] [HFr _]);
       [apply NT_mal; lia | apply NT_free] | exact (NT_tail sm x Hx)]] | lia | lia].
Qed.

(* ================================================================ part 5: a call, the run *)

Theorem NT_call : forall sm x o1 o2 o0, NT (call_evs sm x o1 o2 o0) NCALL TREQ_CALL.
Proof.
  intros sm x o1 o2 o0. pose proof consts_nn as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  rewrite call_evs_blocks.
  destruct (MAXB <? Z.of_nat (length x)) eqn:EB; cbv beta iota.
  { eapply NT_weak; [exact NT_nil | unfold NCALL; lia | unfold TREQ_CALL; lia]. }
  apply Z.ltb_ge in EB.
  assert (H3 : NT [HMal (Z.of_nat (length x) + FUZZ_PAD); HMal (Z.of_nat (length x) + FUZZ_PAD);
                   HMal (Z.of_nat (length x) + FUZZ_PAD)] 3 (3 * (Z.of_nat (length x) + FUZZ_PAD)))
    by (apply NT_mal3; unfold FUZZ_PAD; lia).
  assert (HCP : Z.of_nat (length x) + FUZZ_PAD <= MAXB + 16) by (unfold FUZZ_PAD; lia).
  destruct (ranout sm x o1); cbv beta iota.
  { eapply NT_weak; [apply NT_app; [exact H3 | apply NT_app; [apply NT_parse; exact EB | apply NT_fr3]]
                    | unfold NCALL; lia | unfold TREQ_CALL; lia]. }
  destruct (ranout sm x o2); cbv beta iota.
  { eapply NT_weak;
      [apply NT_app; [exact H3 | apply NT_app; [apply NT_app; apply NT_parse; exact EB |
         apply NT_app; [apply NT_tfree | apply NT_fr3]]] | unfold NCALL; lia | unfold TREQ_CALL; lia]. }
  assert (HR : NT (if ranout sm x o0 then [] else call_rest sm x)
                  (2 * RD_N + 3 * RB_N + 9 + 5 * CH_P + 4 * CH_C)
                  (2 * RD_T + (MAXB + 1) + 3 * RB_T + 2 * TOP_GROW_T + 5 * CHP_T + 4 * CHC_T)).
  { destruct (ranout sm x o0); [eapply NT_weak; [exact NT_nil | lia | lia] | exact (NT_rest sm x EB)]. }
  eapply NT_weak;
    [apply NT_app; [exact H3 | apply NT_app;
       [apply NT_app; [apply NT_parse; exact EB | apply NT_app; apply NT_parse; exact EB] |
        apply NT_app; [apply NT_app; [apply NT_tfree | apply NT_app; [apply NT_tfree | apply NT_app;
          [apply NT_tfree | apply NT_fr3]]] | exact HR]]]
    | unfold NCALL; lia | unfold TREQ_CALL; lia].
Qed.

(* ONE CALL: at most NCALL secondary requests, of at most TCALL mapped bytes (any x: above MAXB no event) *)
Theorem nsec_call : forall sm x o1 o2 o0, Z.of_nat (nsec (call_evs sm x o1 o2 o0)) <= NCALL.
Proof. intros sm x o1 o2 o0. exact (proj1 (NT_call sm x o1 o2 o0)). Qed.

Theorem tsec_call : forall sm x o1 o2 o0, tsec (call_evs sm x o1 o2 o0) <= TCALL.
Proof.
  intros sm x o1 o2 o0. destruct (NT_call sm x o1 o2 o0) as [N T].
  pose proof (tsec_treq (call_evs sm x o1 o2 o0)). unfold TCALL. unfold SEC_MAP_OVH in *. lia.
Qed.

Lemma NT_hruns : forall sm x os,
  NT (hruns sm x os) (Z.of_nat (length os) * NCALL) (Z.of_nat (length os) * TREQ_CALL).
Proof.
  intros sm x os. induction os as [|[[o1 o2] o0] os IH].
  - eapply NT_weak; [exact NT_nil | cbn; lia | cbn; lia].
  - rewrite hruns_cons. eapply NT_weak; [exact (NT_app _ _ _ _ _ _ (NT_call sm x o1 o2 o0) IH) | |];
      cbn [length]; rewrite Nat2Z.inj_succ, ?NCALL_value, ?TREQ_CALL_value; lia.
Qed.

(* THE RUN: target_run's at most 4 calls *)
Theorem nsec_run : forall sm x os, (length os <= 4)%nat -> Z.of_nat (nsec (hruns sm x os)) <= 4 * NCALL.
Proof.
  intros sm x os Hl. destruct (NT_hruns sm x os) as [N _]. rewrite NCALL_value in *. lia.
Qed.

Theorem tsec_run : forall sm x os, (length os <= 4)%nat -> tsec (hruns sm x os) <= 4 * TCALL.
Proof.
  intros sm x os Hl. destruct (NT_hruns sm x os) as [N T]. pose proof (tsec_treq (hruns sm x os)).
  unfold TCALL. rewrite NCALL_value, TREQ_CALL_value in *. unfold SEC_MAP_OVH in *. lia.
Qed.

(* and every prefix of it: each allocator call's entry and post *)
Corollary nsec_run_prefix : forall sm x os i, (length os <= 4)%nat ->
  Z.of_nat (nsec (firstn i (hruns sm x os))) <= 4 * NCALL.
Proof.
  intros sm x os i Hl. pose proof (nsec_prefix_le (hruns sm x os) i). pose proof (nsec_run sm x os Hl). lia.
Qed.

Corollary tsec_run_prefix : forall sm x os i, (length os <= 4)%nat -> tsec (firstn i (hruns sm x os)) <= 4 * TCALL.
Proof.
  intros sm x os i Hl. pose proof (tsec_prefix_le (hruns sm x os) i). pose proof (tsec_run sm x os Hl). lia.
Qed.

(* ================================================================ part 6: the meter is not vacuous *)

(* an input of 64,497 .. MAXB bytes: every call's three padded copies are secondaries, whatever the grants *)
Lemma sec_witness_call : forall sm x o1 o2 o0, 64497 <= Z.of_nat (length x) <= MAXB ->
  (3 <= nsec (call_evs sm x o1 o2 o0))%nat /\
  3 * YG00.sec_map_size (Z.of_nat (length x) + FUZZ_PAD) <= tsec (call_evs sm x o1 o2 o0).
Proof.
  intros sm x o1 o2 o0 Hx. rewrite call_evs_blocks.
  destruct (MAXB <? Z.of_nat (length x)) eqn:EB; [apply Z.ltb_lt in EB; lia|]. cbv beta iota.
  set (CP := Z.of_nat (length x) + FUZZ_PAD).
  assert (Hs : negb (PresetRoom.is_primary CP) = true).
  { change (sec_req CP = true). rewrite sec_req_iff. apply Z.leb_le. unfold CP, FUZZ_PAD. lia. }
  assert (H3 : forall rest, (3 <= nsec ([HMal CP; HMal CP; HMal CP] ++ rest))%nat /\
                            3 * YG00.sec_map_size CP <= tsec ([HMal CP; HMal CP; HMal CP] ++ rest)).
  { intros rest. rewrite nsec_app, tsec_app. unfold nsec. cbn [nprodR prod_evR tsec sec_mapped]. rewrite Hs.
    pose proof (tsec_nn rest). split; lia. }
  destruct (ranout sm x o1); cbv beta iota; [apply H3|].
  destruct (ranout sm x o2); cbv beta iota; apply H3.
Qed.

Lemma sec_witness_run : forall sm, exists x, Z.of_nat (length x) <= MAXB /\
  (0 < nsec (hruns sm x [(None, None, None)]))%nat /\ 0 < tsec (hruns sm x [(None, None, None)]).
Proof.
  intros sm. exists (repeat 32 (Z.to_nat 65536)).
  assert (Hl : Z.of_nat (length (repeat 32 (Z.to_nat 65536))) = 65536)
    by (rewrite repeat_length; apply Z2Nat.id; lia).
  destruct (sec_witness_call sm (repeat 32 (Z.to_nat 65536)) None None None ltac:(rewrite Hl; unfold MAXB; lia))
    as [W1 W2].
  rewrite Hl in W2. pose proof (sec_map_size_pos (65536 + FUZZ_PAD)).
  rewrite hruns_cons, nsec_app, tsec_app.
  assert (E : hruns sm (repeat 32 (Z.to_nat 65536)) [] = []) by reflexivity. rewrite E.
  cbn [tsec]. rewrite Hl. change (nsec []) with 0%nat.
  split; [unfold MAXB; lia|]. split; lia.
Qed.
