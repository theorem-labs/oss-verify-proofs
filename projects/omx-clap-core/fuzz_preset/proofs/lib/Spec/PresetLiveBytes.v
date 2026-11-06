(* omx-clap-core/fuzz_preset, Spec: blocks_bytes_bound_preset, the live-byte bound U4 (c-omx-hpreset's ruling
   13:23Z / 14:07Z, owner c-omx-alloc), and the lemmas it needs. Nothing here is a function's proof (rule 24);
   kind: model bound lemma.

   WHAT IT SAYS. At every allocator call of the harness run (the i-th event e of PresetRun.hruns sm x os, the
   position of PresetRoomPos.iface_room_pos), the live request bytes of the allocator state S plus the call's own
   request are at most LIVE_MAX = YG01.LIVE_MAX = 2 ^ 34, from Wf_cf, |x| <= MAXB and iface_room_pos only: the model
   bounds every request, so no request-bound premise is needed. The sharper form blocks_bytes_bound_preset_peak
   concludes <= LIVE_PEAK_PRESET = 10 ^ 10.

   HOW (the plan of a Theorem Labs lane's internal file LIVE-BYTES-PEAK.md section 5 / 6):
   - M1 blocks_bytes_room_pos: blocks_bytes S = the model's live bytes at position i + at most 3 driver blocks.
   - M2 blocks_req_lt_cf: every live request is below cf_malloc_max (Wf_cf's chunk_ok_cf), so the driver holds at
     most 3 * (cf_malloc_max - 1) <= DRV_BYTES.
   - M7 hruns_pos: position i of the k calls is position j of ONE call (the earlier calls are closed).
   - M6 call_bytes: at every position j of one call, live bytes + the next request <= CALL_PEAK |x|. Proved with
     pkB, the byte-weighted twin of PresetRun.pkR (the largest live sum plus next request over a run), segment by
     segment over PresetRun.call_evs_blocks: M3 rd_live_bytes (reader bytes = held + 16 per block) with
     PjGrammar.G10 / G7_4 / jr_esize_bound for every reading; PjRoundTrip.G9_trace (the read-back of wdoc t p is
     the trace of reading wdoc t false) for every read-back tree; the writer's and rendered()'s caps from the text
     length (PORT 1 and PORT 2 below); pj_string / pj_set's grow from the copy's own kids block.
   The per-call bound CALL_PEAK n = 2560 n + 131072 is coarser than the note's (2016 n + 67700 + max (2 ^ 27) (112 n)):
   it bounds the rendered and writer chains and the pj_set grow by simple sums instead of M8 / M9's exact bookkeeping.
   At MAXB: CALL_PEAK + DRV_BYTES = 8,053,194,752 + 1,607,467,005 = 9,660,661,757 <= LIVE_PEAK_PRESET = 10 ^ 10
   <= LIVE_MAX = 2 ^ 34.
   ENTRY SUMS (last section, row ENTRY-SUMS): every request of the run is nonnegative (ev_req_nn), so the peak bounds
   blocks_bytes S at any position (entry_sum_ok, entry_sum_pos) and the driver's blocks at a call boundary
   (entry_sum_closed), in the form the texts take at their entry: blocks_bytes S + n <= LIVE_MAX.

   CLOSURE: no lib/Prog/*_c.v and no Lib/LiaTwx2.v. The facts this leaf takes from files whose closure has them
   (lib/Prog/SlotSizes.v, lib/Spec/PresetFlush.v, lib/Prog/check_round_trip_m.v, lib/Spec/PjReqBoundW.v at
   origin/cold/c-frame-alloc-p8 d6092ab75a2) are PORTED below, each with its source cited. *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ PORT 1: the writer's text length
   VERBATIM from lib/Prog/SlotSizes.v (blob 2636bdfbb113) lines 8-397, inside this module so that no name meets
   SlotSizes.v's. ONE change: SlotSizes states wlen_false_read / wlen_true_read over PjWriteHyp.wlen t p, which is
   Z.of_nat (length (wdoc t p)) by definition (PjWriteHyp.v:18); here that body is written out, because PjWriteHyp.v
   Requires lib/Contract.v, lib/Prog/Ledger.v and the run kit (PjWriteHyp.v:1-12). SlotSizes.v itself Requires lib/Prog/check_round_trip_c.v (for crt_esz, :721,
   which is not ported), so it may not enter this leaf's closure. *)
Module SlotSizesPort.

Lemma ech_len : forall c, (length (ech c) <= 6)%nat.
Proof.
  intros c. unfold ech, esc.
  destruct (special c); [|cbn [length]; lia].
  destruct (c =? 34); [cbn [length]; lia|]. destruct (c =? 92); [cbn [length]; lia|].
  destruct (c =? 10); [cbn [length]; lia|]. destruct (c =? 9); [cbn [length]; lia|].
  destruct (c =? 13); cbn [length]; lia.
Qed.

Lemma ech_raw : forall c, 32 <= c -> c <> 34 -> c <> 92 -> ech c = [c].
Proof.
  intros c H1 H2 H3. unfold ech, special.
  rewrite (proj2 (Z.eqb_neq c 34) H2), (proj2 (Z.eqb_neq c 92) H3), (proj2 (Z.ltb_ge c 32) H1).
  reflexivity.
Qed.

Lemma fme_hi : forall l, Forall (fun b => 128 <= b) l -> length (flat_map ech l) = length l.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [Hb H]. cbn [flat_map].
  rewrite (ech_raw b ltac:(lia) ltac:(lia) ltac:(lia)). cbn [app length]. rewrite IH by exact H. reflexivity.
Qed.

Lemma fme_le : forall l, (length (flat_map ech l) <= 6 * length l)%nat.
Proof.
  induction l as [|b l IH]; [cbn; lia|]. cbn [flat_map length]. rewrite length_app.
  pose proof (ech_len b). lia.
Qed.

Lemma fme_utf8 : forall cp, (length (flat_map ech (utf8 cp)) <= 6)%nat.
Proof.
  intros cp. unfold utf8.
  destruct (cp <? 128) eqn:E1.
  - cbn [flat_map]. rewrite app_nil_r. apply ech_len.
  - apply Z.ltb_ge in E1.
    assert (G : forall l, Forall (fun b => 128 <= b) l -> (length l <= 4)%nat -> (length (flat_map ech l) <= 6)%nat)
      by (intros l Hl Hn; rewrite fme_hi by exact Hl; lia).
    destruct (cp <? 2048); [|destruct (cp <? 65536)]; cbv beta iota; apply G; cbn [length]; try lia;
      repeat constructor; cbv beta; Z.div_mod_to_equations; lia.
Qed.

Lemma decode_w : forall x s r, decode x = Some (s, r) ->
  (length (flat_map ech s) + 3 * length r + 3 <= 3 * length x)%nat.
Proof.
  assert (K : forall n x s r, (length x <= n)%nat -> decode x = Some (s, r) ->
    (length (flat_map ech s) + 3 * length r + 3 <= 3 * length x)%nat).
  { induction n as [|n IH]; intros x s r Hl H.
    - destruct x; [discriminate|cbn [length] in Hl; lia].
    - destruct x as [|b x0]; [discriminate|]. cbn [length] in Hl |- *. cbn [decode] in H.
      destruct (b =? 34) eqn:E34; cbv beta iota in H.
      { injection H as Es Er. subst s r. cbn [flat_map length]. lia. }
      destruct (b <? 32) eqn:E32; cbv beta iota in H; [discriminate|].
      destruct (negb (b =? 92)) eqn:E92; cbv beta iota in H.
      { unfold emit in H. destruct (decode x0) as [[s0 r0]|] eqn:Ed; [|discriminate].
        injection H as Es Er. subst s r. pose proof (IH x0 s0 r0 ltac:(lia) Ed) as I.
        apply Z.eqb_neq in E34. apply Z.ltb_ge in E32. apply negb_true_iff, Z.eqb_neq in E92.
        cbn [app flat_map]. rewrite (ech_raw b ltac:(lia) E34 E92). cbn [app length]. lia. }
      destruct x0 as [|e r2]; [discriminate|]. cbn [length] in Hl |- *.
      destruct (e =? 117) eqn:Eu; cbv beta iota in H.
      + destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; cbv beta iota in H; try discriminate.
        destruct (hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Eh; cbv beta iota in H; [|discriminate].
        destruct (cp =? 0); cbv beta iota in H; [discriminate|].
        destruct ((55296 <=? cp) && (cp <? 56320)); cbv beta iota in H.
        * destruct r3 as [|l0 [|l1 [|l2 [|l3 [|l4 [|l5 r4]]]]]]; cbv beta iota in H; try discriminate.
          destruct (low (l0 :: l1 :: l2 :: l3 :: l4 :: l5 :: r4)) as [lo|]; cbv beta iota in H; [|discriminate].
          unfold emit in H. destruct (decode r4) as [[s0 r0]|] eqn:Ed; [|discriminate].
          injection H as Es Er. subst s r. cbn [length] in Hl |- *.
          pose proof (IH r4 s0 r0 ltac:(lia) Ed) as I. pose proof (fme_utf8 (pair_cp cp lo)) as U.
          rewrite flat_map_app, length_app. lia.
        * destruct ((56320 <=? cp) && (cp <? 57344)); cbv beta iota in H; [discriminate|].
          unfold emit in H. destruct (decode r3) as [[s0 r0]|] eqn:Ed; [|discriminate].
          injection H as Es Er. subst s r. cbn [length] in Hl |- *.
          pose proof (IH r3 s0 r0 ltac:(lia) Ed) as I. pose proof (fme_utf8 cp) as U.
          rewrite flat_map_app, length_app. lia.
      + destruct (escape e) as [c|]; cbv beta iota in H; [|discriminate].
        unfold emit in H. destruct (decode r2) as [[s0 r0]|] eqn:Ed; [|discriminate].
        injection H as Es Er. subst s r.
        pose proof (IH r2 s0 r0 ltac:(lia) Ed) as I. pose proof (ech_len c) as U.
        cbn [app flat_map]. rewrite length_app. lia. }
  intros x s r H. exact (K (length x) x s r (Nat.le_refl _) H).
Qed.

Lemma name_w : forall o y ok nm y1 tn ok', jr_name o y ok = (Some (nm, y1), tn, ok') ->
  if o then (length (flat_map ech nm) + 3 * length y1 + 9 <= 3 * length y)%nat else y1 = y.
Proof.
  intros o y ok nm y1 tn ok' H. unfold jr_name in H. destruct o; cbv beta iota in H |- *.
  - destruct (skip y) as [|b z] eqn:Ey; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
    pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([nm0 r] & t1 & ok1 & t2 & Hs & H & _).
    pose proof (jr_string_spec z ok) as Hsp. rewrite Hs in Hsp. destruct Hsp as (q & _ & Hd & _ & Hl).
    pose proof (decode_w z nm0 r Hd) as D.
    cbv beta iota in H.
    destruct (skip r) as [|c r1] eqn:Er; cbv beta iota in H.
    + unfold jbind, jfree, jrefuse in H. cbv beta iota in H. discriminate H.
    + pose proof (skip_len r) as Hr. rewrite Er in Hr.
      destruct (c =? 58); cbv beta iota in H.
      * unfold jret in H. injection H as E1 E2 _ _. subst nm0 r1. cbn [length] in Hr. lia.
      * unfold jbind, jfree, jrefuse in H. cbv beta iota in H. discriminate H.
  - unfold jret in H. injection H as _ E _ _. symmetry. exact E.
Qed.

Lemma num_w : forall sm x ok u r t o, jr_number sm x ok = (Some (u, r), t, o) ->
  exists txt bits, u = JNum txt bits /\ (1 <= length txt)%nat /\ (length txt + length r = length x)%nat.
Proof.
  intros sm x ok u r t o H. unfold jr_number in H. cbv zeta in H.
  remember (match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) as j eqn:Ej.
  assert (Hj : (j <= length x)%nat).
  { rewrite Ej. destruct x as [|b x']; [cbn; lia|]. destruct (b =? 45); cbn [length]; lia. }
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c z] eqn:Ez; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end); cbv beta iota in H;
    [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:Es. cbv beta iota in H.
  pose proof (span_app _ _ _ _ Es) as Hz.
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _).
  destruct (whole sm (firstn j x ++ c :: a)); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as Hu Hr _ _. subst u r'.
  exists (firstn j x ++ c :: a), (snd (sm (firstn j x ++ c :: a))). split; [reflexivity|].
  rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk. rewrite Hz, length_app in Hsk.
  split; lia.
Qed.

Lemma prefixb_len : forall w x, prefixb w x = true -> (length w <= length x)%nat.
Proof.
  induction w as [|a w IH]; intros x H; [cbn; lia|].
  destruct x as [|b x]; [cbn in H; discriminate|].
  cbn [prefixb] in H. apply andb_true_iff in H as [_ H]. cbn [length]. specialize (IH x H). lia.
Qed.

Lemma lit_w : forall w v x ok u r t o, lit w v x ok = (Some (u, r), t, o) ->
  u = v /\ (length r + length w = length x)%nat.
Proof.
  intros w v x ok u r t o H. unfold lit in H.
  destruct (prefixb w x) eqn:Ep; [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as Hu Hr _ _. subst u r. split; [reflexivity|].
  rewrite length_skipn. pose proof (prefixb_len w x Ep). lia.
Qed.

Lemma rep_len : forall k, length (concat (repeat [32; 32] k)) = (2 * k)%nat.
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat]. rewrite concat_cons, length_app, IH. cbn [length]. lia.
Qed.

Definition indl (p : bool) (c : nat) : Z := if p then 1 + 2 * Z.of_nat c else 0.

Lemma wind_len : forall p c, Z.of_nat (length (concat (wind p (Z.of_nat c)))) = indl p c.
Proof.
  intros p c. unfold wind, indl. destruct p; [|reflexivity].
  rewrite concat_cons, length_app, Nat2Z.id, rep_len. cbn [length]. lia.
Qed.

Section W.
Variable sm : list Z -> Z * Z.
Variable pw : bool.
Variable wt : Z.
Variable al : nat -> Z.
Hypothesis HW : 3 <= wt.
Hypothesis HS : forall d, 1 - wt <= al d.
Hypothesis HC : forall c, (c < 32)%nat -> 2 - 2 * wt + indl pw (S c) + indl pw c + al (S c) <= al c.
Hypothesis HI : forall c, (c < 32)%nat -> 1 + indl pw (S c) - wt + al (S c) <= 0.

Definition Wv (d : nat) (v : jv) : Z := Z.of_nat (length (concat (wvpieces v pw (Z.of_nat d)))).

Definition wgo (o : bool) (c i : nat) (l : list (list Z * jv)) : list (list Z) :=
  if o then wgo_obj pw (Z.of_nat c) i l else wgo_arr pw (Z.of_nat c) i (map snd l).

Definition Lw (o : bool) (c i : nat) (l : list (list Z * jv)) : Z :=
  Z.of_nat (length (concat (wgo o c i l))) + indl pw c + 1.

Definition NP (o : bool) (nm : list Z) : Z :=
  if o then Z.of_nat (length (concat (spieces nm))) + Z.of_nat (length (wsep pw)) else 0.

Definition Bn (c i : nat) : Z := (if Nat.eqb i 0 then indl pw (S c) + al (S c) - wt else 0) + indl pw c + 1.

Lemma wm : forall a b, (a <= b)%nat -> wt * Z.of_nat a <= wt * Z.of_nat b.
Proof. intros a b H. apply Z.mul_le_mono_nonneg_l; lia. Qed.

Lemma wS : forall a, wt * Z.of_nat (S a) = wt + wt * Z.of_nat a.
Proof. intros a. rewrite Nat2Z.inj_succ. unfold Z.succ. ring. Qed.

Lemma wadd : forall a b, wt * Z.of_nat (a + b) = wt * Z.of_nat a + wt * Z.of_nat b.
Proof. intros a b. rewrite Nat2Z.inj_add. ring. Qed.

Lemma w3 : forall a b, (a <= b)%nat -> 3 * Z.of_nat b - 3 * Z.of_nat a <= wt * Z.of_nat b - wt * Z.of_nat a.
Proof. intros a b H. assert (0 <= Z.of_nat b - Z.of_nat a) by lia. nia. Qed.

Lemma w1 : forall k, (1 <= k)%nat -> Z.of_nat k - wt * Z.of_nat k <= 1 - wt.
Proof. intros k H. assert (1 <= Z.of_nat k) by lia. nia. Qed.

Lemma wnn : forall a, 0 <= wt * Z.of_nat a.
Proof. intros a. apply Z.mul_nonneg_nonneg; lia. Qed.

Lemma wv_mk : forall o c l, l <> [] -> Wv c (mk o l) = 1 + Lw o c 0 l.
Proof.
  intros o c l Hl. destruct l as [|m l']; [contradiction|]. clear Hl.
  pose proof (wind_len pw c) as Wd.
  unfold Wv, Lw, wgo, mk. destruct o; cbv beta iota; [rewrite wv_obj | rewrite wv_arr]; cbn [map]; cbv beta iota;
    rewrite concat_cons, !concat_app, !length_app; cbn [concat app length]; rewrite ?app_nil_r; lia.
Qed.

Lemma wv_mk0 : forall o c, Wv c (mk o []) = 2.
Proof. intros o c. unfold Wv, mk. destruct o; reflexivity. Qed.

Lemma wgo_nil : forall o c i, Z.of_nat (length (concat (wgo o c i []))) = 0.
Proof. intros o c i. unfold wgo. destruct o; reflexivity. Qed.

Lemma wgo_cons : forall o c i nm u r,
  Z.of_nat (length (concat (wgo o c i ((nm, u) :: r)))) =
  (if Nat.eqb i 0 then 0 else 1) + indl pw (S c) + NP o nm + Wv (S c) u +
  Z.of_nat (length (concat (wgo o c (S i) r))).
Proof.
  intros o c i nm u r. unfold wgo, NP, Wv.
  pose proof (wind_len pw (S c)) as Wd.
  replace (Z.of_nat (S c)) with (Z.of_nat c + 1) in * by lia.
  destruct o; cbn [wgo_obj wgo_arr map snd]; rewrite !concat_app, !length_app; unfold wcomma;
    destruct (Nat.eqb i 0); cbn [concat app length]; rewrite ?app_nil_r, ?length_app; lia.
Qed.

Lemma np_bound : forall o y ok nm y1 tn ok', jr_name o y ok = (Some (nm, y1), tn, ok') ->
  NP o nm + wt * Z.of_nat (length y1) <= wt * Z.of_nat (length y) /\ (length y1 <= length y)%nat.
Proof.
  intros o y ok nm y1 tn ok' H. pose proof (name_w o y ok nm y1 tn ok' H) as Hn. unfold NP.
  destruct o; cbv beta iota in Hn |- *.
  - assert (Ls : length (concat (spieces nm)) = (length (flat_map ech nm) + 2)%nat)
      by (rewrite wstr_eq; cbn [length]; rewrite length_app; cbn [length]; lia).
    assert (Lp : (length (wsep pw) <= 2)%nat) by (unfold wsep; destruct pw; cbn [length]; lia).
    pose proof (w3 (length y1) (length y) ltac:(lia)) as W3. split; lia.
  - subst y1. split; lia.
Qed.

Definition JRL (f : nat) : Prop := forall c o n cap acc y ok v r tr ok', (c < 32)%nat ->
  jrl sm f (S c) o n cap acc y ok = (Some (v, r), tr, ok') ->
  exists nw, nw <> [] /\ v = mk o (rev acc ++ nw) /\ (length r < length y)%nat /\
    Lw o c n nw + wt * Z.of_nat (length r) <= wt * Z.of_nat (length y) + Bn c n.

Lemma cont_w : forall f d o b y ok v r tr ok', JRL f ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (v, r), tr, ok') ->
  (length r < length (b :: y))%nat /\ Wv d v + wt * Z.of_nat (length r) <= wt * Z.of_nat (length (b :: y)) + al d.
Proof.
  intros f d o b y ok v r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  apply Nat.ltb_ge in Ed. unfold MAXD in Ed.
  cbn [tl] in H. cbv zeta in H. cbn [length].
  pose proof (wS (length y)) as E1. pose proof (HS d) as Hs.
  assert (LOOP : forall z, (length z <= length y)%nat -> jrl sm f (S d) o 0 0 [] z ok = (Some (v, r), tr, ok') ->
    (length r < S (length y))%nat /\ Wv d v + wt * Z.of_nat (length r) <= wt * Z.of_nat (S (length y)) + al d).
  { intros z Hz HL. destruct (IHl d o 0%nat 0%nat [] z ok v r tr ok' ltac:(lia) HL) as (nw & Hne & -> & Hr & B).
    cbn [rev app]. rewrite wv_mk by exact Hne. unfold Bn in B. cbn [Nat.eqb] in B.
    pose proof (HC d ltac:(lia)) as Hc. pose proof (wm _ _ Hz) as M. split; lia. }
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  { exact (LOOP [] ltac:(cbn [length]; lia) H). }
  destruct (c =? closer o); cbv beta iota in H.
  2: { exact (LOOP (c :: r0) ltac:(rewrite <- Ey; exact (skip_len y)) H). }
  unfold jret in H. injection H as Hv Hr _ _. subst v r.
  pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
  rewrite wv_mk0. pose proof (wm (S (S (length r0))) (S (length y)) ltac:(lia)) as M.
  pose proof (wS (S (length r0))) as E2. pose proof (wS (length r0)) as E3. split; lia.
Qed.

Lemma lit_case : forall wl V d x ok v r tr ok', wl <> [] -> Wv d V = Z.of_nat (length wl) ->
  lit wl V x ok = (Some (v, r), tr, ok') ->
  (length r < length x)%nat /\ Wv d v + wt * Z.of_nat (length r) <= wt * Z.of_nat (length x) + al d.
Proof.
  intros wl V d x ok v r tr ok' Hne HV H. destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl].
  assert (L1 : (1 <= length wl)%nat) by (destruct wl; [contradiction | cbn [length]; lia]).
  pose proof (wadd (length r) (length wl)) as E. rewrite Hl in E. pose proof (w1 _ L1) as W1. pose proof (HS d).
  rewrite HV. split; lia.
Qed.

Lemma w_fuel : forall f,
  (forall d x ok v r tr ok', jrv sm f d x ok = (Some (v, r), tr, ok') ->
     (length r < length x)%nat /\ Wv d v + wt * Z.of_nat (length r) <= wt * Z.of_nat (length x) + al d) /\
  JRL f.
Proof.
  induction f as [|f [IHv IHl]].
  - split; [|unfold JRL]; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok v r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (Fin : (length r < length (b :: y))%nat /\
          Wv d v + wt * Z.of_nat (length r) <= wt * Z.of_nat (length (b :: y)) + al d ->
          (length r < length x)%nat /\ Wv d v + wt * Z.of_nat (length r) <= wt * Z.of_nat (length x) + al d).
      { intros [A1 A2]. pose proof (skip_len x) as Hs'. rewrite Ex in Hs'. pose proof (wm _ _ Hs') as M.
        split; lia. }
      apply Fin. clear Fin.
      destruct (b =? 123); cbv beta iota in H; [exact (cont_w f d true b y ok v r tr ok' IHl H)|].
      destruct (b =? 91); cbv beta iota in H; [exact (cont_w f d false b y ok v r tr ok' IHl H)|].
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
        pose proof (jr_string_spec y ok) as Hs'. rewrite Hj in Hs'. destruct Hs' as (q & _ & Hd & _ & Hl).
        cbv beta iota in H. unfold jret in H. injection H as Hv Hr _ _. subst v r1.
        pose proof (decode_w y s r Hd) as D.
        assert (Ws : Wv d (JStr s) = Z.of_nat (length (flat_map ech s)) + 2).
        { unfold Wv. cbn [wvpieces]. rewrite wstr_eq. cbn [length]. rewrite length_app. cbn [length]. lia. }
        rewrite Ws. pose proof (w3 (length r) (length y) ltac:(lia)) as W3. pose proof (wS (length y)) as E.
        pose proof (HS d). cbn [length]. split; lia. }
      destruct (b =? 116); cbv beta iota in H.
      { exact (lit_case w_true JTrue d (b :: y) ok v r tr ok' ltac:(unfold w_true; discriminate) eq_refl H). }
      destruct (b =? 102); cbv beta iota in H.
      { exact (lit_case w_false JFalse d (b :: y) ok v r tr ok' ltac:(unfold w_false; discriminate) eq_refl H). }
      destruct (b =? 110); cbv beta iota in H.
      { exact (lit_case w_null JNull d (b :: y) ok v r tr ok' ltac:(unfold w_null; discriminate) eq_refl H). }
      destruct (num_w _ _ _ _ _ _ _ H) as (txt & bits & -> & H1 & Hl).
      assert (Wn : Wv d (JNum txt bits) = Z.of_nat (length txt))
        by (unfold Wv; cbn [wvpieces concat]; rewrite app_nil_r; reflexivity).
      rewrite Wn. pose proof (w1 _ H1) as W1. pose proof (wadd (length txt) (length r)) as E. rewrite Hl in E.
      pose proof (HS d). split; lia.
    + unfold JRL. intros c o n cap acc y ok v r tr ok' Hc H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      destruct (IHv (S c) y1 ok2 v0 r0 tv ok3 Ev) as (Hr0 & Bv).
      destruct (np_bound o y ok1 nm y1 tn ok2 En) as (Np & Ny).
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c' r1] eqn:Er; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      pose proof (HI c Hc) as Hi.
      pose proof (wm (S (length r1)) (length r0) ltac:(lia)) as M1. rewrite wS in M1.
      destruct (c' =? 44); cbv beta iota in H.
      { destruct (IHl c o (S n) cap1 ((nm, v0) :: acc) r1 ok3 v r t4 ok' Hc H) as (nw & Hne & Hv & Hr & B).
        exists ((nm, v0) :: nw). split; [discriminate|]. split.
        - rewrite Hv. cbn [rev]. rewrite <- app_assoc. reflexivity.
        - split; [lia|]. unfold Lw in *. rewrite wgo_cons. unfold Bn in *. cbn [Nat.eqb] in B.
          destruct (Nat.eqb n 0); cbv beta iota; lia. }
      destruct (c' =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as Hv Hr _ _. subst v r.
      exists [(nm, v0)]. split; [discriminate|]. split; [cbn [rev]; reflexivity|].
      split; [lia|]. unfold Lw. rewrite wgo_cons, wgo_nil. unfold Bn.
      destruct (Nat.eqb n 0); cbv beta iota; lia.
Qed.

Theorem w_read : forall x t, json_read sm x = Some t -> Wv 0 t <= wt * Z.of_nat (length x) + al 0.
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. destruct (proj1 (w_fuel _) 0%nat x [] t' r tr ok' E) as [_ B].
  pose proof (wnn (length r)). lia.
Qed.

End W.

Definition Gtab : list Z :=
  [-55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55; -55;
   -55; -55; -55; -37; -23; -13; -7; -5; -7; -13; -23; -37; -55].

Definition G (d : nat) : Z := nth d Gtab (-55).

Lemma G_table : forallb (fun c => (4 * Z.of_nat c - 106 + G (S c) <=? G c) && (2 * Z.of_nat c - 52 + G (S c) <=? 0))
  (seq 0 32) = true.
Proof. reflexivity. Qed.

Lemma G_lo : forall d, -55 <= G d.
Proof.
  intros d. unfold G. destruct (nth_in_or_default d Gtab (-55)) as [Hin| ->]; [|lia].
  assert (K : forallb (fun z => -55 <=? z) Gtab = true) by reflexivity.
  rewrite forallb_forall in K. apply Z.leb_le, K, Hin.
Qed.

Lemma G_step : forall c, (c < 32)%nat -> 4 * Z.of_nat c - 106 + G (S c) <= G c /\ 2 * Z.of_nat c - 52 + G (S c) <= 0.
Proof.
  intros c Hc. pose proof G_table as K. rewrite forallb_forall in K.
  specialize (K c (proj2 (in_seq 32 0 c) (conj (Nat.le_0_l c) Hc))).
  apply andb_true_iff in K as [K1 K2]. apply Z.leb_le in K1, K2. split; assumption.
Qed.

Theorem wlen_false_read : forall sm x t, json_read sm x = Some t -> Z.of_nat (length (wdoc t false)) <= 3 * Z.of_nat (length x).
Proof.
  intros sm x t H.
  assert (E : Z.of_nat (length (wdoc t false)) = Wv false 0 t).
  { unfold wdoc, wdpieces, Wv. cbv beta iota. rewrite app_nil_r. reflexivity. }
  rewrite E.
  enough (W : Wv false 0 t <= 3 * Z.of_nat (length x) + (fun _ => 0) 0%nat) by (cbv beta in W; lia).
  apply (w_read sm false 3 (fun _ => 0)); first [exact H | (intros; try unfold indl; cbv beta iota; lia)].
Qed.

Theorem wlen_true_read : forall sm x t, json_read sm x = Some t -> Z.of_nat (length (wdoc t true)) <= 56 * Z.of_nat (length x) - 54.
Proof.
  intros sm x t H.
  assert (E : Z.of_nat (length (wdoc t true)) = Wv true 0 t + 1).
  { unfold wdoc, wdpieces, Wv. change (Z.of_nat 0) with 0. cbv beta iota.
    rewrite concat_app, length_app. cbn [concat app length]. lia. }
  rewrite E.
  enough (W : Wv true 0 t <= 56 * Z.of_nat (length x) + G 0) by (change (G 0) with (-55) in W; lia).
  apply (w_read sm true 56 G); first [exact H | lia | exact G_lo |
    (intros c Hc; destruct (G_step c Hc) as [K1 K2]; unfold indl; cbv beta iota; lia) |
    (intros d; pose proof (G_lo d); lia)].
Qed.

End SlotSizesPort.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PresetReqAt PresetReqAtNoMiss PresetRun.

(* ================================================================ live bytes and the byte peak *)

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Lemma zsum_nil : zsum [] = 0.
Proof. reflexivity. Qed.

Lemma zsum_cons : forall a l, zsum (a :: l) = a + zsum l.
Proof. reflexivity. Qed.

Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a as [|x a IH]; intros b; [reflexivity|]. cbn [app]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_perm : forall a b, Permutation a b -> zsum a = zsum b.
Proof.
  intros a b H. induction H as [|x a b H IH|x y a|a b c H1 IH1 H2 IH2]; rewrite ?zsum_cons; lia.
Qed.

(* the request an allocator call makes: malloc n / realloc (_, n); a free asks for nothing *)
Definition ev_req (e : PresetReqAt.hev) : Z :=
  match e with PresetReqAt.HMal r => r | PresetReqAt.HRe _ r => r | _ => 0 end.

(* PresetRun.pkR with a byte weight: the largest live sum, or live sum plus the next event's request, over the
   states s, hstep s e1, ... of a run *)
Fixpoint pkB (s : list Z) (es : list hev) : Z :=
  match es with
  | [] => zsum s
  | e :: r => Z.max (zsum s + Z.max 0 (ev_req e)) (pkB (hstep s e) r)
  end.

Lemma pkB_ge : forall es s, zsum s <= pkB s es.
Proof. intros [|e r] s; cbn [pkB]; lia. Qed.

Lemma pkB_last : forall es s, zsum (hlive_from s es) <= pkB s es.
Proof.
  induction es as [|e r IH]; intros s; cbn [pkB]; [rewrite hlive_from_nil; lia|].
  rewrite hlive_from_cons. pose proof (IH (hstep s e)). lia.
Qed.

Lemma pkB_nth : forall es s j e, nth_error es j = Some e ->
  zsum (hlive_from s (firstn j es)) + ev_req e <= pkB s es.
Proof.
  induction es as [|e0 r IH]; intros s j e H; [destruct j; discriminate|].
  destruct j as [|j]; cbn [nth_error firstn] in H |- *.
  - injection H as <-. rewrite hlive_from_nil. cbn [pkB]. lia.
  - rewrite hlive_from_cons. cbn [pkB]. pose proof (IH (hstep s e0) j e H). lia.
Qed.

Lemma pkB_app : forall a b s, pkB s (a ++ b) = Z.max (pkB s a) (pkB (hlive_from s a) b).
Proof.
  induction a as [|e r IH]; intros b s.
  - cbn [app pkB]. rewrite hlive_from_nil. pose proof (pkB_ge b s). lia.
  - cbn [app pkB]. rewrite IH, hlive_from_cons. lia.
Qed.

Lemma pkB_one : forall s e, pkB s [e] = Z.max (zsum s + Z.max 0 (ev_req e)) (zsum (hstep s e)).
Proof. reflexivity. Qed.

Lemma pkB_perm : forall es a b, Permutation a b -> pkB a es = pkB b es.
Proof.
  induction es as [|e r IH]; intros a b H; cbn [pkB].
  - apply zsum_perm. exact H.
  - rewrite (zsum_perm a b H), (IH _ _ (hstep_perm e a b H)). reflexivity.
Qed.

(* a run that removes only its own blocks sees the blocks below it as a constant *)
Lemma pkB_frame : forall es a s, okf a es -> pkB (a ++ s) es = pkB a es + zsum s.
Proof.
  induction es as [|e r IH]; intros a s H; cbn [pkB].
  - apply zsum_app.
  - destruct H as [Hh Hr].
    assert (Hst : hstep (a ++ s) e = hstep a e ++ s).
    { destruct e as [n | m n | n | L]; cbn [hstep hits] in *.
      - reflexivity.
      - rewrite (rm1_app_l m a s Hh). reflexivity.
      - rewrite (rm1_app_l n a s Hh). reflexivity.
      - rewrite (rmall_app_in L a s Hh). reflexivity. }
    rewrite Hst, (IH _ s Hr), zsum_app. lia.
Qed.

Lemma pkB_frame0 : forall es s, okf [] es -> pkB s es = pkB [] es + zsum s.
Proof. intros es s H. exact (pkB_frame es [] s H). Qed.

(* ---------------------------------------------------------------- nonnegative requests *)

Definition nnl (s : list Z) : Prop := Forall (fun z => 0 <= z) s.

Definition evs_nn (es : list hev) : Prop := Forall (fun e => 0 <= ev_req e) es.

Fixpoint sumreq (es : list hev) : Z :=
  match es with [] => 0 | e :: r => Z.max 0 (ev_req e) + sumreq r end.

Lemma sumreq_app : forall a b, sumreq (a ++ b) = sumreq a + sumreq b.
Proof. induction a as [|e a IH]; intros b; cbn [app sumreq]; [lia|]. rewrite IH. lia. Qed.

Lemma sumreq_nn : forall es, 0 <= sumreq es.
Proof. induction es as [|e r IH]; cbn [sumreq]; lia. Qed.

Lemma nn_perm : forall a b, Permutation a b -> nnl a -> nnl b.
Proof.
  intros a b H Ha. unfold nnl in *. rewrite Forall_forall in *. intros z Hz.
  apply Ha. exact (Permutation_in z (Permutation_sym H) Hz).
Qed.

Lemma nn_app : forall a b, nnl a -> nnl b -> nnl (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.

Lemma nn_app_inv : forall a b, nnl (a ++ b) -> nnl a /\ nnl b.
Proof. intros a b H. apply Forall_app in H. exact H. Qed.

Lemma nn_subm : forall a b, subm a b -> nnl b -> nnl a.
Proof.
  intros a b [d H] Hb. apply (nn_perm _ _ H) in Hb. exact (proj1 (nn_app_inv _ _ Hb)).
Qed.

Lemma zsum_nn : forall a, nnl a -> 0 <= zsum a.
Proof. intros a H. induction H as [|x a Hx _ IH]; [reflexivity|]. rewrite zsum_cons. lia. Qed.

Lemma zsum_subm : forall a b, subm a b -> nnl b -> zsum a <= zsum b.
Proof.
  intros a b [d H] Hb. apply (nn_perm _ _ H) in Hb. destruct (nn_app_inv _ _ Hb) as [_ Hd].
  rewrite (zsum_perm _ _ H), zsum_app. pose proof (zsum_nn d Hd). lia.
Qed.

Lemma nn_hstep : forall s e, nnl s -> 0 <= ev_req e -> nnl (hstep s e).
Proof.
  intros s [n | m n | n | L] Hs He; cbn [hstep ev_req] in *.
  - constructor; assumption.
  - constructor; [exact He|]. exact (nn_subm _ _ (rm1_subm m s) Hs).
  - exact (nn_subm _ _ (rm1_subm n s) Hs).
  - exact (nn_subm _ _ (rmall_subm L s) Hs).
Qed.

Lemma zsum_hstep : forall s e, nnl s -> zsum (hstep s e) <= zsum s + Z.max 0 (ev_req e).
Proof.
  intros s [n | m n | n | L] Hs; cbn [hstep ev_req].
  - rewrite zsum_cons. lia.
  - rewrite zsum_cons. pose proof (zsum_subm _ _ (rm1_subm m s) Hs). lia.
  - pose proof (zsum_subm _ _ (rm1_subm n s) Hs). lia.
  - pose proof (zsum_subm _ _ (rmall_subm L s) Hs). lia.
Qed.

Lemma nn_hlive_from : forall es s, nnl s -> evs_nn es -> nnl (hlive_from s es).
Proof.
  induction es as [|e r IH]; intros s Hs He; [exact Hs|].
  inversion He as [|e' r' He1 He2]; subst. rewrite hlive_from_cons. apply IH; [|exact He2].
  exact (nn_hstep s e Hs He1).
Qed.

(* PresetRun.pkR_le with a byte weight: a run from a nonnegative heap peaks below the heap plus all its requests *)
Lemma pkB_le : forall es s, nnl s -> evs_nn es -> pkB s es <= zsum s + sumreq es.
Proof.
  induction es as [|e r IH]; intros s Hs He; cbn [pkB sumreq]; [lia|].
  inversion He as [|e' r' He1 He2]; subst.
  pose proof (zsum_hstep s e Hs). pose proof (IH (hstep s e) (nn_hstep s e Hs He1) He2).
  pose proof (sumreq_nn r). lia.
Qed.

(* ================================================================ M3: the reader's live bytes *)

Lemma rd_live_gen : forall P s, okf s (rd_hevs P) ->
  zsum (hlive_from s (rd_hevs P)) - HEAD * Z.of_nat (length (hlive_from s (rd_hevs P))) =
    zsum s - HEAD * Z.of_nat (length s) + held P /\
  (length (hlive_from s (rd_hevs P)) <= length s + calls P)%nat.
Proof.
  induction P as [|e P IH]; intros s H.
  - cbn [rd_hevs flat_map hlive_from fold_left held calls]. lia.
  - rewrite rd_hevs_cons in *. apply okf_app in H as [H1 H2].
    rewrite hlive_from_app. destruct (IH _ H2) as [E1 E2].
    assert (K : zsum (hlive_from s (rd_hev e)) - HEAD * Z.of_nat (length (hlive_from s (rd_hev e))) =
                  zsum s - HEAD * Z.of_nat (length s) + held_ev e /\
                (length (hlive_from s (rd_hev e)) <= length s + (if is_call e then 1 else 0))%nat).
    { destruct e as [n | [|m] n | n | n]; cbn [rd_hev hlive_from fold_left hstep held_ev is_call] in *.
      - cbn [length]. rewrite zsum_cons. unfold HEAD. lia.
      - cbn [length]. rewrite zsum_cons. unfold HEAD. lia.
      - destruct H1 as [Hin _]. pose proof (rm1_in _ _ Hin) as Hp.
        rewrite (zsum_perm _ _ Hp), (Permutation_length Hp). cbn [length]. rewrite !zsum_cons.
        unfold HEAD in *. lia.
      - lia.
      - destruct H1 as [Hin _]. pose proof (rm1_in _ _ Hin) as Hp.
        rewrite (zsum_perm _ _ Hp), (Permutation_length Hp). cbn [length]. rewrite !zsum_cons.
        unfold HEAD in *. lia. }
    destruct K as [K1 K2]. cbn [held calls]. destruct (is_call e); lia.
Qed.

(* M3: a reader trace's live bytes are what it holds plus one HEAD per live block, and it has at most one live
   block per call (the Spec twin of lib/Prog/PackTraceT.v:63 run_bytes, which Requires the plain AllocPack). *)
Theorem rd_live_bytes : forall P, okf [] (rd_hevs P) ->
  zsum (hlive (rd_hevs P)) = held P + HEAD * Z.of_nat (length (hlive (rd_hevs P))) /\
  (length (hlive (rd_hevs P)) <= calls P)%nat.
Proof.
  intros P H. destruct (rd_live_gen P [] H) as [E1 E2]. unfold hlive. rewrite zsum_nil in E1.
  cbn [length] in *. split; lia.
Qed.

(* ================================================================ one reading of a text y *)

(* the bytes of any prefix of one reading of a text of length m, heads included (G10 + G7_4 + M3) *)
Definition RDB (m : Z) : Z := 256 * m + 16416.
(* one reader request plus HEAD (jr_esize_bound) *)
Definition RDQ (m : Z) : Z := 56 * m + 464.

Lemma rd_prefix_bytes : forall sm y ok P R, snd (jr_run sm y ok) = P ++ R ->
  zsum (hlive (rd_hevs P)) <= RDB (Z.of_nat (length y)).
Proof.
  intros sm y ok P R E.
  pose proof (rd_okf_prefix sm y ok P R E) as K.
  destruct (rd_live_bytes P K) as [E1 E2].
  pose proof (G10 sm y ok P R E) as H1.
  pose proof (G7_4 sm y ok) as H2. rewrite E, calls_app in H2.
  unfold RDB, HEAD in *. lia.
Qed.

Lemma rd_req : forall sm y ok e h, In e (snd (jr_run sm y ok)) -> In h (rd_hev e) ->
  0 <= ev_req h <= RDQ (Z.of_nat (length y)).
Proof.
  intros sm y ok e h Hin Hh. pose proof (jr_esize_bound sm y ok e Hin) as B.
  destruct e as [n | [|m] n | n | n]; cbn [rd_hev] in Hh;
    first [destruct Hh as [<- | []] | destruct Hh]; cbn [ev_req esize] in *; unfold RDQ, HEAD; lia.
Qed.

Lemma rd_hevs_nn : forall tr, evs_nn (rd_hevs tr).
Proof.
  induction tr as [|e tr IH]; [constructor|]. rewrite rd_hevs_cons. apply Forall_app. split; [|exact IH].
  destruct e as [n | [|m] n | n | n]; cbn [rd_hev]; repeat constructor; cbn [ev_req]; unfold HEAD; lia.
Qed.

Lemma pk_rd0 : forall sm y ok R P, snd (jr_run sm y ok) = P ++ R ->
  pkB (hlive (rd_hevs P)) (rd_hevs R) <= RDB (Z.of_nat (length y)) + RDQ (Z.of_nat (length y)).
Proof.
  intros sm y ok R. induction R as [|e R IH]; intros P E.
  - cbn [rd_hevs flat_map pkB]. pose proof (rd_prefix_bytes sm y ok P [] E). unfold RDQ. lia.
  - rewrite rd_hevs_cons, pkB_app.
    assert (E' : snd (jr_run sm y ok) = (P ++ [e]) ++ R) by (rewrite E, <- app_assoc; reflexivity).
    pose proof (IH (P ++ [e]) E') as H2.
    assert (Hs : hlive_from (hlive (rd_hevs P)) (rd_hev e) = hlive (rd_hevs (P ++ [e]))).
    { unfold hlive. rewrite rd_hevs_app, hlive_from_app. cbn [rd_hevs flat_map]. rewrite app_nil_r. reflexivity. }
    rewrite Hs.
    pose proof (rd_prefix_bytes sm y ok P (e :: R) E) as B1.
    pose proof (rd_prefix_bytes sm y ok (P ++ [e]) R E') as B2.
    assert (Hin : In e (snd (jr_run sm y ok))) by (rewrite E; apply in_or_app; right; left; reflexivity).
    assert (H1 : pkB (hlive (rd_hevs P)) (rd_hev e) <= RDB (Z.of_nat (length y)) + RDQ (Z.of_nat (length y))).
    { pose proof (rd_hev_lenR e) as Hl.
      destruct (rd_hev e) as [|h [|h' l]] eqn:Eh; cbn [length] in Hl; try lia.
      - cbn [pkB]. unfold RDQ. lia.
      - rewrite pkB_one. cbn [hlive_from fold_left] in Hs. rewrite Hs.
        pose proof (rd_req sm y ok e h Hin ltac:(rewrite Eh; left; reflexivity)). lia. }
    lia.
Qed.

(* any reading of y, from any heap *)
Lemma pk_rd : forall sm y ok s,
  pkB s (rd_hevs (snd (jr_run sm y ok))) <= zsum s + RDB (Z.of_nat (length y)) + RDQ (Z.of_nat (length y)).
Proof.
  intros sm y ok s. rewrite (pkB_frame0 _ s (rd_okf sm y ok)).
  pose proof (pk_rd0 sm y ok (snd (jr_run sm y ok)) [] eq_refl) as H.
  unfold hlive in H. cbn [rd_hevs flat_map hlive_from fold_left] in H. lia.
Qed.

(* one pj_parse of y (a refusal then frees what it holds) *)
Lemma pk_parse : forall sm y ok s,
  pkB s (parse_evs sm y ok) <= zsum s + RDB (Z.of_nat (length y)) + RDQ (Z.of_nat (length y)).
Proof.
  intros sm y ok s. unfold parse_evs, rtr. rewrite pkB_app.
  pose proof (pk_rd sm y ok s) as H1.
  pose proof (pkB_last (rd_hevs (snd (jr_run sm y ok))) s) as H0.
  destruct (fst (jr_run sm y ok)) eqn:Ef.
  - cbn [pkB]. lia.
  - rewrite pkB_one.
    assert (HS : Permutation (hlive_from s (rd_hevs (snd (jr_run sm y ok)))) (pj_frees sm ok y ++ s)).
    { rewrite (rd_closed sm y ok s). apply Permutation_app_tail. apply Permutation_sym.
      pose proof (pj_frees_blocks sm ok y) as P. unfold rtr in P. exact P. }
    destruct (bulk_ok _ _ _ HS) as [_ B]. rewrite (zsum_perm _ _ B). cbn [ev_req].
    pose proof (pkB_ge (rd_hevs (snd (jr_run sm y ok))) s). lia.
Qed.

Lemma pacc_bytes : forall sm y ok, zsum (pacc sm y ok) <= RDB (Z.of_nat (length y)).
Proof.
  intros sm y ok. unfold pacc. destruct (fst (jr_run sm y ok)).
  - unfold rd_blocks, rtr. apply (rd_prefix_bytes sm y ok _ []). rewrite app_nil_r. reflexivity.
  - rewrite zsum_nil. unfold RDB. lia.
Qed.

Lemma nn_rd_blocks : forall tr, nnl (rd_blocks tr).
Proof. intros tr. unfold rd_blocks, hlive. apply nn_hlive_from; [constructor | apply rd_hevs_nn]. Qed.

Lemma nn_pacc : forall sm y ok, nnl (pacc sm y ok).
Proof. intros sm y ok. unfold pacc. destruct (fst (jr_run sm y ok)); [apply nn_rd_blocks | constructor]. Qed.

Lemma nn_tblk : forall t, nnl (tblk t).
Proof. intros t. exact (nn_perm _ _ (ttrace_blocks t) (nn_rd_blocks _)). Qed.

(* ---------------------------------------------------------------- a read-back: the trace of the compact text *)

Lemma tt_trace : forall sm t, pj_wf sm t -> ttrace t = snd (jr_run sm (wdoc t false) []).
Proof. intros sm t Hw. symmetry. exact (G9_trace sm t Hw false). Qed.

Lemma pk_tt : forall sm t s, pj_wf sm t ->
  pkB s (rd_hevs (ttrace t)) <=
    zsum s + RDB (Z.of_nat (length (wdoc t false))) + RDQ (Z.of_nat (length (wdoc t false))).
Proof. intros sm t s Hw. rewrite (tt_trace sm t Hw). apply pk_rd. Qed.

Lemma tblk_bytes : forall sm t, pj_wf sm t -> zsum (tblk t) <= RDB (Z.of_nat (length (wdoc t false))).
Proof.
  intros sm t Hw. rewrite <- (zsum_perm _ _ (ttrace_blocks t)). unfold rd_blocks. rewrite (tt_trace sm t Hw).
  apply (rd_prefix_bytes sm (wdoc t false) [] _ []). rewrite app_nil_r. reflexivity.
Qed.

(* ================================================================ PORT 2: rendered()'s text is the writer's text
   VERBATIM from lib/Spec/PresetFlush.v (blob 7aa21aabd93a) lines 402-475 (zsum_rep2 .. tx_len); indl / wind_len are
   SlotSizes.v's, here SlotSizesPort's. PresetFlush.v Requires lib/Prog/SlotSizes.v (so check_round_trip_c.v). *)
Lemma zsum_rep2 : forall n, zsum (repeat 2 n) = 2 * Z.of_nat n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat]. rewrite zsum_cons, IH. lia. Qed.

Lemma zsum_ind : forall (p : bool) (d : nat), zsum (if p then tx_line d else []) = SlotSizesPort.indl p d.
Proof.
  intros [|] d; unfold SlotSizesPort.indl; cbv beta iota; [|reflexivity].
  unfold tx_line. rewrite zsum_cons, zsum_rep2. reflexivity.
Qed.

Lemma tx_ch_len : forall c, zsum (tx_ch c) = Z.of_nat (length (ech c)).
Proof.
  intros c. unfold tx_ch, ech, special, esc.
  destruct (c =? 34); [reflexivity|]. cbn [orb].
  destruct (c =? 92); [reflexivity|]. cbn [orb].
  rewrite Z.ltb_antisym. destruct (32 <=? c); [reflexivity|]. cbn [negb].
  destruct (c =? 10); [reflexivity|]. destruct (c =? 9); [reflexivity|]. destruct (c =? 13); reflexivity.
Qed.

Lemma tx_str_len : forall s, zsum (tx_str s) = Z.of_nat (length (concat (spieces s))).
Proof.
  intros s. rewrite wstr_eq. unfold tx_str. rewrite zsum_cons, zsum_app, zsum_cons, zsum_nil.
  cbn [length]. rewrite length_app. cbn [length].
  assert (H : zsum (flat_map tx_ch s) = Z.of_nat (length (flat_map ech s))).
  { induction s as [|c s IH]; [reflexivity|]. cbn [flat_map]. rewrite zsum_app, length_app, IH, tx_ch_len. lia. }
  lia.
Qed.

Lemma tx_len : forall t p d, zsum (tx_val p d t) = Z.of_nat (length (concat (wvpieces t p (Z.of_nat d)))).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros p d.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [tx_val wvpieces concat]. rewrite app_nil_r, zsum_cons, zsum_nil. lia.
  - cbn [tx_val wvpieces]. apply tx_str_len.
  - rewrite tx_arr_eq, wv_arr.
    assert (Hgo : forall l i, Forall (fun u => forall p' d',
        zsum (tx_val p' d' u) = Z.of_nat (length (concat (wvpieces u p' (Z.of_nat d'))))) l ->
      zsum (txa p d i l) = Z.of_nat (length (concat (wgo_arr p (Z.of_nat d) i l)))).
    { induction l as [|u r IHl]; intros i Hf; [reflexivity|].
      apply Forall_cons_iff in Hf as [Hu Hr]. cbn [txa wgo_arr].
      rewrite !zsum_app, !concat_app, !length_app.
      replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
      rewrite (Hu p (S d)), (IHl (S i) Hr), zsum_ind.
      pose proof (SlotSizesPort.wind_len p (S d)) as W.
      assert (C : zsum (if Nat.eqb i 0 then [] else [1]) = Z.of_nat (length (concat (wcomma i))))
        by (unfold wcomma; destruct (Nat.eqb i 0); reflexivity).
      lia. }
    rewrite zsum_cons, !zsum_app, concat_cons, !concat_app, !length_app, (Hgo items 0%nat IH).
    assert (C : zsum (match items with [] => [] | _ :: _ => if p then tx_line d else [] end) =
                Z.of_nat (length (concat (match items with [] => [] | _ :: _ => wind p (Z.of_nat d) end)))).
    { destruct items; [reflexivity|]. rewrite zsum_ind, SlotSizesPort.wind_len. reflexivity. }
    rewrite zsum_cons, zsum_nil. cbn [length concat app]. lia.
  - rewrite tx_obj_eq, wv_obj.
    assert (Hgo : forall l i, Forall (fun m => forall p' d',
        zsum (tx_val p' d' (snd m)) = Z.of_nat (length (concat (wvpieces (snd m) p' (Z.of_nat d'))))) l ->
      zsum (txo p d i l) = Z.of_nat (length (concat (wgo_obj p (Z.of_nat d) i l)))).
    { induction l as [|[k u] r IHl]; intros i Hf; [reflexivity|].
      apply Forall_cons_iff in Hf as [Hu Hr]. cbn [snd] in Hu. cbn [txo wgo_obj].
      rewrite !zsum_app, !concat_app, !length_app.
      replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
      rewrite (Hu p (S d)), (IHl (S i) Hr), zsum_ind, tx_str_len.
      pose proof (SlotSizesPort.wind_len p (S d)) as W.
      assert (C : zsum (if Nat.eqb i 0 then [] else [1]) = Z.of_nat (length (concat (wcomma i))))
        by (unfold wcomma; destruct (Nat.eqb i 0); reflexivity).
      assert (C2 : zsum [1] + zsum (if p then [1] else []) = Z.of_nat (length (concat [wsep p])))
        by (destruct p; reflexivity).
      lia. }
    rewrite zsum_cons, !zsum_app, concat_cons, !concat_app, !length_app, (Hgo ms 0%nat IH).
    assert (C : zsum (match ms with [] => [] | _ :: _ => if p then tx_line d else [] end) =
                Z.of_nat (length (concat (match ms with [] => [] | _ :: _ => wind p (Z.of_nat d) end)))).
    { destruct ms; [reflexivity|]. rewrite zsum_ind, SlotSizesPort.wind_len. reflexivity. }
    rewrite zsum_cons, zsum_nil. cbn [length concat app]. lia.
Qed.

(* rendered (t, p)'s puts sum to the writer's text length (PresetFlush.v:478 rpieces_len, with rpieces unfolded) *)
Lemma rend_len : forall t p,
  zsum (tx_val p 0 t ++ (if p then [1] else [])) = Z.of_nat (length (wdoc t p)).
Proof.
  intros t p. unfold wdoc, wdpieces.
  pose proof (tx_len t p 0%nat) as E. change (Z.of_nat 0) with 0 in E.
  rewrite zsum_app, concat_app, length_app, E.
  destruct p; cbv beta iota; rewrite ?zsum_cons, ?zsum_nil; cbn [concat app length]; lia.
Qed.

(* ================================================================ PORT 3: the rewritten copy's text
   check_round_trip_m.v (blob 6fa8a67e4c56) :101-143 (crtm_wcomma_len, crtm_wgo_set, crtm_wdoc_len, crtm_obj_len,
   crt_len) and lib/Spec/PjReqBoundW.v at origin/cold/c-frame-alloc-p8 d6092ab75a2 (blob 0394d1a7ad83: wdoc_false_len,
   obj_len_false, crt_len_false), over PresetReqAt.copy_set ms = JObj (pj_set_model ms MOD_KEY (JStr MOD_VAL)), which
   is check_round_trip_c.crt_tree (JObj ms) (MOD_AT = MOD_KEY, STAMP = MOD_VAL byte for byte). Both sources Require
   lib/Prog/check_round_trip_c.v. Proofs verbatim but for those names. *)

Lemma crtm_wcomma_len : forall i, length (concat (wcomma i)) = (if Nat.eqb i 0 then 0 else 1)%nat.
Proof. intros [|i]; reflexivity. Qed.

Lemma crtm_wgo_set : forall p d k tv ms i,
  (length (concat (wgo_obj p d i (pj_set_model ms k tv))) <=
   length (concat (wgo_obj p d i ms)) + length (concat (wcomma (i + length ms))) +
   length (concat (wind p (d + 1))) + length (concat (spieces k)) + length (wsep p) +
   length (concat (wvpieces tv p (d + 1))))%nat.
Proof.
  intros p d k tv ms. induction ms as [|[k0 v0] r IH]; intros i; cbn [pj_set_model].
  - cbn [wgo_obj length]. rewrite Nat.add_0_r, !concat_app, concat_cons, !length_app. cbn [concat length]. lia.
  - destruct (list_eq_dec Z.eq_dec k0 k) as [E|E]; cbn [wgo_obj length].
    + rewrite !concat_app, !concat_cons, !length_app. lia.
    + specialize (IH (S i)). rewrite Nat.add_succ_r. rewrite Nat.add_succ_l in IH.
      rewrite !concat_app, !concat_cons, !length_app. lia.
Qed.

Lemma crtm_wdoc_len : forall t, length (wdoc t true) = (length (concat (wvpieces t true 0)) + 1)%nat.
Proof. intros t. unfold wdoc, wdpieces. rewrite concat_app, length_app. reflexivity. Qed.

Lemma crtm_obj_len : forall ms, length (concat (wvpieces (JObj ms) true 0)) =
  (2 + length (concat (wgo_obj true 0 0 ms)) + match ms with [] => 0 | _ :: _ => 1 end)%nat.
Proof.
  intros ms. rewrite wv_obj, concat_cons, !concat_app, !length_app.
  destruct ms as [|m r]; cbn [length concat app].
  - lia.
  - assert (W : length (concat (wind true 0)) = 1%nat) by reflexivity. rewrite W. lia.
Qed.

Lemma copy_len_true : forall ms, (length (wdoc (copy_set ms) true) <= length (wdoc (JObj ms) true) + 40)%nat.
Proof.
  intros ms. unfold copy_set. rewrite !crtm_wdoc_len, !crtm_obj_len.
  pose proof (crtm_wgo_set true 0 MOD_KEY (JStr MOD_VAL) ms 0) as H.
  assert (L1 : length (concat (wind true (0 + 1))) = 3%nat) by reflexivity.
  assert (L2 : length (concat (spieces MOD_KEY)) = 12%nat) by reflexivity.
  assert (L3 : length (wsep true) = 2%nat) by reflexivity.
  assert (L4 : length (concat (wvpieces (JStr MOD_VAL) true (0 + 1))) = 22%nat) by reflexivity.
  rewrite L1, L2, L3, L4, crtm_wcomma_len in H.
  destruct ms as [|[k v] r]; cbn [pj_set_model length Nat.add Nat.eqb] in *.
  - lia.
  - destruct (list_eq_dec Z.eq_dec k MOD_KEY); cbn [length] in *; lia.
Qed.

Lemma wdoc_false_len : forall u, length (wdoc u false) = length (concat (wvpieces u false 0)).
Proof. intros u. unfold wdoc, wdpieces. cbv beta iota. rewrite app_nil_r. reflexivity. Qed.

Lemma obj_len_false : forall ms, length (concat (wvpieces (JObj ms) false 0)) =
  (2 + length (concat (wgo_obj false 0 0 ms)))%nat.
Proof.
  intros ms. rewrite wv_obj, concat_cons, !concat_app, !length_app.
  destruct ms as [|m r]; cbn [length concat app wind]; lia.
Qed.

Lemma copy_len_false : forall ms, (length (wdoc (copy_set ms) false) <= length (wdoc (JObj ms) false) + 36)%nat.
Proof.
  intros ms. unfold copy_set. rewrite !wdoc_false_len, !obj_len_false.
  pose proof (crtm_wgo_set false 0 MOD_KEY (JStr MOD_VAL) ms 0%nat) as H.
  assert (L1 : length (concat (wind false (0 + 1))) = 0%nat) by reflexivity.
  assert (L2 : length (concat (spieces MOD_KEY)) = 12%nat) by reflexivity.
  assert (L3 : length (wsep false) = 1%nat) by reflexivity.
  assert (L4 : length (concat (wvpieces (JStr MOD_VAL) false (0 + 1))) = 22%nat) by reflexivity.
  rewrite L1, L2, L3, L4, crtm_wcomma_len in H.
  destruct (Nat.eqb (0 + length ms) 0); lia.
Qed.

(* ================================================================ the writer's and rendered()'s capacities *)

(* lib/Prog/PackTraceR.v:525-532 dbl_S / dbl_le and lib/Spec/PresetFlush.v:133 dbl_ge, ported (both Require
   plain *_c.v files) *)
Lemma dbl_le : forall f c need, dbl f c need <= Z.max c (2 * need - 1).
Proof.
  induction f as [|f IH]; intros c need; [cbn [dbl]; lia|]. cbn [dbl].
  destruct (Z.leb_spec need c); [lia|]. specialize (IH (2 * c) need). lia.
Qed.

Lemma dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (need <=? c); cbv beta iota; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma gc_le : forall ls x c, 0 <= x -> 0 <= c -> nnl ls ->
  forall d, In d (grow_calls x c ls) -> d <= Z.max (Z.max 4096 c) (2 * (x + zsum ls + 1)).
Proof.
  induction ls as [|l ls IH]; intros x c Hx Hc Hl d Hd; cbn [grow_calls] in Hd; [destruct Hd|].
  inversion Hl as [|l' ls' Hl1 Hl2]; subst. rewrite zsum_cons. pose proof (zsum_nn ls Hl2) as Z0.
  destruct (c <? x + l + 1) eqn:E.
  - set (c' := newcap c (x + l + 1)) in *.
    assert (Hc' : 0 <= c' <= Z.max (Z.max 4096 c) (2 * (x + l + 1) - 1)).
    { unfold c', newcap. destruct (c =? 0) eqn:E0.
      - pose proof (dbl_le 64 4096 (x + l + 1)). pose proof (dbl_ge 64 4096 (x + l + 1) ltac:(lia)). lia.
      - pose proof (dbl_le 64 c (x + l + 1)). pose proof (dbl_ge 64 c (x + l + 1) Hc). lia. }
    destruct Hd as [<- | Hd]; [lia|].
    pose proof (IH (x + l) c' ltac:(lia) ltac:(lia) Hl2 d Hd). lia.
  - pose proof (IH (x + l) c ltac:(lia) Hc Hl2 d Hd). lia.
Qed.

Lemma piece_lens_nn : forall P, nnl (piece_lens P).
Proof. induction P as [|b P IH]; [constructor|]. cbn [piece_lens map]. constructor; [lia | exact IH]. Qed.

Lemma zsum_piece_lens : forall P, zsum (piece_lens P) = Z.of_nat (length (concat P)).
Proof.
  induction P as [|b P IH]; [reflexivity|].
  cbn [piece_lens map]. rewrite zsum_cons. fold (piece_lens P). rewrite IH, concat_cons, length_app. lia.
Qed.

(* the writer's largest buffer (pj_write t p): 4096 doubled to hold the text and its NUL *)
Definition WCAP (t : jv) (p : bool) : Z := Z.max 4096 (2 * (Z.of_nat (length (wdoc t p)) + 1)).
(* rendered (t, p)'s largest buffer: twice the bytes put so far, plus one *)
Definition RCAP (t : jv) (p : bool) : Z := 2 * (Z.of_nat (length (wdoc t p)) + 1).

Lemma WCAP_ge : forall t p, 4096 <= WCAP t p.
Proof. intros t p. unfold WCAP. lia. Qed.

Lemma RCAP_ge : forall t p, 2 <= RCAP t p.
Proof. intros t p. unfold RCAP. lia. Qed.

Lemma wcaps_le : forall t p, Forall (fun c => 0 < c <= WCAP t p) (wcaps t p).
Proof.
  intros t p. pose proof (wcaps_pos t p) as Hp. rewrite Forall_forall in *. intros c Hc.
  split; [exact (Hp c Hc)|]. unfold wcaps in Hc.
  pose proof (gc_le _ 0 0 ltac:(lia) ltac:(lia) (piece_lens_nn _) c Hc) as H.
  rewrite zsum_piece_lens in H. unfold WCAP, wdoc. lia.
Qed.

Lemma txc_le : forall ls n cap, 0 <= n -> nnl ls ->
  forall d, In d (tx_caps n cap ls) -> d <= 2 * (n + zsum ls + 1).
Proof.
  induction ls as [|k ls IH]; intros n cap Hn Hl d Hd; cbn [tx_caps] in Hd; [destruct Hd|].
  inversion Hl as [|k' ls' Hk Hl2]; subst. rewrite zsum_cons. pose proof (zsum_nn ls Hl2) as Z0.
  destruct (cap <? n + k + 1).
  - destruct Hd as [<- | Hd]; [lia|]. pose proof (IH (n + k) _ ltac:(lia) Hl2 d Hd). lia.
  - pose proof (IH (n + k) cap ltac:(lia) Hl2 d Hd). lia.
Qed.

Lemma rcaps_le : forall t p, Forall (fun c => 0 < c <= RCAP t p) (rcaps t p).
Proof.
  intros t p. pose proof (rcaps_pos t p) as Hp. rewrite Forall_forall in *. intros c Hc.
  split; [exact (Hp c Hc)|]. unfold rcaps in Hc.
  assert (Hn : nnl (0 :: tx_val p 0 t ++ (if p then [1] else []))).
  { constructor; [lia|]. apply nn_app; [exact (nng_tx_val t p 0%nat)|].
    destruct p; repeat constructor; lia. }
  pose proof (txc_le _ 0 0 ltac:(lia) Hn c Hc) as H.
  rewrite zsum_cons, rend_len in H. unfold RCAP. lia.
Qed.

Lemma zlast_in : forall (l : list Z) d, l <> [] -> In (last l d) l.
Proof.
  induction l as [|a l IH]; intros d H; [contradiction|].
  destruct l as [|b l]; [left; reflexivity|].
  change (last (a :: b :: l) d) with (last (b :: l) d). right. apply IH. discriminate.
Qed.

Lemma wlast_le : forall t p, 0 < last (wcaps t p) 0 <= WCAP t p.
Proof.
  intros t p. destruct (wcaps_cons t p) as (c & r & E).
  pose proof (zlast_in (wcaps t p) 0 ltac:(rewrite E; discriminate)) as H.
  pose proof (wcaps_le t p) as F. rewrite Forall_forall in F. exact (F _ H).
Qed.

Lemma rlast_le : forall t p, 0 < last (rcaps t p) 0 <= RCAP t p.
Proof.
  intros t p. destruct (rcaps_cons t p) as (c & r & E).
  pose proof (zlast_in (rcaps t p) 0 ltac:(rewrite E; discriminate)) as H.
  pose proof (rcaps_le t p) as F. rewrite Forall_forall in F. exact (F _ H).
Qed.

(* ---------------------------------------------------------------- one buffer grown through its capacities *)

Lemma pk_chain_h : forall cs hd old s C, Forall (fun c => 0 < c <= C) cs -> 0 < old <= C -> 0 <= hd ->
  pkB ((old + hd) :: s) (chain hd old cs) <= zsum s + 2 * (C + hd).
Proof.
  induction cs as [|c cs IH]; intros hd old s C Hall Hold Hhd.
  - cbn [chain pkB]. rewrite zsum_cons. lia.
  - inversion Hall as [|c' cs' Hc Hall']; subst.
    cbn [chain]. rewrite (proj2 (Z.eqb_neq old 0)) by lia. cbn [pkB hstep ev_req]. rewrite rm1_cons_eq.
    pose proof (IH hd c s C Hall' Hc Hhd). rewrite zsum_cons. lia.
Qed.

Lemma pk_chain0 : forall cs hd s C, Forall (fun c => 0 < c <= C) cs -> 0 <= hd -> 0 <= C ->
  pkB s (chain hd 0 cs) <= zsum s + 2 * (C + hd).
Proof.
  intros [|c cs] hd s C Hall Hhd HC; cbn [chain]; [cbn [pkB]; lia|].
  inversion Hall as [|c' cs' Hc Hall']; subst. rewrite Z.eqb_refl. cbn [pkB hstep ev_req].
  pose proof (pk_chain_h cs hd c s C Hall' Hc Hhd). lia.
Qed.

Lemma pk_w_evs : forall t p s, pkB s (w_evs t p) <= zsum s + 2 * (WCAP t p + HEAD).
Proof.
  intros t p s. unfold w_evs. apply pk_chain0; [exact (wcaps_le t p) | unfold HEAD; lia | unfold WCAP; lia].
Qed.

Lemma pk_r_evs : forall t p s, pkB s (r_evs t p) <= zsum s + 2 * RCAP t p.
Proof.
  intros t p s. unfold r_evs. pose proof (pk_chain0 (rcaps t p) 0 s (RCAP t p) (rcaps_le t p)) as H.
  assert (0 <= RCAP t p) by (unfold RCAP; lia). specialize (H ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma pk_w_starved : forall t p k s, pkB s (w_starved t p k) <= zsum s + 2 * (WCAP t p + HEAD).
Proof.
  intros t p k s. unfold w_starved. rewrite pkB_app.
  assert (Hf : Forall (fun c => 0 < c <= WCAP t p) (firstn k (wcaps t p)))
    by exact (firstn_forall _ _ _ k (wcaps_le t p)).
  pose proof (pk_chain0 _ HEAD s (WCAP t p) Hf ltac:(unfold HEAD; lia) ltac:(unfold WCAP; lia)) as H1.
  pose proof (pkB_last (chain HEAD 0 (firstn k (wcaps t p))) s) as H0.
  destruct k as [|k]; [cbn [pkB]; lia|].
  assert (Hne : firstn (S k) (wcaps t p) <> []).
  { destruct (wcaps_cons t p) as (c & r & E). rewrite E. cbn [firstn]. discriminate. }
  destruct (chain_okf (firstn (S k) (wcaps t p)) HEAD s (firstn_forall _ _ _ (S k) (wcaps_pos t p))) as [_ H2].
  rewrite (H2 Hne) in H0 |- *. rewrite pkB_one. cbn [hstep ev_req]. rewrite rm1_cons_eq.
  pose proof (WCAP_ge t p). unfold HEAD in *. lia.
Qed.

Lemma pk_w_pair : forall t p s, pkB s (w_evs t p ++ w_free t p) <= zsum s + 2 * (WCAP t p + HEAD).
Proof.
  intros t p s. rewrite pkB_app. pose proof (pk_w_evs t p s) as H1.
  pose proof (pkB_last (w_evs t p) s) as H0.
  destruct (w_evs_ok t p s) as [_ W2]. rewrite W2 in H0 |- *. unfold w_free.
  rewrite pkB_one. cbn [hstep ev_req]. rewrite rm1_cons_eq. pose proof (WCAP_ge t p). unfold HEAD in *. lia.
Qed.

Lemma pk_starved_write : forall x t p rest s B, pkB s rest <= zsum s + B -> hlive_from s rest = s ->
  2 * (WCAP t p + HEAD) <= B -> pkB s (starved_write x t p rest) <= zsum s + B.
Proof.
  intros x t p rest s B Hr Hl HB. unfold starved_write.
  rewrite app_assoc, pkB_app. destruct (w_pair_ok t p s) as [_ P2]. rewrite P2.
  pose proof (pk_w_pair t p s).
  pose proof (pkB_ge rest s).
  destruct (wcalls t p) as [|m]; [cbn [pkB]; lia|].
  rewrite (pkB_app (w_starved t p (pick x (S m))) rest s), w_starved_live.
  pose proof (pk_w_starved t p (pick x (S m)) s). lia.
Qed.

Lemma pk_starved_writes : forall x t s,
  pkB s (starved_writes x t) <= zsum s + 2 * (Z.max (WCAP t true) (WCAP t false) + HEAD).
Proof.
  intros x t s. unfold starved_writes.
  destruct (starved_write_ok x t false [] s I eq_refl) as [_ A2].
  apply pk_starved_write; [| exact A2 | lia].
  pose proof (WCAP_ge t true). pose proof (WCAP_ge t false).
  apply pk_starved_write; [cbn [pkB]; unfold HEAD; lia | reflexivity | lia].
Qed.

(* ================================================================ the harness's segments, byte by byte *)

Local Ltac evnn := unfold evs_nn; try unfold w_free; try unfold r_free; cbn [app];
  repeat (match goal with |- Forall _ (_ :: _) => apply Forall_cons end);
  try (match goal with |- Forall _ [] => apply Forall_nil end); cbn [ev_req]; unfold HEAD; lia.

(* the length of the compact text of t: every read-back of t has the trace of reading it (G9_trace) *)
Definition Lf (t : jv) : Z := Z.of_nat (length (wdoc t false)).

(* ---------------------------------------------------------------- round_trip_text (t, p) *)

Definition BRT1 (t : jv) (p : bool) : Z := 2 * (WCAP t p + HEAD) + 2 * RCAP t p + RDB (Lf t) + RDQ (Lf t).

Lemma pk_rt_text0 : forall sm t p, pj_wf sm t -> pkB [] (rt_text sm t p) <= BRT1 t p.
Proof.
  intros sm t p Hw. unfold rt_text. rewrite (parse_wf sm t p Hw).
  pose proof (pk_w_evs t p []) as H1. rewrite zsum_nil in H1.
  pose proof (wlast_le t p) as HW. pose proof (rlast_le t p) as HR.
  pose proof (tblk_bytes sm t Hw) as HT. pose proof (WCAP_ge t p) as HWg. pose proof (RCAP_ge t p) as HRg.
  rewrite pkB_app. destruct (w_evs_ok t p []) as [_ W2]. rewrite W2.
  rewrite pkB_app. pose proof (pk_r_evs t p [last (wcaps t p) 0 + HEAD]) as H2.
  destruct (r_evs_ok t p [last (wcaps t p) 0 + HEAD]) as [_ R2]. rewrite R2.
  rewrite pkB_app.
  pose proof (pk_tt sm t [last (rcaps t p) 0 + 0; last (wcaps t p) 0 + HEAD] Hw) as H3.
  destruct (tt_ok t [last (rcaps t p) 0 + 0; last (wcaps t p) 0 + HEAD]) as [_ T2].
  assert (HX : nnl (hlive_from [last (rcaps t p) 0 + 0; last (wcaps t p) 0 + HEAD] (rd_hevs (ttrace t)))).
  { apply (nn_perm _ _ (Permutation_sym T2)). apply nn_app; [apply nn_tblk|].
    unfold HEAD in *. repeat constructor; lia. }
  assert (EvF : evs_nn (r_free t p ++ w_free t p)) by evnn.
  pose proof (pkB_le _ _ HX EvF) as H4. rewrite (zsum_perm _ _ T2) in H4.
  assert (S0 : sumreq (r_free t p ++ w_free t p) = 0) by reflexivity.
  rewrite !zsum_app, !zsum_cons, !zsum_nil in *.
  unfold BRT1. unfold Lf, RDB, RDQ, HEAD in *. lia.
Qed.

Lemma pk_rt_text : forall sm t p s, pj_wf sm t -> pkB s (rt_text sm t p) <= zsum s + BRT1 t p.
Proof.
  intros sm t p s Hw. rewrite (pkB_frame0 _ s (proj1 (rt_text_ok sm t p [] Hw))).
  pose proof (pk_rt_text0 sm t p Hw). lia.
Qed.

(* ---------------------------------------------------------------- pj_string / pj_set on the copy *)

(* the requests of pj_string and pj_set: the stamp (37), and on a miss the grow of the kids / keys arrays (at most
   twice the copy's arrays, or 464 + 80 from none) and the key (27) *)
Lemma set_sumreq : forall ms, sumreq (set_evs ms) <= 608 + 2 * zsum (tblk (JObj ms)).
Proof.
  intros ms. pose proof (zsum_nn _ (nn_tblk (JObj ms))) as N.
  unfold set_evs. cbn [sumreq ev_req].
  assert (Hv : Z.of_nat (S (length MOD_VAL)) + HEAD = 37) by reflexivity. rewrite Hv.
  destruct (mfind ms) as [u|].
  - cbn [sumreq ev_req]. lia.
  - rewrite rd_hevs_app, sumreq_app.
    assert (Hk : sumreq (rd_hevs [EAlloc (S (length MOD_KEY))]) = 27) by reflexivity. rewrite Hk.
    remember (ncap (length ms)) as cap eqn:Ecap.
    pose proof (tblk_array ms) as Ha. rewrite <- Ecap in Ha.
    unfold grow_ev, gcap. destruct (Nat.ltb (length ms) cap) eqn:El; [cbn [rd_hevs flat_map sumreq]; lia|].
    destruct cap as [|c].
    + cbn [Nat.eqb Nat.mul Nat.add rd_hevs flat_map rd_hev app sumreq ev_req]. unfold HEAD. lia.
    + cbn [Nat.eqb rd_hevs flat_map].
      rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)), (rd_hev_grow_S (8 * S c) _ ltac:(lia)).
      cbn [app sumreq ev_req]. cbn [arrz] in Ha.
      pose proof (zsum_subm _ _ Ha (nn_tblk _)) as Hz. rewrite !zsum_cons, zsum_nil in Hz.
      unfold HEAD in *. lia.
Qed.

(* pj_string's and pj_set's requests are nonnegative (lifted from pk_set's proof; ev_req_nn below uses it too) *)
Lemma set_evs_nn : forall ms, evs_nn (set_evs ms).
Proof.
  intros ms. unfold set_evs, evs_nn. constructor; [cbn [ev_req]; unfold HEAD; lia|].
  destruct (mfind ms); [constructor; [cbn [ev_req]; lia | constructor] | apply rd_hevs_nn].
Qed.

Lemma pk_set : forall ms, pkB (tblk (JObj ms)) (set_evs ms) <= 3 * zsum (tblk (JObj ms)) + 608.
Proof.
  intros ms. pose proof (set_evs_nn ms) as He.
  pose proof (pkB_le _ _ (nn_tblk (JObj ms)) He). pose proof (set_sumreq ms). lia.
Qed.

(* ---------------------------------------------------------------- round_trip_rewrite (:606-649) *)

Definition BRW (ms : list (list Z * jv)) : Z :=
  Z.max (3 * RDB (Lf (JObj ms)) + 608)
        (2 * RDB (Lf (copy_set ms)) + 2 * (WCAP (copy_set ms) true + HEAD) + RDQ (Lf (copy_set ms))).

Lemma pk_rw : forall sm ms, pj_wf sm (JObj ms) -> pkB (tblk (JObj ms)) (rw_evs sm ms) <= BRW ms.
Proof.
  intros sm ms Hw. pose proof (wf_copy sm ms Hw) as Hc.
  unfold rw_evs. rewrite (parse_wf sm (copy_set ms) true Hc).
  pose proof (pk_set ms) as H1. pose proof (tblk_bytes sm _ Hw) as Hm. pose proof (tblk_bytes sm _ Hc) as Hcb.
  pose proof (wlast_le (copy_set ms) true) as HW. pose proof (WCAP_ge (copy_set ms) true) as HWc.
  pose proof (zsum_nn _ (nn_tblk (copy_set ms))) as Zc. pose proof (zsum_nn _ (nn_tblk (JObj ms))) as Zm.
  rewrite pkB_app, (pkB_perm _ _ _ (set_tblk ms)).
  rewrite pkB_app. pose proof (pk_w_evs (copy_set ms) true (tblk (copy_set ms))) as H2.
  destruct (w_evs_ok (copy_set ms) true (tblk (copy_set ms))) as [_ W2]. rewrite W2.
  rewrite pkB_app.
  pose proof (pk_tt sm (copy_set ms) (last (wcaps (copy_set ms) true) 0 + HEAD :: tblk (copy_set ms)) Hc) as H3.
  destruct (tt_ok (copy_set ms) (last (wcaps (copy_set ms) true) 0 + HEAD :: tblk (copy_set ms))) as [_ T2].
  assert (HX : nnl (hlive_from (last (wcaps (copy_set ms) true) 0 + HEAD :: tblk (copy_set ms))
                              (rd_hevs (ttrace (copy_set ms))))).
  { apply (nn_perm _ _ (Permutation_sym T2)). apply nn_app; [apply nn_tblk|].
    constructor; [unfold HEAD; lia | apply nn_tblk]. }
  assert (EvF : evs_nn (w_free (copy_set ms) true ++ [HBulk (fo (copy_set ms))])) by evnn.
  pose proof (pkB_le _ _ HX EvF) as H4. rewrite (zsum_perm _ _ T2) in H4.
  assert (S0 : sumreq (w_free (copy_set ms) true ++ [HBulk (fo (copy_set ms))]) = 0) by reflexivity.
  rewrite !zsum_app, !zsum_cons in *.
  unfold BRW. unfold Lf, RDB, RDQ, HEAD in *. lia.
Qed.

(* ---------------------------------------------------------------- check_round_trip (:651-660) *)

Definition BRTT (t : jv) : Z :=
  Z.max (Z.max (BRT1 t false) (RDB (Lf t) + BRT1 t true))
        (Z.max (2 * RDB (Lf t))
               (match t with JObj ms => Z.max (BRW ms) (RDB (Lf (copy_set ms))) | _ => RDB (Lf t) end)).

Lemma pk_round_trip0 : forall sm t, pj_wf sm t -> pkB [] (round_trip sm t) <= BRTT t.
Proof.
  intros sm t Hw. unfold round_trip.
  pose proof (tblk_bytes sm t Hw) as HT. fold (Lf t) in HT.
  pose proof (nn_tblk t) as NT. pose proof (zsum_nn _ NT) as ZT.
  rewrite pkB_app. pose proof (pk_rt_text sm t false [] Hw) as H1. rewrite zsum_nil in H1.
  destruct (rt_text_ok sm t false [] Hw) as [_ A2]. rewrite app_nil_r in A2.
  rewrite pkB_app. pose proof (pk_rt_text sm t true (hlive_from [] (rt_text sm t false)) Hw) as H2.
  rewrite (zsum_perm _ _ A2) in H2.
  destruct (rt_text_ok sm t true (hlive_from [] (rt_text sm t false)) Hw) as [_ B2].
  assert (HS2 : Permutation (hlive_from (hlive_from [] (rt_text sm t false)) (rt_text sm t true)) (tblk t ++ tblk t)).
  { apply (Permutation_trans B2). apply Permutation_app_head. exact A2. }
  assert (N2 : nnl (hlive_from (hlive_from [] (rt_text sm t false)) (rt_text sm t true))).
  { apply (nn_perm _ _ (Permutation_sym HS2)). apply nn_app; exact NT. }
  rewrite pkB_app.
  pose proof (pkB_le [HBulk (fo t)] _ N2 ltac:(evnn)) as H3. cbn [sumreq ev_req] in H3.
  rewrite (zsum_perm _ _ HS2), zsum_app in H3.
  assert (HS3 : Permutation (hlive_from (hlive_from (hlive_from [] (rt_text sm t false)) (rt_text sm t true))
                               [HBulk (fo t)]) (tblk t)).
  { assert (P : Permutation (hlive_from (hlive_from [] (rt_text sm t false)) (rt_text sm t true))
                            (fo t ++ tblk t)).
    { apply (Permutation_trans HS2). apply Permutation_app_tail. apply Permutation_sym. apply fo_tblk. }
    destruct (bulk_ok (fo t) _ (tblk t) P) as [_ C2]. cbn [hlive_from fold_left]. exact C2. }
  set (S3 := hlive_from (hlive_from (hlive_from [] (rt_text sm t false)) (rt_text sm t true)) [HBulk (fo t)]) in *.
  assert (N3 : nnl S3) by exact (nn_perm _ _ (Permutation_sym HS3) NT).
  assert (H4 : pkB S3 (match t with JObj ms => rw_evs sm ms ++ [HBulk (fo (copy_set ms))] | _ => [HBulk (fo t)] end) <=
               match t with JObj ms => Z.max (BRW ms) (RDB (Lf (copy_set ms))) | _ => RDB (Lf t) end).
  { destruct t as [| | | txt bits | z | items | ms]; cbv beta iota.
    1-6: (match goal with |- pkB ?S ?L <= _ => pose proof (pkB_le L S N3 ltac:(evnn)) as P end;
          cbn [sumreq ev_req] in P; rewrite (zsum_perm _ _ HS3) in P; lia).
    rewrite (pkB_perm _ _ _ HS3), pkB_app. pose proof (pk_rw sm ms Hw) as R1.
    pose proof (wf_copy sm ms Hw) as Hc.
    destruct (rw_ok sm ms (tblk (JObj ms)) Hw (Permutation_refl _)) as [_ R2].
    assert (HS4 : Permutation (hlive_from (tblk (JObj ms)) (rw_evs sm ms)) (tblk (copy_set ms)))
      by (apply (Permutation_trans R2); apply set_tblk).
    rewrite (pkB_perm _ _ _ HS4).
    pose proof (pkB_le [HBulk (fo (copy_set ms))] (tblk (copy_set ms)) (nn_tblk _) ltac:(evnn)) as P.
    cbn [sumreq ev_req] in P. pose proof (tblk_bytes sm _ Hc) as Hcb. fold (Lf (copy_set ms)) in Hcb. lia. }
  unfold BRTT. lia.
Qed.

Lemma pk_round_trip : forall sm t s, pj_wf sm t -> pkB s (round_trip sm t) <= zsum s + BRTT t.
Proof.
  intros sm t s Hw. rewrite (pkB_frame0 _ s (proj1 (round_trip_ok sm t Hw))).
  pose proof (pk_round_trip0 sm t Hw). lia.
Qed.

(* ---------------------------------------------------------------- after check_no_overread *)

Lemma pk_starved : forall sm x s, pkB s (starved_parse sm x (calls (rtr sm [] x))) <=
  zsum s + RDB (Z.of_nat (length x)) + RDQ (Z.of_nat (length x)).
Proof.
  intros sm x s. unfold starved_parse. destruct (calls (rtr sm [] x)); [cbn [pkB]; unfold RDB, RDQ; lia|].
  apply pk_parse.
Qed.

(* the accepted path's own peak above the doc tree: the round trips, or the starved writes *)
Definition TLB (sm : list Z -> Z * Z) (x : list Z) : Z :=
  match fst (jr_run sm x []) with
  | Some t => Z.max (BRTT t) (2 * (Z.max (WCAP t true) (WCAP t false) + HEAD))
  | None => 0
  end.

Lemma pk_tail : forall sm x, pkB (pacc sm x []) (call_tail sm x) <=
  RDB (Z.of_nat (length x)) + Z.max (RDB (Z.of_nat (length x)) + RDQ (Z.of_nat (length x))) (TLB sm x).
Proof.
  intros sm x. pose proof (pacc_bytes sm x []) as HL. pose proof (nn_pacc sm x []) as NL.
  pose proof (zsum_nn _ NL) as ZL.
  assert (RBn : 0 <= RDB (Z.of_nat (length x))) by (unfold RDB; lia).
  assert (RQn : 0 <= RDQ (Z.of_nat (length x))) by (unfold RDQ; lia).
  unfold call_tail, TLB. unfold pacc in HL, NL, ZL |- *.
  destruct (fst (jr_run sm x [])) as [t|] eqn:Ej.
  - assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ej).
    set (Lr := rd_blocks (rtr sm [] x)) in *.
    rewrite (pkB_app (round_trip sm t)). pose proof (pk_round_trip sm t Lr Hw) as H1.
    destruct (round_trip_ok sm t Hw) as [R1 R2].
    assert (HR : Permutation (hlive_from Lr (round_trip sm t)) Lr).
    { rewrite (hlive_okf _ Lr R1). apply (Permutation_trans (Permutation_app_tail Lr R2)). apply Permutation_refl. }
    rewrite (pkB_perm _ _ _ HR).
    rewrite (pkB_app (starved_parse sm x (calls (rtr sm [] x)))), (proj2 (starved_ok sm x Lr)).
    rewrite (pkB_app (starved_writes x t)), (proj2 (starved_writes_ok x t Lr)).
    pose proof (pk_starved sm x Lr) as H2. pose proof (pk_starved_writes x t Lr) as H3.
    pose proof (pkB_le [HBulk (pj_frees sm [] x)] Lr NL ltac:(evnn)) as H4. cbn [sumreq ev_req] in H4.
    lia.
  - pose proof (pk_starved sm x []) as H. rewrite zsum_nil in H. lia.
Qed.

Lemma pk_rest : forall sm x, pkB [] (call_rest sm x) <=
  RDB (Z.of_nat (length x)) +
  Z.max (RDB (Z.of_nat (length x)) + RDQ (Z.of_nat (length x))) (Z.max (Z.of_nat (length x) + 1) (TLB sm x)).
Proof.
  intros sm x. unfold call_rest. cbv zeta.
  pose proof (pacc_bytes sm x []) as HL. pose proof (nn_pacc sm x []) as NL. pose proof (zsum_nn _ NL) as ZL.
  assert (RBn : 0 <= RDB (Z.of_nat (length x))) by (unfold RDB; lia).
  assert (RQn : 0 <= RDQ (Z.of_nat (length x))) by (unfold RDQ; lia).
  rewrite pkB_app. pose proof (pk_parse sm x [] []) as H1. rewrite zsum_nil in H1.
  destruct (parse_ok sm x [] []) as [_ P2]. rewrite app_nil_r in P2. rewrite P2.
  rewrite pkB_app.
  pose proof (pkB_le [HMal (Z.of_nat (length x) + 1); HFr (Z.of_nat (length x) + 1)] _ NL ltac:(evnn)) as H2.
  cbn [sumreq ev_req] in H2.
  assert (HS : hlive_from (pacc sm x []) [HMal (Z.of_nat (length x) + 1); HFr (Z.of_nat (length x) + 1)] =
               pacc sm x []).
  { cbn [hlive_from fold_left hstep]. apply rm1_cons_eq. }
  rewrite HS. pose proof (pk_tail sm x) as H3. lia.
Qed.

(* ---------------------------------------------------------------- one call *)

Lemma evs_nn_tfree : forall sm x o, evs_nn (p1_tfree sm x o).
Proof. intros sm x o. unfold p1_tfree. destruct (fst (jr_run sm x (okof o))); evnn. Qed.

Lemma evs_nn_app : forall a b, evs_nn a -> evs_nn b -> evs_nn (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.

Local Ltac maxsplit := repeat match goal with |- Z.max _ _ <= _ => apply Z.max_lub end.
Local Ltac to_l A := apply (Z.le_trans _ A); [|apply Z.le_max_l].
Local Ltac to_r B := apply (Z.le_trans _ B); [|apply Z.le_max_r].

Lemma pk_call0 : forall sm x o1 o2 o0, pkB [] (call_evs sm x o1 o2 o0) <=
  Z.max (3 * (Z.of_nat (length x) + FUZZ_PAD) + 3 * RDB (Z.of_nat (length x)) + RDQ (Z.of_nat (length x)))
        (RDB (Z.of_nat (length x)) +
         Z.max (RDB (Z.of_nat (length x)) + RDQ (Z.of_nat (length x)))
               (Z.max (Z.of_nat (length x) + 1) (TLB sm x))).
Proof.
  intros sm x o1 o2 o0. rewrite call_evs_blocks.
  remember (Z.of_nat (length x)) as n eqn:En.
  remember (3 * (n + FUZZ_PAD) + 3 * RDB n + RDQ n) as A eqn:EA.
  remember (RDB n + Z.max (RDB n + RDQ n) (Z.max (n + 1) (TLB sm x))) as B eqn:EB.
  assert (Hn : 0 <= n) by (subst n; lia).
  assert (RBn : 0 <= RDB n) by (unfold RDB; lia).
  assert (RQn : 0 <= RDQ n) by (unfold RDQ; lia).
  remember (n + FUZZ_PAD) as CP eqn:ECP.
  assert (HCP : 16 <= CP) by (subst CP; unfold FUZZ_PAD; lia).
  assert (HAB : 0 <= A) by (subst A; lia).
  destruct (MAXB <? n); [cbn [pkB]; rewrite zsum_nil; lia|].
  assert (H3 : pkB [] [HMal CP; HMal CP; HMal CP] <= 3 * CP).
  { pose proof (pkB_le [HMal CP; HMal CP; HMal CP] [] ltac:(constructor) ltac:(evnn)) as P.
    assert (S3 : sumreq [HMal CP; HMal CP; HMal CP] = 3 * CP) by (cbn [sumreq ev_req]; lia).
    rewrite S3, zsum_nil in P. lia. }
  assert (HC : hlive_from [] [HMal CP; HMal CP; HMal CP] = [CP; CP; CP]) by reflexivity.
  assert (NC : nnl [CP; CP; CP]) by (repeat constructor; lia).
  assert (ZC : zsum [CP; CP; CP] = 3 * CP) by (rewrite !zsum_cons, zsum_nil; lia).
  assert (Hpa : forall o, zsum (pacc sm x (okof o)) <= RDB n) by (intros o; subst n; apply pacc_bytes).
  assert (Hpn : forall o, nnl (pacc sm x (okof o))) by (intros o; apply nn_pacc).
  assert (Hpp : forall o s, pkB s (parse_evs sm x (okof o)) <= zsum s + RDB n + RDQ n)
    by (intros o s; subst n; apply pk_parse).
  assert (SF : sumreq [HFr CP; HFr CP; HFr CP] = 0) by reflexivity.
  assert (ST : forall o, sumreq (p1_tfree sm x o) = 0)
    by (intros o; unfold p1_tfree; destruct (fst (jr_run sm x (okof o))); reflexivity).
  destruct (ranout sm x o1) eqn:E1; cbv iota.
  { rewrite pkB_app, HC, pkB_app.
    pose proof (Hpp o1 [CP; CP; CP]) as P1.
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [_ Q1].
    rewrite (ranout_pacc sm x o1 E1), app_nil_l in Q1. rewrite Q1.
    pose proof (pkB_le [HFr CP; HFr CP; HFr CP] _ NC ltac:(evnn)) as P2. rewrite SF in P2.
    clear - H3 P1 P2 ZC RBn RQn HCP EA ECP. to_l A. maxsplit; lia. }
  destruct (ranout sm x o2) eqn:E2; cbv iota.
  { rewrite pkB_app, HC, pkB_app, pkB_app, hlive_from_app.
    pose proof (Hpp o1 [CP; CP; CP]) as P1.
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [_ Q1]. rewrite Q1.
    pose proof (Hpp o2 (pacc sm x (okof o1) ++ [CP; CP; CP])) as P2.
    destruct (parse_ok sm x (okof o2) (pacc sm x (okof o1) ++ [CP; CP; CP])) as [_ Q2].
    rewrite (ranout_pacc sm x o2 E2), app_nil_l in Q2. rewrite Q2.
    assert (N1 : nnl (pacc sm x (okof o1) ++ [CP; CP; CP])) by (apply nn_app; [apply Hpn | exact NC]).
    pose proof (pkB_le (p1_tfree sm x o1 ++ [HFr CP; HFr CP; HFr CP]) _ N1
                  (evs_nn_app (p1_tfree sm x o1) [HFr CP; HFr CP; HFr CP] (evs_nn_tfree sm x o1)
                     ltac:(evnn))) as P3.
    rewrite sumreq_app, ST, SF in P3. rewrite zsum_app in P2, P3. pose proof (Hpa o1) as Ha1.
    clear - H3 P1 P2 P3 Ha1 ZC RBn RQn HCP EA ECP. to_l A. maxsplit; lia. }
  rewrite pkB_app, HC, pkB_app.
  destruct (p1_ok sm x o1 o2 o0 [CP; CP; CP]) as [_ Q].
  assert (G1 : pkB [CP; CP; CP] (parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0))
               <= 3 * CP + 3 * RDB n + RDQ n).
  { rewrite pkB_app, pkB_app.
    pose proof (Hpp o1 [CP; CP; CP]) as P1.
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [_ Q1]. rewrite Q1.
    pose proof (Hpp o2 (pacc sm x (okof o1) ++ [CP; CP; CP])) as P2.
    destruct (parse_ok sm x (okof o2) (pacc sm x (okof o1) ++ [CP; CP; CP])) as [_ Q2]. rewrite Q2.
    pose proof (Hpp o0 (pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ [CP; CP; CP])) as P3.
    rewrite !zsum_app in P2. rewrite !zsum_app in P3. pose proof (Hpa o1) as Ha1. pose proof (Hpa o2) as Ha2.
    clear - P1 P2 P3 Ha1 Ha2 ZC RBn RQn. maxsplit; lia. }
  rewrite Q, (pkB_app (p1_tfree sm x o1 ++ p1_tfree sm x o2 ++ p1_tfree sm x o0 ++ [HFr CP; HFr CP; HFr CP])).
  assert (N0 : nnl (pacc sm x (okof o0) ++ pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ [CP; CP; CP])).
  { apply nn_app; [apply Hpn|]. apply nn_app; [apply Hpn|]. apply nn_app; [apply Hpn | exact NC]. }
  assert (EvG : evs_nn (p1_tfree sm x o1 ++ p1_tfree sm x o2 ++ p1_tfree sm x o0 ++ [HFr CP; HFr CP; HFr CP])).
  { apply evs_nn_app; [apply evs_nn_tfree|]. apply evs_nn_app; [apply evs_nn_tfree|].
    apply evs_nn_app; [apply evs_nn_tfree | evnn]. }
  pose proof (pkB_le _ _ N0 EvG) as G2.
  rewrite !sumreq_app, !ST, SF in G2. rewrite !zsum_app in G2.
  pose proof (Hpa o0) as Ha0. pose proof (Hpa o1) as Ha1. pose proof (Hpa o2) as Ha2.
  destruct (tfrees_ok sm x o1 o2 o0 CP) as [_ T2]. rewrite T2.
  assert (G3 : pkB [] (if ranout sm x o0 then [] else call_rest sm x) <= B).
  { destruct (ranout sm x o0); [cbn [pkB]; rewrite zsum_nil; subst B; unfold RDB in *; lia|].
    subst B n. exact (pk_rest sm x). }
  clear - H3 G1 G2 G3 Ha0 Ha1 Ha2 ZC RBn RQn HCP EA ECP.
  maxsplit; [to_l A; lia | to_l A; lia | to_l A; lia | to_r B; exact G3].
Qed.

(* ================================================================ M6: one call's byte peak at the input's size *)

(* The per-call peak (live bytes plus the next request) at |x| = n. 2560 n is the rewrite's pj_set grow: the doc
   tree (256 n), the copy (768 n) and its arrays' grow (2 x 768 n), every read-back tree bounded by reading the
   compact text, |wdoc t false| <= 3 n. CALL_PEAK MAXB = 8,053,194,752; the tight figure of the internal file LIVE-BYTES-PEAK.md
   section 5 (M6) is 6,694,176,884. *)
Definition CALL_PEAK (n : Z) : Z := 2560 * n + 131072.

Section Peak.
Variable sm : list Z -> Z * Z.
Variable x : list Z.
Variable t : jv.
Hypothesis Hr : json_read sm x = Some t.

Local Notation n := (Z.of_nat (length x)).

Lemma Lf_read : Lf t <= 3 * n.
Proof. exact (SlotSizesPort.wlen_false_read sm x t Hr). Qed.

Lemma Lt_read : Z.of_nat (length (wdoc t true)) <= 56 * n - 54.
Proof. exact (SlotSizesPort.wlen_true_read sm x t Hr). Qed.

Lemma brt1_false_le : BRT1 t false <= 2304 * n + 81920.
Proof. pose proof Lf_read as L. unfold BRT1, WCAP, RCAP, Lf, RDB, RDQ, HEAD in *. lia. Qed.

Lemma brt1_true_le : RDB (Lf t) + BRT1 t true <= 2304 * n + 81920.
Proof. pose proof Lf_read as L. pose proof Lt_read as T. unfold BRT1, WCAP, RCAP, Lf, RDB, RDQ, HEAD in *. lia. Qed.

Lemma rb2_le : 2 * RDB (Lf t) <= 2304 * n + 81920.
Proof. pose proof Lf_read as L. unfold RDB. lia. Qed.

Lemma rb1_le : RDB (Lf t) <= 2304 * n + 81920.
Proof. pose proof Lf_read as L. unfold RDB. lia. Qed.

Lemma wmax_le : 2 * (Z.max (WCAP t true) (WCAP t false) + HEAD) <= 2304 * n + 81920.
Proof. pose proof Lf_read as L. pose proof Lt_read as T. unfold WCAP, Lf, HEAD in *. lia. Qed.

End Peak.

Lemma brw_le : forall sm x ms, json_read sm x = Some (JObj ms) ->
  BRW ms <= 2304 * Z.of_nat (length x) + 81920 /\ RDB (Lf (copy_set ms)) <= 2304 * Z.of_nat (length x) + 81920.
Proof.
  intros sm x ms H. pose proof (Lf_read sm x _ H) as L. pose proof (Lt_read sm x _ H) as T.
  pose proof (copy_len_false ms) as Cf. pose proof (copy_len_true ms) as Ct.
  unfold BRW, WCAP, Lf, RDB, RDQ, HEAD in *. split; lia.
Qed.

Lemma tlb_le : forall sm x, TLB sm x <= 2304 * Z.of_nat (length x) + 81920.
Proof.
  intros sm x. unfold TLB. destruct (fst (jr_run sm x [])) as [t|] eqn:Ej; [|lia].
  assert (H : json_read sm x = Some t) by (unfold json_read; exact Ej).
  pose proof (brt1_false_le sm x t H). pose proof (brt1_true_le sm x t H).
  pose proof (rb2_le sm x t H). pose proof (rb1_le sm x t H). pose proof (wmax_le sm x t H).
  assert (M : match t with JObj ms => Z.max (BRW ms) (RDB (Lf (copy_set ms))) | _ => RDB (Lf t) end <=
              2304 * Z.of_nat (length x) + 81920).
  { destruct t as [| | | txt bits | z | items | ms]; try assumption.
    destruct (brw_le sm x ms H). lia. }
  unfold BRTT. lia.
Qed.

Lemma pk_call : forall sm x o1 o2 o0, pkB [] (call_evs sm x o1 o2 o0) <= CALL_PEAK (Z.of_nat (length x)).
Proof.
  intros sm x o1 o2 o0. pose proof (pk_call0 sm x o1 o2 o0) as H. pose proof (tlb_le sm x) as T.
  unfold CALL_PEAK, RDB, RDQ, FUZZ_PAD in *. lia.
Qed.

(* M6: at every position j of one call, the live bytes plus the request of the j-th event *)
Theorem call_bytes : forall sm x o1 o2 o0 j e, Z.of_nat (length x) <= MAXB ->
  nth_error (PresetRun.call_evs sm x o1 o2 o0) j = Some e ->
  zsum (hlive (firstn j (PresetRun.call_evs sm x o1 o2 o0))) + ev_req e <= CALL_PEAK (Z.of_nat (length x)).
Proof.
  intros sm x o1 o2 o0 j e _ He. unfold hlive.
  pose proof (pkB_nth _ [] j e He). pose proof (pk_call sm x o1 o2 o0). lia.
Qed.

(* ================================================================ M7: a position of the k calls is one of a call *)

Theorem hruns_pos : forall sm x os i e, nth_error (PresetRun.hruns sm x os) i = Some e ->
  exists o1 o2 o0 j, nth_error (PresetRun.call_evs sm x o1 o2 o0) j = Some e /\
    Permutation (hlive (firstn i (PresetRun.hruns sm x os))) (hlive (firstn j (PresetRun.call_evs sm x o1 o2 o0))).
Proof.
  intros sm x os. induction os as [|[[o1 o2] o0] os IH]; intros i e H.
  - cbn [hruns map concat] in H. destruct i; discriminate.
  - rewrite hruns_cons in *.
    destruct (Nat.lt_ge_cases i (length (call_evs sm x o1 o2 o0))) as [Hl | Hg].
    + exists o1, o2, o0, i. rewrite nth_error_app1 in H by exact Hl. split; [exact H|].
      rewrite firstn_app. replace (i - length (call_evs sm x o1 o2 o0))%nat with 0%nat by lia.
      rewrite firstn_O, app_nil_r. apply Permutation_refl.
    + rewrite nth_error_app2 in H by exact Hg. destruct (IH _ _ H) as (p1 & p2 & p0 & j & Hj & Hp).
      exists p1, p2, p0, j. split; [exact Hj|].
      rewrite firstn_app, (firstn_all2 _ Hg). unfold hlive. rewrite hlive_from_app.
      destruct (call_ok sm x o1 o2 o0) as [_ E]. unfold hlive in E. rewrite E. exact Hp.
Qed.

(* ================================================================ the allocator side *)

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames YG01cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetRoomPos.

(* YD23.v:51 (A/AD23.v:48) in the zsum form: the live request bytes are the sum of the live requests *)
Lemma blocks_bytes_zsum : forall S, blocks_bytes S = zsum (map snd (blocks S)).
Proof.
  intros S. unfold blocks_bytes, blocks. rewrite map_map. cbn [snd].
  induction (st_chunks S) as [|k l IH]; [reflexivity|].
  cbn [fold_right filter]. destruct (is_alloc k); cbn [map]; rewrite ?zsum_cons, IH; reflexivity.
Qed.

(* M1: at position i of the run, the allocator's live bytes are the model's live bytes plus at most 3 driver
   blocks, each a live request of S *)
Theorem blocks_bytes_room_pos : forall sm x os i H0 hist S,
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  exists d, (length d <= 3)%nat /\ incl d (map snd (blocks S)) /\
    blocks_bytes S = zsum (PresetReqAt.hlive (firstn i (PresetRun.hruns sm x os))) + zsum d.
Proof.
  intros sm x os i H0 hist S [[d [Hd Hp]] _]. exists d.
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in Hp.
  split; [exact Hd|]. split.
  - intros z Hz. apply (Permutation_in z (Permutation_sym Hp)). apply in_or_app. right. exact Hz.
  - rewrite blocks_bytes_zsum, (zsum_perm _ _ Hp), zsum_app. reflexivity.
Qed.

(* M2: every live request of a Wf_cf state is below cf_malloc_max (chunk_ok_cf, YG01cf.v:107-108) *)
Theorem blocks_req_lt_cf : forall (cp : CfParams) U S z, @Wf_cf cp U S -> In z (map snd (blocks S)) ->
  0 <= z < cf_malloc_max.
Proof.
  intros cp U S z HW Hz. pose proof (wfc_chunks U 0 0 0 S HW) as HF.
  unfold blocks in Hz. rewrite map_map in Hz. apply in_map_iff in Hz as (k & Ek & Hk).
  apply filter_In in Hk as [Hk _]. rewrite Forall_forall in HF. destruct (HF k Hk) as [Hr _].
  cbn [snd] in Ek. subst z. exact Hr.
Qed.

(* the driver's blocks at preset's instance: 3 * (cf_malloc_max - 1) <= DRV_BYTES = 3 * (2 ^ 29 - 2 ^ 20 - 1), the
   value at the cf_malloc_max of 298d096d6893 (the internal file LIVE-BYTES-PEAK.md section 2, DRVc). int102 lowered cf_malloc_max to
   2 ^ 28 + 2 ^ 27 (CfParamsPreset.v:94, b60d0f63c926), so drv_bytes uses only cf_malloc_max <= 2 ^ 29 - 2 ^ 20 and
   holds at either value (h-pre-b2, PEAK-BYTES-102: the proof's `= 535822336 by reflexivity` failed on int102). *)
Definition DRV_BYTES : Z := 1607467005.

Lemma zsum_le_len : forall d M, (forall z, In z d -> z <= M) -> zsum d <= Z.of_nat (length d) * M.
Proof.
  induction d as [|a d IH]; intros M H; [rewrite zsum_nil; cbn [length]; lia|].
  rewrite zsum_cons. pose proof (H a (or_introl eq_refl)) as Ha.
  pose proof (IH M (fun z Hz => H z (or_intror Hz))) as Hd. cbn [length]. lia.
Qed.

Lemma drv_bytes : forall U S d, @Wf_cf CfParamsPreset.CfParams_preset U S ->
  (length d <= 3)%nat -> incl d (map snd (blocks S)) -> zsum d <= DRV_BYTES.
Proof.
  intros U S d HW Hl Hi.
  assert (Hc : @cf_malloc_max CfParamsPreset.CfParams_preset <= 535822336) by (apply Z.leb_le; reflexivity).
  assert (HM : forall z, In z d -> z <= 535822335).
  { intros z Hz. pose proof (blocks_req_lt_cf _ U S z HW (Hi z Hz)) as B. lia. }
  assert (HN : forall z, In z d -> 0 <= z).
  { intros z Hz. pose proof (blocks_req_lt_cf _ U S z HW (Hi z Hz)) as B. lia. }
  pose proof (zsum_le_len d 535822335 HM) as H. unfold DRV_BYTES. nia.
Qed.

(* ================================================================ U4 *)

(* LIVE_PEAK_PRESET: the measured uniform peak (the internal file LIVE-BYTES-PEAK.md section 3 "Results" and section 5 M6 / section 6
   step 4: CALL_PEAK (MAXB) + DRVc = 6,694,176,884 + 1,607,467,005 = 8,301,643,889) rounded up with margin to
   10 ^ 10. What is proved here: CALL_PEAK MAXB + DRV_BYTES = 8,053,194,752 + 1,607,467,005 = 9,660,661,757
   <= 10 ^ 10 <= 2 ^ 34 = YG01.LIVE_MAX. *)
Definition LIVE_PEAK_PRESET : Z := 10000000000.

Theorem blocks_bytes_bound_preset_peak :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) (e : PresetReqAt.hev),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  Z.of_nat (length x) <= PresetReqAt.MAXB ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i = Some e ->
  blocks_bytes S + ev_req e <= LIVE_PEAK_PRESET.
Proof.
  intros U sm x os i H0 hist S e HW HX HP He.
  destruct (blocks_bytes_room_pos sm x os i H0 hist S HP) as (d & Hd & Hi & Eb).
  pose proof (drv_bytes U S d HW Hd Hi) as HD.
  destruct (hruns_pos sm x os i e He) as (o1 & o2 & o0 & j & Hj & Hp).
  pose proof (call_bytes sm x o1 o2 o0 j e HX Hj) as HC.
  rewrite (zsum_perm _ _ Hp) in Eb.
  unfold CALL_PEAK, DRV_BYTES, LIVE_PEAK_PRESET, MAXB in *. lia.
Qed.

(* U4, the shape a Theorem Labs lane binds (the internal file LIVE-BYTES-PEAK.md section 6): at a keep site with He : nth_error .. i =
   Some (HMal r) or Some (HRe m r), the premise blocks_bytes S + r <= LIVE_MAX is this lemma at He. *)
Theorem blocks_bytes_bound_preset :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) (e : PresetReqAt.hev),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  Z.of_nat (length x) <= PresetReqAt.MAXB ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i = Some e ->
  blocks_bytes S + ev_req e <= LIVE_MAX.
Proof.
  intros U sm x os i H0 hist S e HW HX HP He.
  pose proof (blocks_bytes_bound_preset_peak U sm x os i H0 hist S e HW HX HP He) as H.
  assert (E : LIVE_MAX = 17179869184) by reflexivity. rewrite E. unfold LIVE_PEAK_PRESET in H. lia.
Qed.

(* ================================================================ ENTRY SUMS (row ENTRY-SUMS, h-pre-b2)
   The texts (d6318e886fd9) take `blocks_bytes S + LIVE_<fn> args <= LIVE_MAX` at their ENTRY: the subtree's summed
   live room on top of what is live, not one request. This section turns the byte peak above into that form:
   - ev_req_nn: every event of the run asks a nonnegative request (PROVED from the model: chain_nn for the writer's
     and rendered ()'s buffers, set_evs_nn, rd_hevs_nn, and the literal events of call_evs), so the peak
     `blocks_bytes S + ev_req e <= LIVE_PEAK_PRESET` bounds blocks_bytes S alone;
   - entry_sum_ok (the owner's shape): at a position with an event, any n with 0 <= n <= ENTRY_ROOM fits;
   - blocks_bytes_peak_pos / entry_sum_pos: the same at ANY position, event or none (past the run's last event every
     call is closed, so only the driver's blocks are live, DRV_BYTES <= LIVE_PEAK_PRESET);
   - blocks_bytes_closed / entry_sum_closed (the owner's addition (a)): at a CALL BOUNDARY (the harness entry) only
     the driver's blocks are live, so any n with 0 <= n <= CLOSED_ROOM fits.
   The per-text arithmetic (each LIVE_<fn> at the argument its consumer passes, within ENTRY_ROOM or CLOSED_ROOM) is
   lib/A/PresetEntrySums.v and lib/A/PresetEntryLib.v (they Require the texts, which this leaf may not). *)

(* ---------------------------------------------------------------- every request of the run is nonnegative *)

Lemma pos_nn_forall : forall l, Forall (fun z => 0 < z) l -> Forall (fun z => 0 <= z) l.
Proof. intros l H. eapply Forall_impl; [|exact H]. cbv beta. intros z Hz. lia. Qed.

(* a buffer grown through nonnegative capacities, with a nonnegative head, asks for nonnegative sizes *)
Lemma chain_nn : forall hd old cs, 0 <= hd -> Forall (fun c => 0 <= c) cs -> evs_nn (PresetReqAt.chain hd old cs).
Proof.
  intros hd old cs Hhd Hcs. revert old.
  induction Hcs as [|c cs Hc Hcs IH]; intros old; cbn [chain]; [constructor|].
  constructor; [|apply IH]. destruct (old =? 0); cbn [ev_req]; lia.
Qed.

Lemma w_evs_nn : forall t p, evs_nn (w_evs t p).
Proof. intros t p. unfold w_evs. apply chain_nn; [unfold HEAD; lia | apply pos_nn_forall, wcaps_pos]. Qed.

Lemma r_evs_nn : forall t p, evs_nn (r_evs t p).
Proof. intros t p. unfold r_evs. apply chain_nn; [lia | apply pos_nn_forall, rcaps_pos]. Qed.

Lemma w_starved_nn : forall t p k, evs_nn (w_starved t p k).
Proof.
  intros t p k. unfold w_starved. apply evs_nn_app.
  - apply chain_nn; [unfold HEAD; lia|]. apply pos_nn_forall. exact (firstn_forall _ _ _ k (wcaps_pos t p)).
  - destruct k as [|k]; cbv beta iota; [constructor | evnn].
Qed.

Lemma starved_write_nn : forall x t p rest, evs_nn rest -> evs_nn (starved_write x t p rest).
Proof.
  intros x t p rest Hr. unfold starved_write. apply evs_nn_app; [apply w_evs_nn|]. apply evs_nn_app; [evnn|].
  destruct (wcalls t p); cbv beta iota; [constructor | apply evs_nn_app; [apply w_starved_nn | exact Hr]].
Qed.

Lemma starved_writes_nn : forall x t, evs_nn (starved_writes x t).
Proof. intros x t. unfold starved_writes. apply starved_write_nn, starved_write_nn. constructor. Qed.

Lemma parse_evs_nn : forall sm y ok, evs_nn (parse_evs sm y ok).
Proof.
  intros sm y ok. unfold parse_evs. apply evs_nn_app; [apply rd_hevs_nn|].
  destruct (fst (jr_run sm y ok)); evnn.
Qed.

Lemma starved_parse_nn : forall sm x k, evs_nn (starved_parse sm x k).
Proof. intros sm x [|k]; unfold starved_parse; [constructor | apply parse_evs_nn]. Qed.

Lemma rt_text_nn : forall sm t p, evs_nn (rt_text sm t p).
Proof.
  intros sm t p. unfold rt_text. apply evs_nn_app; [apply w_evs_nn|]. apply evs_nn_app; [apply r_evs_nn|].
  apply evs_nn_app; [apply parse_evs_nn|]. apply evs_nn_app; evnn.
Qed.

Lemma rw_evs_nn : forall sm ms, evs_nn (rw_evs sm ms).
Proof.
  intros sm ms. unfold rw_evs. apply evs_nn_app; [apply set_evs_nn|]. apply evs_nn_app; [apply w_evs_nn|].
  apply evs_nn_app; [apply parse_evs_nn|]. apply evs_nn_app; evnn.
Qed.

Lemma round_trip_nn : forall sm t, evs_nn (round_trip sm t).
Proof.
  intros sm t. unfold round_trip. apply evs_nn_app; [apply rt_text_nn|]. apply evs_nn_app; [apply rt_text_nn|].
  apply evs_nn_app; [evnn|].
  destruct t as [| | | txt bits | s | items | ms]; cbv beta iota; try evnn.
  apply evs_nn_app; [apply rw_evs_nn | evnn].
Qed.

Lemma call_tail_nn : forall sm x, evs_nn (call_tail sm x).
Proof.
  intros sm x. unfold call_tail. destruct (fst (jr_run sm x [])) as [t|]; cbv beta iota; [|apply starved_parse_nn].
  apply evs_nn_app; [apply round_trip_nn|]. apply evs_nn_app; [apply starved_parse_nn|].
  apply evs_nn_app; [apply starved_writes_nn | evnn].
Qed.

Lemma call_rest_nn : forall sm x, evs_nn (call_rest sm x).
Proof.
  intros sm x. unfold call_rest. cbv zeta. apply evs_nn_app; [apply parse_evs_nn|].
  apply evs_nn_app; [evnn | apply call_tail_nn].
Qed.

Lemma call_evs_nn : forall sm x o1 o2 o0, evs_nn (call_evs sm x o1 o2 o0).
Proof.
  intros sm x o1 o2 o0.
  assert (Hc : 0 <= Z.of_nat (length x) + FUZZ_PAD) by (unfold FUZZ_PAD; lia).
  assert (C3 : forall c, 0 <= c -> evs_nn [HMal c; HMal c; HMal c]) by (intros c H; evnn).
  assert (F3 : forall c, evs_nn [HFr c; HFr c; HFr c]) by (intros c; evnn).
  rewrite call_evs_blocks. destruct (MAXB <? Z.of_nat (length x)); cbv iota; [constructor|].
  destruct (ranout sm x o1); cbv iota.
  { apply evs_nn_app; [exact (C3 _ Hc)|]. apply evs_nn_app; [apply parse_evs_nn | apply F3]. }
  destruct (ranout sm x o2); cbv iota.
  { apply evs_nn_app; [exact (C3 _ Hc)|].
    apply evs_nn_app; [apply evs_nn_app; apply parse_evs_nn|].
    apply evs_nn_app; [apply evs_nn_tfree | apply F3]. }
  apply evs_nn_app; [exact (C3 _ Hc)|].
  apply evs_nn_app; [apply evs_nn_app; [apply parse_evs_nn|]; apply evs_nn_app; apply parse_evs_nn|].
  apply evs_nn_app.
  - apply evs_nn_app; [apply evs_nn_tfree|]. apply evs_nn_app; [apply evs_nn_tfree|].
    apply evs_nn_app; [apply evs_nn_tfree | apply F3].
  - destruct (ranout sm x o0); cbv iota; [constructor | apply call_rest_nn].
Qed.

(* EVERY REQUEST OF THE RUN IS NONNEGATIVE: the step from blocks_bytes S + ev_req e <= LIVE_PEAK_PRESET (the peak at
   the event e of position i) to blocks_bytes S <= LIVE_PEAK_PRESET. Proved from the model, never a premise. *)
Theorem ev_req_nn : forall sm x os i e, nth_error (PresetRun.hruns sm x os) i = Some e -> 0 <= ev_req e.
Proof.
  intros sm x os i e He. destruct (hruns_pos sm x os i e He) as (o1 & o2 & o0 & j & Hj & _).
  pose proof (call_evs_nn sm x o1 o2 o0) as N. unfold evs_nn in N. rewrite Forall_forall in N.
  exact (N e (nth_error_In _ _ Hj)).
Qed.

(* a position with an event is on an input of at most MAXB bytes (call_evs is [] above it, PresetRun.v:372) *)
Lemma hruns_maxb : forall sm x os i e, nth_error (PresetRun.hruns sm x os) i = Some e ->
  Z.of_nat (length x) <= MAXB.
Proof.
  intros sm x os i e He. destruct (hruns_pos sm x os i e He) as (o1 & o2 & o0 & j & Hj & _).
  rewrite call_evs_blocks in Hj. destruct (MAXB <? Z.of_nat (length x)) eqn:E; cbv iota in Hj.
  - destruct j; discriminate.
  - apply Z.ltb_ge in E. exact E.
Qed.

(* the calls of the run give back all they took (PresetRun.call_ok, call_closed :702) *)
Lemma hruns_hlive_nil : forall sm x os, hlive (PresetRun.hruns sm x os) = [].
Proof.
  intros sm x os. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
  rewrite hruns_cons. unfold hlive in *. rewrite hlive_from_app.
  destruct (call_ok sm x o1 o2 o0) as [_ E]. unfold hlive in E. rewrite E. exact IH.
Qed.

(* ---------------------------------------------------------------- the two rooms *)

(* what an entry-keyed text may still take above blocks_bytes S at any position of the run *)
Definition ENTRY_ROOM : Z := LIVE_MAX - LIVE_PEAK_PRESET.

(* what a text may take above blocks_bytes S at a CALL BOUNDARY (the harness entry): only the driver's blocks *)
Definition CLOSED_ROOM : Z := LIVE_MAX - DRV_BYTES.

(* THE OWNER'S SHAPE: at a position with an event, the live bytes plus any n within ENTRY_ROOM fit in LIVE_MAX *)
Theorem entry_sum_ok :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) (e : PresetReqAt.hev) (n : Z),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i = Some e ->
  0 <= n <= ENTRY_ROOM ->
  blocks_bytes S + n <= LIVE_MAX.
Proof.
  intros U sm x os i H0 hist S e n HW HP He Hn.
  pose proof (blocks_bytes_bound_preset_peak U sm x os i H0 hist S e HW (hruns_maxb sm x os i e He) HP He).
  pose proof (ev_req_nn sm x os i e He). unfold ENTRY_ROOM in Hn. lia.
Qed.

(* THE SAME AT ANY POSITION, event or none: before the run's end the position has an event (the peak and ev_req_nn);
   at or past it every call is closed, so only the driver's blocks are live (drv_bytes). No input bound: an input
   above MAXB has no event at all. *)
Theorem blocks_bytes_peak_pos :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  blocks_bytes S <= LIVE_PEAK_PRESET.
Proof.
  intros U sm x os i H0 hist S HW HP.
  destruct (Nat.lt_ge_cases i (length (PresetRun.hruns sm x os))) as [Hl | Hg].
  - destruct (nth_error (PresetRun.hruns sm x os) i) as [e|] eqn:He.
    + pose proof (blocks_bytes_bound_preset_peak U sm x os i H0 hist S e HW (hruns_maxb sm x os i e He) HP He).
      pose proof (ev_req_nn sm x os i e He). lia.
    + apply nth_error_None in He. lia.
  - destruct (blocks_bytes_room_pos sm x os i H0 hist S HP) as (d & Hd & Hi & Eb).
    rewrite (firstn_all2 _ Hg), hruns_hlive_nil, zsum_nil in Eb.
    pose proof (drv_bytes U S d HW Hd Hi). unfold DRV_BYTES, LIVE_PEAK_PRESET in *. lia.
Qed.

Theorem entry_sum_pos :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) (n : Z),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  0 <= n <= ENTRY_ROOM ->
  blocks_bytes S + n <= LIVE_MAX.
Proof.
  intros U sm x os i H0 hist S n HW HP Hn.
  pose proof (blocks_bytes_peak_pos U sm x os i H0 hist S HW HP). unfold ENTRY_ROOM in Hn. lia.
Qed.

(* AT A CALL BOUNDARY (the events before i are whole calls): every earlier call is closed (call_closed,
   PresetRun.v:702), so blocks_bytes S is the driver's at most three blocks (blocks_bytes_room_pos, drv_bytes) *)
Theorem blocks_bytes_closed :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os os0 : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  firstn i (PresetRun.hruns sm x os) = PresetRun.hruns sm x os0 ->
  blocks_bytes S <= DRV_BYTES.
Proof.
  intros U sm x os os0 i H0 hist S HW HP Hf.
  destruct (blocks_bytes_room_pos sm x os i H0 hist S HP) as (d & Hd & Hi & Eb).
  rewrite Hf, hruns_hlive_nil, zsum_nil in Eb. pose proof (drv_bytes U S d HW Hd Hi). lia.
Qed.

(* WHERE THE CLOSED ROOM ALSO APPLIES INSIDE A CALL: a refused call whose reading allocates nothing has an empty tail
   (call_tail, PresetRun.v:352-357: starved_parse at took = calls = 0), so check_reject_clean_starved's call there
   (took = 0, doc = 0, the no-event site) is the call's END, a call boundary: blocks_bytes_closed holds at it with
   os0 := the calls so far and this one *)
Lemma call_tail_refused_noalloc : forall sm x, fst (jr_run sm x []) = None -> calls (rtr sm [] x) = 0%nat ->
  call_tail sm x = [].
Proof. intros sm x Hn Hc. unfold call_tail. rewrite Hn, Hc. reflexivity. Qed.

(* THE HARNESS ENTRY (the owner's addition (a)). The premises are, conjunct for conjunct, those of the walk's entry
   premise ec_pre (lib/A/Ent102CutsA.v at d6318e886fd9 :388 `PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E)
   (e_i0 E) (e_H0 E) (e_hist0 E) (e_S E)` and :390 `e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E))`),
   and the conclusion at n := LIVE_LIB is its conjunct :397 `blocks_bytes (e_S E) + LIVE_LIB <= LIVE_MAX`, the top
   cut's budget (first used at lib/A/Prog/Ent102L0A.v:677, with ec_lcut E 0 <= LIVE_LIB from ec_lcut_ok :561).
   LIVE_LIB within CLOSED_ROOM: lib/A/PresetEntryLib.v live_lib_fits. *)
Theorem entry_sum_closed :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) (n : Z),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  i = length (PresetRun.hruns sm x os) ->
  0 <= n <= CLOSED_ROOM ->
  blocks_bytes S + n <= LIVE_MAX.
Proof.
  intros U sm x os i H0 hist S n HW HP Hi Hn. subst i.
  pose proof (blocks_bytes_closed U sm x os os _ H0 hist S HW HP (firstn_all _)). unfold CLOSED_ROOM in Hn. lia.
Qed.
