From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require check_round_trip_c.
Import ListNotations.
Local Open Scope Z_scope.

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

Theorem wlen_false_read : forall sm x t, json_read sm x = Some t -> wlen t false <= 3 * Z.of_nat (length x).
Proof.
  intros sm x t H.
  assert (E : wlen t false = Wv false 0 t).
  { unfold wlen, wdoc, wdpieces, Wv. cbv beta iota. rewrite app_nil_r. reflexivity. }
  rewrite E.
  enough (W : Wv false 0 t <= 3 * Z.of_nat (length x) + (fun _ => 0) 0%nat) by (cbv beta in W; lia).
  apply (w_read sm false 3 (fun _ => 0)); first [exact H | (intros; try unfold indl; cbv beta iota; lia)].
Qed.

Theorem wlen_true_read : forall sm x t, json_read sm x = Some t -> wlen t true <= 56 * Z.of_nat (length x) - 54.
Proof.
  intros sm x t H.
  assert (E : wlen t true = Wv true 0 t + 1).
  { unfold wlen, wdoc, wdpieces, Wv. change (Z.of_nat 0) with 0. cbv beta iota.
    rewrite concat_app, length_app. cbn [concat app length]. lia. }
  rewrite E.
  enough (W : Wv true 0 t <= 56 * Z.of_nat (length x) + G 0) by (change (G 0) with (-55) in W; lia).
  apply (w_read sm true 56 G); first [exact H | lia | exact G_lo |
    (intros c Hc; destruct (G_step c Hc) as [K1 K2]; unfold indl; cbv beta iota; lia) |
    (intros d; pose proof (G_lo d); lia)].
Qed.

Inductive szok (N : nat) : jv -> Prop :=
| sz_null : szok N JNull
| sz_false : szok N JFalse
| sz_true : szok N JTrue
| sz_num : forall txt bits, (length txt <= N)%nat -> szok N (JNum txt bits)
| sz_str : forall s, (length (flat_map ech s) <= 3 * N)%nat -> szok N (JStr s)
| sz_arr : forall items, (2 * length items <= N + 1)%nat -> Forall (szok N) items -> szok N (JArr items)
| sz_obj : forall ms, (2 * length ms + 2 <= N)%nat ->
    Forall (fun m => (length (flat_map ech (fst m)) <= 3 * N)%nat) ms -> Forall (szok N) (map snd ms) ->
    szok N (JObj ms).

Lemma szok_num_inv : forall N txt bits, szok N (JNum txt bits) -> (length txt <= N)%nat.
Proof. intros N txt bits H. inversion H. assumption. Qed.

Lemma szok_str_inv : forall N s, szok N (JStr s) -> (length (flat_map ech s) <= 3 * N)%nat.
Proof. intros N s H. inversion H. assumption. Qed.

Lemma szok_arr_inv : forall N items, szok N (JArr items) ->
  (2 * length items <= N + 1)%nat /\ Forall (szok N) items.
Proof. intros N items H. inversion H. split; assumption. Qed.

Lemma szok_obj_inv : forall N ms, szok N (JObj ms) -> (2 * length ms + 2 <= N)%nat /\
  Forall (fun m => (length (flat_map ech (fst m)) <= 3 * N)%nat) ms /\ Forall (szok N) (map snd ms).
Proof. intros N ms H. inversion H. split; [|split]; assumption. Qed.

Lemma szok_mono : forall t N N', szok N t -> (N <= N')%nat -> szok N' t.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros N N' H Hle.
  - constructor.
  - constructor.
  - constructor.
  - apply szok_num_inv in H. constructor. lia.
  - apply szok_str_inv in H. constructor. lia.
  - destruct (szok_arr_inv _ _ H) as [Hn Hf]. constructor; [lia|].
    rewrite Forall_forall in *. intros u Hu. exact (IH u Hu N N' (Hf u Hu) Hle).
  - destruct (szok_obj_inv _ _ H) as (Hn & Hk & Hf). constructor; [lia| |].
    + rewrite Forall_forall in *. intros m Hm. specialize (Hk m Hm). cbv beta in *. lia.
    + rewrite Forall_forall in *. intros u Hu. apply in_map_iff in Hu as (m & <- & Hm).
      exact (IH m Hm N N' (Hf (snd m) (in_map snd ms m Hm)) Hle).
Qed.

Definition cw (o : bool) : nat := if o then 5%nat else 2%nat.

Definition mok (o : bool) (N : nat) (m : list Z * jv) : Prop :=
  (o = true -> (length (flat_map ech (fst m)) <= 3 * N)%nat) /\ szok N (snd m).

Section S.
Variable sm : list Z -> Z * Z.

Definition SRL (f : nat) : Prop := forall d o n cap acc y ok v r tr ok',
  jrl sm f d o n cap acc y ok = (Some (v, r), tr, ok') ->
  exists nw, nw <> [] /\ v = mk o (rev acc ++ nw) /\ (cw o * length nw + length r <= length y)%nat /\
    Forall (mok o (length y)) nw.

Lemma cont_s : forall f d o b y ok v r tr ok', SRL f ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (v, r), tr, ok') ->
  (length r < length (b :: y))%nat /\ szok (length (b :: y)) v.
Proof.
  intros f d o b y ok v r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H. cbn [length].
  assert (LOOP : forall z, (length z <= length y)%nat -> jrl sm f (S d) o 0 0 [] z ok = (Some (v, r), tr, ok') ->
    (length r < S (length y))%nat /\ szok (S (length y)) v).
  { intros z Hz HL. destruct (IHl _ _ _ _ _ _ _ _ _ _ _ HL) as (nw & Hne & -> & Hc & Hf). cbn [rev app].
    destruct nw as [|m nw']; [contradiction|]. clear Hne. cbn [length] in Hc.
    unfold mk. destruct o; cbn [cw] in Hc; cbv beta iota; (split; [lia|]).
    - constructor.
      + cbn [length]. lia.
      + rewrite Forall_forall in *. intros m' Hm'. destruct (Hf m' Hm') as [H1 _]. specialize (H1 eq_refl).
        cbv beta. lia.
      + rewrite Forall_forall in *. intros u Hu. apply in_map_iff in Hu as (m' & <- & Hm').
        destruct (Hf m' Hm') as [_ H2]. apply (szok_mono _ _ _ H2). lia.
    - constructor.
      + rewrite length_map. cbn [length]. lia.
      + rewrite Forall_forall in *. intros u Hu. apply in_map_iff in Hu as (m' & <- & Hm').
        destruct (Hf m' Hm') as [_ H2]. apply (szok_mono _ _ _ H2). lia. }
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  { exact (LOOP [] ltac:(cbn [length]; lia) H). }
  destruct (c =? closer o); cbv beta iota in H.
  2: { exact (LOOP (c :: r0) ltac:(rewrite <- Ey; exact (skip_len y)) H). }
  unfold jret in H. injection H as Hv Hr _ _. subst v r.
  pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
  split; [lia|]. unfold mk. destruct o; constructor; cbn [length map]; try lia; constructor.
Qed.

Lemma s_fuel : forall f,
  (forall d x ok v r tr ok', jrv sm f d x ok = (Some (v, r), tr, ok') ->
     (length r < length x)%nat /\ szok (length x) v) /\ SRL f.
Proof.
  induction f as [|f [IHv IHl]].
  - split; [|unfold SRL]; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok v r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (Fin : (length r < length (b :: y))%nat /\ szok (length (b :: y)) v ->
          (length r < length x)%nat /\ szok (length x) v).
      { intros [A1 A2]. pose proof (skip_len x) as Hs'. rewrite Ex in Hs'. split; [lia|].
        exact (szok_mono _ _ _ A2 Hs'). }
      apply Fin. clear Fin.
      destruct (b =? 123); cbv beta iota in H; [exact (cont_s f d true b y ok v r tr ok' IHl H)|].
      destruct (b =? 91); cbv beta iota in H; [exact (cont_s f d false b y ok v r tr ok' IHl H)|].
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
        pose proof (jr_string_spec y ok) as Hs'. rewrite Hj in Hs'. destruct Hs' as (q & _ & Hd & _ & Hl).
        cbv beta iota in H. unfold jret in H. injection H as Hv Hr _ _. subst v r1.
        pose proof (decode_w y s r Hd) as D. cbn [length]. split; [lia|]. constructor. lia. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_true in Hl. cbn [length] in Hl |- *.
        split; [lia | constructor]. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_false in Hl. cbn [length] in Hl |- *.
        split; [lia | constructor]. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_null in Hl. cbn [length] in Hl |- *.
        split; [lia | constructor]. }
      destruct (num_w _ _ _ _ _ _ _ H) as (txt & bits & -> & H1 & Hl). split; [lia|]. constructor. lia.
    + unfold SRL. intros d o n cap acc y ok v r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      destruct (IHv d y1 ok2 v0 r0 tv ok3 Ev) as (Hr0 & Sv).
      pose proof (name_w o y ok1 nm y1 tn ok2 En) as Hn.
      assert (Ny0 : (length y1 <= length y)%nat) by (destruct o; cbv beta iota in Hn; [lia | subst y1; lia]).
      assert (Ny3 : o = true -> (length y1 + 3 <= length y)%nat) by (intros ->; cbv beta iota in Hn; lia).
      assert (Nn : o = true -> (length (flat_map ech nm) <= 3 * length y)%nat)
        by (intros ->; cbv beta iota in Hn; lia).
      assert (Mk : mok o (length y) (nm, v0)) by (unfold mok; split; [exact Nn | exact (szok_mono _ _ _ Sv Ny0)]).
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c r1] eqn:Er; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      destruct (c =? 44); cbv beta iota in H.
      { destruct (IHl d o (S n) cap1 ((nm, v0) :: acc) r1 ok3 v r t4 ok' H) as (nw & Hne & Hv & Hc & Hf).
        exists ((nm, v0) :: nw). split; [discriminate|].
        split; [rewrite Hv; cbn [rev]; rewrite <- app_assoc; reflexivity|].
        split.
        - cbn [length]. destruct o; cbn [cw] in *; [specialize (Ny3 eq_refl)|]; lia.
        - constructor; [exact Mk|]. rewrite Forall_forall in *. intros m Hm. destruct (Hf m Hm) as [A1 A2].
          unfold mok. split.
          + intros Ho. specialize (A1 Ho). lia.
          + apply (szok_mono _ _ _ A2). lia. }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as Hv Hr _ _. subst v r.
      exists [(nm, v0)]. split; [discriminate|]. split; [cbn [rev]; reflexivity|].
      split; [cbn [length]; destruct o; cbn [cw]; [specialize (Ny3 eq_refl)|]; lia|].
      constructor; [exact Mk | constructor].
Qed.

Theorem s_read : forall x t, json_read sm x = Some t -> szok (length x) t.
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. destruct (proj1 (s_fuel _) 0%nat x [] t' r tr ok' E) as [_ Sz]. exact Sz.
Qed.

End S.

Inductive ez : jv -> Prop :=
| ez_null : ez JNull
| ez_false : ez JFalse
| ez_true : ez JTrue
| ez_num : forall txt bits, Z.of_nat (length txt) + 17 <= 2 ^ 27 -> ez (JNum txt bits)
| ez_str : forall s, Z.of_nat (length (flat_map ech s)) + 17 <= 2 ^ 27 -> ez (JStr s)
| ez_arr : forall items, Z.of_nat (length items) <= 2 ^ 21 -> Forall ez items -> ez (JArr items)
| ez_obj : forall ms, Z.of_nat (length ms) <= 2 ^ 21 ->
    Forall (fun m => Z.of_nat (length (flat_map ech (fst m))) + 17 <= 2 ^ 27) ms -> Forall ez (map snd ms) ->
    ez (JObj ms).

Lemma ez_num_inv : forall txt bits, ez (JNum txt bits) -> Z.of_nat (length txt) + 17 <= 2 ^ 27.
Proof. intros txt bits H. inversion H. assumption. Qed.

Lemma ez_str_inv : forall s, ez (JStr s) -> Z.of_nat (length (flat_map ech s)) + 17 <= 2 ^ 27.
Proof. intros s H. inversion H. assumption. Qed.

Lemma ez_arr_inv : forall items, ez (JArr items) -> Z.of_nat (length items) <= 2 ^ 21 /\ Forall ez items.
Proof. intros items H. inversion H. split; assumption. Qed.

Lemma ez_obj_inv : forall ms, ez (JObj ms) -> Z.of_nat (length ms) <= 2 ^ 21 /\
  Forall (fun m => Z.of_nat (length (flat_map ech (fst m))) + 17 <= 2 ^ 27) ms /\ Forall ez (map snd ms).
Proof. intros ms H. inversion H. split; [|split]; assumption. Qed.

Definition evok (e : ev) : Prop := Z.of_nat (esize e) + 16 <= 2 ^ 27.

Definition capok (n cap : nat) : Prop :=
  (cap = 0 /\ n = 0)%nat \/ exists j : nat, Z.of_nat cap = 8 * 2 ^ Z.of_nat j /\ (n <= cap)%nat.

Lemma capok_step : forall n cap, capok n cap -> capok (S n) (gcap n cap).
Proof.
  intros n cap [[-> ->] | (j & Ej & Hn)].
  - right. exists 0%nat. unfold gcap. cbn. split; [reflexivity | lia].
  - assert (P : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
    unfold gcap. destruct (Nat.ltb n cap) eqn:El; cbv beta iota.
    + apply Nat.ltb_lt in El. right. exists j. split; [exact Ej | lia].
    + apply Nat.ltb_ge in El. destruct (Nat.eqb cap 0) eqn:E0; cbv beta iota.
      * apply Nat.eqb_eq in E0. subst cap. cbn in Ej. lia.
      * apply Nat.eqb_neq in E0. right. exists (S j). split; [|lia].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma gcap_le : forall n cap, capok n cap -> (cap <= n)%nat -> Z.of_nat n < 2 ^ 21 ->
  Z.of_nat (gcap n cap) <= 2 ^ 21.
Proof.
  intros n cap [[-> ->] | (j & Ej & Hn)] Hc Hl.
  - unfold gcap. cbn. lia.
  - assert (P : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
    assert (Hj : (j <= 17)%nat).
    { destruct (Nat.le_gt_cases j 17) as [H|H]; [exact H|].
      assert (2 ^ 18 <= 2 ^ Z.of_nat j) by (apply Z.pow_le_mono_r; lia). lia. }
    assert (2 ^ Z.of_nat j <= 2 ^ 17) by (apply Z.pow_le_mono_r; lia).
    unfold gcap. rewrite (proj2 (Nat.ltb_ge n cap) Hc). cbv beta iota.
    destruct (Nat.eqb cap 0); cbv beta iota; lia.
Qed.

Lemma tgo_arr_ev : forall l n cap, capok n cap -> Z.of_nat (n + length l)%nat <= 2 ^ 21 ->
  Forall (fun u => forall e, In e (ttrace u) -> evok e) l ->
  forall e, In e (tgo_arr n cap l) -> evok e.
Proof.
  induction l as [|u r IH]; intros n cap Hc Hl Hf e He; [cbn [tgo_arr In] in He; contradiction|].
  apply Forall_cons_iff in Hf as [Hu Hf]. cbn [tgo_arr] in He. cbn [length] in Hl.
  apply in_app_or in He as [He|He].
  - unfold grow_ev in He. destruct (Nat.ltb n cap) eqn:El; cbv beta iota in He; [contradiction|].
    apply Nat.ltb_ge in El. pose proof (gcap_le n cap Hc El ltac:(lia)) as G1.
    cbn [In] in He. destruct He as [<-|[]]. unfold evok, esize. lia.
  - apply in_app_or in He as [He|He]; [exact (Hu e He)|].
    exact (IH (S n) (gcap n cap) (capok_step n cap Hc) ltac:(lia) Hf e He).
Qed.

Lemma tgo_obj_ev : forall l n cap, capok n cap -> Z.of_nat (n + length l)%nat <= 2 ^ 21 ->
  Forall (fun m => Z.of_nat (length (flat_map ech (fst m))) + 17 <= 2 ^ 27) l ->
  Forall (fun m => forall e, In e (ttrace (snd m)) -> evok e) l ->
  forall e, In e (tgo_obj n cap l) -> evok e.
Proof.
  induction l as [|[k u] r IH]; intros n cap Hc Hl Hk Hf e He; [cbn [tgo_obj In] in He; contradiction|].
  apply Forall_cons_iff in Hf as [Hu Hf]. apply Forall_cons_iff in Hk as [Hk0 Hk]. cbn [fst snd] in Hu, Hk0.
  cbn [tgo_obj] in He. cbn [length] in Hl.
  apply in_app_or in He as [He|He].
  - unfold grow_ev in He. destruct (Nat.ltb n cap) eqn:El; cbv beta iota in He; [contradiction|].
    apply Nat.ltb_ge in El. pose proof (gcap_le n cap Hc El ltac:(lia)) as G1.
    cbn [In] in He. destruct He as [<-|[<-|[]]]; unfold evok, esize; lia.
  - cbn [In] in He. destruct He as [<-|He]; [unfold evok, esize; lia|].
    apply in_app_or in He as [He|He]; [exact (Hu e He)|].
    exact (IH (S n) (gcap n cap) (capok_step n cap Hc) ltac:(lia) Hk Hf e He).
Qed.

Lemma ez_ev : forall t, ez t -> forall e, In e (ttrace t) -> evok e.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros H e He.
  - cbn [ttrace In] in He. contradiction.
  - cbn [ttrace In] in He. contradiction.
  - cbn [ttrace In] in He. contradiction.
  - cbn [ttrace In] in He. destruct He as [<-|[]]. apply ez_num_inv in H. unfold evok, esize. lia.
  - cbn [ttrace In] in He. destruct He as [<-|[]]. apply ez_str_inv in H. unfold evok, esize. lia.
  - rewrite tt_arr in He. destruct (ez_arr_inv _ H) as [Hn Hf].
    refine (tgo_arr_ev items 0 0 (or_introl (conj eq_refl eq_refl)) ltac:(lia) _ e He).
    rewrite Forall_forall in *. intros u Hu. exact (IH u Hu (Hf u Hu)).
  - rewrite tt_obj in He. destruct (ez_obj_inv _ H) as (Hn & Hk & Hf).
    refine (tgo_obj_ev ms 0 0 (or_introl (conj eq_refl eq_refl)) ltac:(lia) Hk _ e He).
    rewrite Forall_forall in *. intros m Hm. exact (IH m Hm (Hf (snd m) (in_map snd ms m Hm))).
Qed.

Lemma szok_ez : forall t N, szok N t -> Z.of_nat N <= 3 * 2 ^ 20 -> ez t.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros N H HN.
  - constructor.
  - constructor.
  - constructor.
  - apply szok_num_inv in H. constructor. lia.
  - apply szok_str_inv in H. constructor. lia.
  - destruct (szok_arr_inv _ _ H) as [Hn Hf]. constructor; [lia|].
    rewrite Forall_forall in *. intros u Hu. exact (IH u Hu N (Hf u Hu) HN).
  - destruct (szok_obj_inv _ _ H) as (Hn & Hk & Hf). constructor; [lia| |].
    + rewrite Forall_forall in *. intros m Hm. specialize (Hk m Hm). cbv beta in *. lia.
    + rewrite Forall_forall in *. intros u Hu. apply in_map_iff in Hu as (m & <- & Hm).
      exact (IH m Hm N (Hf (snd m) (in_map snd ms m Hm)) HN).
Qed.

Lemma set_model_in : forall ms k v m, In m (pj_set_model ms k v) -> In m ms \/ m = (k, v).
Proof.
  induction ms as [|[k0 v0] r IH]; intros k v m H; cbn [pj_set_model] in H.
  - cbn [In] in H. destruct H as [<-|[]]. right. reflexivity.
  - destruct (list_eq_dec Z.eq_dec k0 k) as [E|E]; cbn [In] in H.
    + destruct H as [<-|H]; [right; subst; reflexivity | left; right; exact H].
    + destruct H as [<-|H]; [left; left; reflexivity|].
      destruct (IH k v m H) as [H'|H']; [left; right; exact H' | right; exact H'].
Qed.

Lemma set_model_len : forall ms k v, (length (pj_set_model ms k v) <= S (length ms))%nat.
Proof.
  induction ms as [|[k0 v0] r IH]; intros k v; cbn [pj_set_model]; [cbn; lia|].
  destruct (list_eq_dec Z.eq_dec k0 k); cbn [length]; [lia|]. specialize (IH k v). lia.
Qed.

Lemma set_ez : forall ms k sv N, szok N (JObj ms) -> Z.of_nat N <= 3 * 2 ^ 20 ->
  Z.of_nat (length (flat_map ech k)) + 17 <= 2 ^ 27 -> Z.of_nat (length (flat_map ech sv)) + 17 <= 2 ^ 27 ->
  ez (JObj (pj_set_model ms k (JStr sv))).
Proof.
  intros ms k sv N H HN Hk Hs. pose proof (szok_ez _ _ H HN) as Ez.
  destruct (szok_obj_inv _ _ H) as (Hn & _ & _). destruct (ez_obj_inv _ Ez) as (_ & Ek & Ev).
  pose proof (set_model_len ms k (JStr sv)) as Hl.
  constructor; [lia| |].
  - rewrite Forall_forall in *. intros m Hm. destruct (set_model_in _ _ _ _ Hm) as [Hm'| ->]; [exact (Ek m Hm') | exact Hk].
  - rewrite Forall_forall in *. intros u Hu. apply in_map_iff in Hu as (m & <- & Hm).
    destruct (set_model_in _ _ _ _ Hm) as [Hm'| ->].
    + apply Ev. apply in_map. exact Hm'.
    + cbn [snd]. constructor. exact Hs.
Qed.

Theorem read_ez : forall sm x t, json_read sm x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 -> ez t.
Proof. intros sm x t H HN. exact (szok_ez _ _ (s_read sm x t H) HN). Qed.

Theorem set_esz : forall sm x t k sv, json_read sm x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  Z.of_nat (length (flat_map ech k)) + 17 <= 2 ^ 27 -> Z.of_nat (length (flat_map ech sv)) + 17 <= 2 ^ 27 ->
  forall e, In e (ttrace t) \/
    In e (ttrace (match t with JObj ms => JObj (pj_set_model ms k (JStr sv)) | _ => t end)) ->
  is_call e = true -> Z.of_nat (esize e) + 16 <= 2 ^ 27.
Proof.
  intros sm x t k sv H HN Hk Hs e He _. pose proof (s_read sm x t H) as Sz. pose proof (szok_ez _ _ Sz HN) as Ez.
  destruct He as [He|He]; [exact (ez_ev t Ez e He)|].
  destruct t as [| | | | | | ms]; try exact (ez_ev _ Ez e He).
  exact (ez_ev _ (set_ez ms k sv (length x) Sz HN Hk Hs) e He).
Qed.

Theorem crt_esz : forall sm x t, json_read sm x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  forall e, In e (ttrace t) \/ In e (ttrace (check_round_trip_c.crt_tree t)) -> is_call e = true ->
  Z.of_nat (esize e) + 16 <= 2 ^ 27.
Proof.
  intros sm x t H HN.
  assert (Km : Z.of_nat (length (flat_map ech check_round_trip_c.MOD_AT)) + 17 <= 2 ^ 27).
  { pose proof (fme_le check_round_trip_c.MOD_AT) as F. unfold check_round_trip_c.MOD_AT in *. cbn [length] in F. lia. }
  assert (Ks : Z.of_nat (length (flat_map ech check_round_trip_c.STAMP)) + 17 <= 2 ^ 27).
  { pose proof (fme_le check_round_trip_c.STAMP) as F. unfold check_round_trip_c.STAMP in *. cbn [length] in F. lia. }
  exact (set_esz sm x t _ _ H HN Km Ks).
Qed.
