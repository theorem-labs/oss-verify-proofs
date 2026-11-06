From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0i YO0f YO0g YO0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AllocPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
Import ListNotations.
Local Open Scope Z_scope.

Ltac sinj H := apply some_inj in H; apply pair_inj in H; let H1 := fresh in let H2 := fresh in destruct H as [H1 H2].

Definition elen (s : list Z) : nat := length (flat_map ech s).

Fixpoint bfc (x : list Z) : nat :=
  match x with
  | [] => 0%nat
  | b :: r =>
    if b =? 34 then 0%nat
    else if b =? 92 then
      match r with
      | [] => 0%nat
      | e :: r2 => ((if Z.eqb e 98 || Z.eqb e 102 then 1 else 0) + bfc r2)%nat
      end
    else bfc r
  end.

Lemma elen_app : forall a b, elen (a ++ b) = (elen a + elen b)%nat.
Proof. intros a b. unfold elen. rewrite flat_map_app, length_app. reflexivity. Qed.

Lemma elen_one : forall c, elen [c] = length (ech c).
Proof. intros c. unfold elen. cbn [flat_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma ech_plain : forall c, 32 <= c -> c <> 34 -> c <> 92 -> ech c = [c].
Proof.
  intros c H1 H2 H3. unfold ech, special.
  rewrite (proj2 (Z.eqb_neq c 34) H2), (proj2 (Z.eqb_neq c 92) H3), (proj2 (Z.ltb_ge c 32) H1). reflexivity.
Qed.

Lemma ech_len : forall c, (length (ech c) <= 6)%nat.
Proof.
  intros c. unfold ech, esc.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [length]; lia.
Qed.

Lemma elen_plain : forall l, Forall (fun b => 32 <= b /\ b <> 34 /\ b <> 92) l -> elen l = length l.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [[H1 [H2 H3]] Hl].
  change (b :: l) with ([b] ++ l). rewrite elen_app, elen_one, ech_plain by assumption.
  rewrite IH by exact Hl. reflexivity.
Qed.

Lemma utf8_high : forall cp, 128 <= cp -> Forall (fun b => 32 <= b /\ b <> 34 /\ b <> 92) (utf8 cp).
Proof.
  intros cp H. unfold utf8.
  destruct (Z.ltb_spec cp 128) as [L|L]; [lia|].
  pose proof (Z.div_pos cp 64 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos cp 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos cp 262144 ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound cp 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (cp / 64) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (cp / 4096) 64 ltac:(lia)).
  destruct (cp <? 2048); [|destruct (cp <? 65536)];
    repeat (apply Forall_cons; [split; [|split]; lia|]); apply Forall_nil.
Qed.

Lemma elen_utf8 : forall cp, 0 < cp -> (elen (utf8 cp) <= 6)%nat.
Proof.
  intros cp H. destruct (Z.ltb_spec cp 128) as [L|L].
  - assert (E : utf8 cp = [cp]) by (unfold utf8; rewrite (proj2 (Z.ltb_lt cp 128) L); reflexivity).
    rewrite E, elen_one. apply ech_len.
  - rewrite (elen_plain _ (utf8_high cp L)). pose proof (utf8_len cp) as U. revert U.
    destruct (cp <? 65536); cbv iota; intros U; lia.
Qed.

Lemma bfc_plain : forall b r, b <> 34 -> b <> 92 -> bfc (b :: r) = bfc r.
Proof.
  intros b r H1 H2. cbn [bfc].
  rewrite (proj2 (Z.eqb_neq b 34) H1), (proj2 (Z.eqb_neq b 92) H2). reflexivity.
Qed.

Lemma bfc_esc : forall e r, bfc (92 :: e :: r) = ((if Z.eqb e 98 || Z.eqb e 102 then 1 else 0) + bfc r)%nat.
Proof. reflexivity. Qed.

Lemma bfc_u : forall r, bfc (92 :: 117 :: r) = bfc r.
Proof. reflexivity. Qed.

Lemma escape_ech : forall e c, escape e = Some c ->
  (length (ech c) <= 2 + 4 * (if Z.eqb e 98 || Z.eqb e 102 then 1 else 0))%nat.
Proof.
  intros e c H. unfold escape in H. revert H.
  destruct (Z.eqb_spec e 34) as [->|N1]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 92) as [->|N2]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 47) as [->|N3]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 98) as [->|N4]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 102) as [->|N5]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 110) as [->|N6]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 114) as [->|N7]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  destruct (Z.eqb_spec e 116) as [->|N8]; [intros H; injection H as <-; apply Nat.leb_le; reflexivity|].
  intros H; discriminate H.
Qed.

Theorem decode_elen : forall x s r, decode x = Some (s, r) ->
  (elen s + 1 + length r <= length x + 4 * bfc x)%nat /\ (2 * bfc x + 1 + length r <= length x)%nat.
Proof.
  intro x. remember (length x) as n eqn:Hn. revert x Hn.
  induction n as [n IH] using lt_wf_ind. intros x Hn s r H.
  destruct x as [|b r0]; [discriminate|]. cbn [decode] in H.
  destruct (b =? 34) eqn:E34.
  - sinj H. subst s r n.
    assert (B : bfc (b :: r0) = 0%nat) by (cbn [bfc]; rewrite E34; reflexivity).
    rewrite B. unfold elen. cbn [flat_map length]. lia.
  - destruct (b <? 32) eqn:E32; [discriminate|].
    destruct (negb (b =? 92)) eqn:E92.
    + destruct (decode r0) as [[s1 r1]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
      apply negb_true_iff in E92. apply Z.eqb_neq in E92. apply Z.eqb_neq in E34. apply Z.ltb_ge in E32.
      cbn [length] in Hn.
      destruct (IH (length r0) ltac:(lia) r0 eq_refl s1 r1 Hd) as [A B].
      rewrite bfc_plain by assumption. rewrite elen_app, elen_one, ech_plain by assumption.
      cbn [length]. lia.
    + apply negb_false_iff in E92. apply Z.eqb_eq in E92. subst b.
      destruct r0 as [|e r2]; [discriminate|].
      destruct (e =? 117) eqn:Eu.
      * apply Z.eqb_eq in Eu. subst e.
        destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; try discriminate.
        destruct (hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Hx; [|discriminate].
        destruct (hex4_some _ _ Hx) as (a0 & a1 & a2 & a3 & r' & Heq & N0 & N0' & N1 & N1' & N2 & N2' & N3 & N3' & Hcp).
        inversion Heq; subst a0 a1 a2 a3 r'. clear Heq.
        destruct (cp =? 0) eqn:Ec0; [discriminate|]. apply Z.eqb_neq in Ec0.
        rewrite bfc_u. rewrite !bfc_plain by assumption.
        destruct ((55296 <=? cp) && (cp <? 56320)) eqn:Ehi.
        -- apply andb_true_iff in Ehi as [Ehi1 Ehi2]. apply Z.leb_le in Ehi1. apply Z.ltb_lt in Ehi2.
           destruct r3 as [|b1 [|b2 [|m0 [|m1 [|m2 [|m3 r4]]]]]]; try discriminate.
           destruct (low (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: r4)) as [lo|] eqn:Hl; [|discriminate].
           destruct (low_some _ _ Hl) as (n0 & n1 & n2 & n3 & r'' & Heq & M0 & M0' & M1 & M1' & M2 & M2' & M3 & M3' & Hlo).
           inversion Heq; subst b1 b2 n0 n1 n2 n3 r''. clear Heq.
           destruct (decode r4) as [[s4 r5]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
           cbn [length] in Hn.
           destruct (IH (length r4) ltac:(lia) r4 eq_refl s4 r5 Hd) as [A B].
           rewrite bfc_u. rewrite !bfc_plain by assumption.
           pose proof (pair_cp_range cp lo (conj Ehi1 Ehi2) Hlo) as Hp.
           pose proof (elen_utf8 (pair_cp cp lo) ltac:(lia)).
           rewrite elen_app. cbn [length]. lia.
        -- destruct ((56320 <=? cp) && (cp <? 57344)) eqn:Elo; [discriminate|].
           destruct (decode r3) as [[s3 r5]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
           cbn [length] in Hn.
           destruct (IH (length r3) ltac:(lia) r3 eq_refl s3 r5 Hd) as [A B].
           pose proof (elen_utf8 cp ltac:(lia)).
           rewrite elen_app. cbn [length]. lia.
      * destruct (escape e) as [c|] eqn:He; [|discriminate].
        destruct (decode r2) as [[s2 r5]|] eqn:Hd; [|discriminate]. sinj H. subst s r.
        cbn [length] in Hn.
        destruct (IH (length r2) ltac:(lia) r2 eq_refl s2 r5 Hd) as [A B].
        pose proof (escape_ech e c He) as Ec.
        rewrite bfc_esc, elen_app, elen_one. cbn [length].
        revert Ec. destruct (Z.eqb e 98 || Z.eqb e 102); cbv iota; intros Ec; lia.
Qed.

Theorem jr_string_esc : forall z ok s r t ok', jr_string z ok = (Some (s, r), t, ok') ->
  exists q, t = [EAlloc (S q)] /\ (length r + S q = length z)%nat /\
    (elen s <= q + 4 * bfc z)%nat /\ (elen s <= 3 * q)%nat.
Proof.
  intros z ok s r t ok' H. pose proof (jr_string_spec z ok) as Hs. rewrite H in Hs.
  destruct Hs as (q & _ & Hd & Ht & Hl). exists q. split; [exact Ht|]. split; [exact Hl|].
  destruct (decode_elen z s r Hd) as [A B]. lia.
Qed.

Theorem ttrace_str : forall s, ttrace (JStr s) = [EAlloc (S (elen s))].
Proof. reflexivity. Qed.

Definition rsl (s : list Z) : nat := ((elen s + 2) / 3 + 2)%nat.

Lemma rsl_le : forall s q, (elen s <= 3 * q)%nat -> (rsl s <= q + 2)%nat.
Proof.
  intros s q H. unfold rsl.
  assert ((elen s + 2) / 3 < S q)%nat by (apply Nat.Div0.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma rsl_z : forall s, Z.of_nat (rsl s) = (Z.of_nat (elen s) + 2) / 3 + 2.
Proof. intros s. unfold rsl. rewrite Nat2Z.inj_add, Nat2Z.inj_div, Nat2Z.inj_add. reflexivity. Qed.

Definition rkw (o : bool) (N : nat) : nat :=
  match N with O => 0%nat | S _ => (S N + (if o then N else 0))%nat end.

Fixpoint rtw (t : jv) : nat :=
  match t with
  | JNum txt _ => Nat.max 1 (length txt)
  | JStr s => rsl s
  | JArr items => (rkw false (length items) + list_sum (map rtw items))%nat
  | JObj ms => (rkw true (length ms) + list_sum (map (fun '(k, u) => (rsl k + rtw u)%nat) ms))%nat
  | _ => 0%nat
  end.

Lemma rtw_arr : forall items, rtw (JArr items) = (rkw false (length items) + list_sum (map rtw items))%nat.
Proof. reflexivity. Qed.

Lemma rtw_obj : forall ms,
  rtw (JObj ms) = (rkw true (length ms) + list_sum (map (fun '(k, u) => (rsl k + rtw u)%nat) ms))%nat.
Proof. reflexivity. Qed.

Definition racc (o : bool) (L : list (list Z * jv)) : nat :=
  list_sum (map (fun '(k, u) => (1 + (if o then rsl k + 1 else 0) + rtw u)%nat) L).

Lemma racc_cons : forall o k v L,
  racc o ((k, v) :: L) = (1 + (if o then rsl k + 1 else 0) + rtw v + racc o L)%nat.
Proof. intros o k v L. unfold racc. cbn [map]. rewrite lsum_cons. reflexivity. Qed.

Lemma racc_rev_snoc : forall o L k v,
  racc o (rev L ++ [(k, v)]) = (racc o L + (1 + (if o then rsl k + 1 else 0) + rtw v))%nat.
Proof.
  intros o L k v. unfold racc. rewrite map_app, lsum_app, map_rev, lsum_rev. cbn [map list_sum fold_right]. lia.
Qed.

Lemma racc_arr : forall L, racc false L = (length L + list_sum (map rtw (map snd L)))%nat.
Proof. induction L as [|[k u] L IH]; [reflexivity|]. rewrite racc_cons. cbn [map length snd]. rewrite lsum_cons, IH. lia. Qed.

Lemma racc_obj : forall L, racc true L = (2 * length L + list_sum (map (fun '(k, u) => (rsl k + rtw u)%nat) L))%nat.
Proof. induction L as [|[k u] L IH]; [reflexivity|]. rewrite racc_cons. cbn [map length]. rewrite lsum_cons, IH. lia. Qed.

Lemma rtw_mk : forall o L, L <> [] -> rtw (mk o L) = (1 + racc o L)%nat.
Proof.
  intros o L H. unfold mk. destruct L as [|m L']; [contradiction|]. destruct o.
  - rewrite rtw_obj, racc_obj. cbn [length rkw]. lia.
  - rewrite rtw_arr, racc_arr, length_map. cbn [length rkw]. lia.
Qed.

Lemma lit_tw : forall w v x ok t r tr ok', w <> [] -> lit w v x ok = (Some (t, r), tr, ok') ->
  t = v /\ (length r < length x)%nat.
Proof.
  intros w v x ok t r tr ok' Hw H. pose proof (lit_spec w v x ok Hw) as Hs. rewrite H in Hs.
  destruct Hs as [_ Hr]. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as <- _ _ _. split; [reflexivity|exact Hr].
Qed.

Lemma jr_name_sl : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  ((if o then rsl nm + 1 else 0) + length y1 <= length y)%nat /\
  (o = true -> exists q, tn = [EAlloc (S q)] /\ (elen nm <= 3 * q)%nat).
Proof.
  intros o y ok nm y1 tn ok2 H. destruct o; cbv iota.
  - unfold jr_name in H. pose proof (skip_len y) as Hy.
    destruct (skip y) as [|b z] eqn:Ey; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
    cbn [length] in Hy.
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([s r] & t1 & ok1 & t2 & Hj & H & Ht).
    destruct (jr_string_esc z ok s r t1 ok1 Hj) as (q & Ht1 & Hl & _ & He).
    cbv beta iota in H.
    pose proof (skip_len r) as Hr.
    destruct (skip r) as [|c r1]; cbv beta iota in H.
    + apply jbind_some in H as (? & ? & ? & ? & ? & H & ?). unfold jrefuse in H. discriminate.
    + cbn [length] in Hr.
      destruct (c =? 58); cbv beta iota in H.
      * unfold jret in H. injection H as <- <- Ht2 _. pose proof (rsl_le s q He).
        split; [lia|]. intros _. exists q. split; [subst tn t1 t2; reflexivity|exact He].
      * apply jbind_some in H as (? & ? & ? & ? & ? & H & ?). unfold jrefuse in H. discriminate.
  - unfold jr_name, jret in H. injection H as <- <- _ _. split; [lia|]. discriminate.
Qed.

Section Walk.

Variable sm : list Z -> Z * Z.

Theorem jr_number_txt : forall x ok u r t ok', jr_number sm x ok = (Some (u, r), t, ok') ->
  exists txt bits, u = JNum txt bits /\ t = [EAlloc (S (length txt))] /\ (1 <= length txt)%nat /\
    (length txt + length r = length x)%nat.
Proof.
  intros x ok u r t ok' H. unfold jr_number in H. cbv zeta in H.
  remember (match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) as j eqn:Ej.
  destruct (skipn j x) as [|c z] eqn:Ez; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)) eqn:Ed; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end) eqn:E0; cbv beta iota in H;
    [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:Es. cbv beta iota in H.
  apply span_forall in Es as [_ Hz].
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & Ha & H & Ht).
  destruct (whole sm (firstn j x ++ c :: a)) eqn:Ew; [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as Hu Hr Ht2 _.
  unfold jalloc, take in Ha. destruct ok as [|bo ok]; [|destruct bo]; cbv beta iota in Ha;
    [injection Ha as _ Ht1 _|injection Ha as _ Ht1 _|discriminate Ha].
  all: exists (firstn j x ++ c :: a), (snd (sm (firstn j x ++ c :: a))).
  all: split; [symmetry; exact Hu|]; split; [subst; reflexivity|]; split; [rewrite length_app; cbn [length]; lia|].
  all: pose proof (firstn_skipn j x) as Hx; rewrite Ez, Hz in Hx; subst r'.
  all: rewrite <- Hx at 2; rewrite !length_app; cbn [length]; rewrite length_app; lia.
Qed.

Theorem number_trace_same : forall x ok u r t ok', jr_number sm x ok = (Some (u, r), t, ok') -> ttrace u = t.
Proof.
  intros x ok u r t ok' H. destruct (jr_number_txt x ok u r t ok' H) as (txt & bits & -> & -> & _). reflexivity.
Qed.

Lemma cont_tw : forall f d o b y ok t r tr ok',
  (forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     (rtw t + length r <= length y + 1 + racc o acc)%nat) ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (t, r), tr, ok') ->
  (rtw t + length r <= length (b :: y))%nat.
Proof.
  intros f d o b y ok t r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H. pose proof (skip_len y) as Hy. cbn [length].
  assert (Ha : racc o [] = 0%nat) by reflexivity.
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  - pose proof (IHl _ _ _ _ _ _ _ _ _ _ _ H) as E. rewrite Ha in E. cbn [length] in E. lia.
  - destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as <- <- _ _. cbn [length] in Hy.
      assert (rtw (mk o []) = 0%nat) by (destruct o; reflexivity). lia.
    + pose proof (IHl _ _ _ _ _ _ _ _ _ _ _ H) as E. rewrite Ha in E. cbn [length] in E, Hy. lia.
Qed.

Lemma tw_fuel : forall f,
  (forall d x ok t r tr ok', jrv sm f d x ok = (Some (t, r), tr, ok') -> (rtw t + length r <= length x)%nat) /\
  (forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     (rtw t + length r <= length y + 1 + racc o acc)%nat).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123); cbv beta iota in H.
      { pose proof (cont_tw f d true b y ok t r tr ok' IHl H). lia. }
      destruct (b =? 91); cbv beta iota in H.
      { pose proof (cont_tw f d false b y ok t r tr ok' IHl H). lia. }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
        destruct (jr_string_esc y ok s r1 t1 ok1 Hj) as (q & _ & Hl & _ & He).
        cbv beta iota in H. unfold jret in H. injection H as <- <- _ _.
        pose proof (rsl_le s q He). cbn [rtw]. cbn [length] in Hsx. lia. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (lit_tw w_true JTrue _ _ _ _ _ _ ltac:(unfold w_true; discriminate) H) as [-> B].
        cbn [rtw]. lia. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (lit_tw w_false JFalse _ _ _ _ _ _ ltac:(unfold w_false; discriminate) H) as [-> B].
        cbn [rtw]. lia. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (lit_tw w_null JNull _ _ _ _ _ _ ltac:(unfold w_null; discriminate) H) as [-> B].
        cbn [rtw]. lia. }
      destruct (jr_number_txt (b :: y) ok t r tr ok' H) as (txt & bits & -> & _ & H1 & Hl).
      cbn [rtw]. lia.
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (IHv d y1 ok2 v r0 tv ok3 Ev) as Bv.
      destruct (jr_name_sl o y ok1 nm y1 tn ok2 En) as [Hy1 _].
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      destruct (c =? 44); cbv beta iota in H.
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' H) as E.
        rewrite racc_cons in E. lia. }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as <- <- _ _.
      cbn [rev]. rewrite rtw_mk by (intro E; apply app_eq_nil in E; destruct E as [_ E]; discriminate E).
      rewrite racc_rev_snoc. lia.
Qed.

Theorem rtw_read : forall x t, json_read sm x = Some t -> (rtw t <= length x)%nat.
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. pose proof (proj1 (tw_fuel _) 0%nat x [] t' r tr ok' E). lia.
Qed.

End Walk.

Fixpoint rfcap (k n cap : nat) : nat :=
  match k with
  | O => cap
  | S k' => rfcap k' (S n) (gcap n cap)
  end.

Definition rkb (o : bool) (cap : nat) : list nat :=
  if Nat.eqb cap 0 then [] else if o then [(56 * cap)%nat; (8 * cap)%nat] else [(56 * cap)%nat].

Fixpoint rtsz (t : jv) : list nat :=
  match t with
  | JNum txt _ => [S (length txt)]
  | JStr s => [S (elen s)]
  | JArr items => rkb false (rfcap (length items) 0 0) ++ flat_map rtsz items
  | JObj ms => rkb true (rfcap (length ms) 0 0) ++ flat_map (fun '(k, u) => S (elen k) :: rtsz u) ms
  | _ => []
  end.

Lemma rtsz_arr : forall items, rtsz (JArr items) = rkb false (rfcap (length items) 0 0) ++ flat_map rtsz items.
Proof. reflexivity. Qed.

Lemma rtsz_obj : forall ms,
  rtsz (JObj ms) = rkb true (rfcap (length ms) 0 0) ++ flat_map (fun '(k, u) => S (elen k) :: rtsz u) ms.
Proof. reflexivity. Qed.

Lemma rm1n_perm : forall k s s', Permutation s s' -> Permutation (rm1n k s) (rm1n k s').
Proof.
  intros k s s' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
  - constructor.
  - cbn [rm1n]. destruct (Nat.eqb x k); [exact H|]. apply perm_skip, IH.
  - cbn [rm1n]. destruct (Nat.eqb y k) eqn:Ey; destruct (Nat.eqb x k) eqn:Ex.
    + apply Nat.eqb_eq in Ey, Ex. subst. apply Permutation_refl.
    + apply Permutation_refl.
    + apply Permutation_refl.
    + apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma lsz_ev_perm : forall s s' e, Permutation s s' -> Permutation (lsz_ev s e) (lsz_ev s' e).
Proof.
  intros s s' e H. destruct e as [n|[|m] n|n|n]; cbn [lsz_ev].
  - apply perm_skip, H.
  - apply perm_skip, H.
  - apply perm_skip, rm1n_perm, H.
  - exact H.
  - apply rm1n_perm, H.
Qed.

Lemma lszf_perm : forall tr s s', Permutation s s' -> Permutation (fold_left lsz_ev tr s) (fold_left lsz_ev tr s').
Proof.
  induction tr as [|e tr IH]; intros s s' H; cbn [fold_left]; [exact H|]. apply IH, lsz_ev_perm, H.
Qed.

Lemma rm1n_hd : forall k s, rm1n k (k :: s) = s.
Proof. intros k s. cbn [rm1n]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma rm1n_ne : forall k a s, a <> k -> rm1n k (a :: s) = a :: rm1n k s.
Proof. intros k a s H. cbn [rm1n]. destruct (Nat.eqb_spec a k); [contradiction|reflexivity]. Qed.

Lemma lsz_grow_0 : forall s n, lsz_ev s (EGrow 0 n) = n :: s.
Proof. reflexivity. Qed.

Lemma lsz_grow_S : forall s m n, m <> 0%nat -> lsz_ev s (EGrow m n) = n :: rm1n m s.
Proof. intros s [|m] n H; [contradiction|reflexivity]. Qed.

Lemma lsz_alloc : forall s n, lsz_ev s (EAlloc n) = n :: s.
Proof. reflexivity. Qed.

Lemma rkb_S : forall o c, c <> 0%nat -> rkb o c = if o then [(56 * c)%nat; (8 * c)%nat] else [(56 * c)%nat].
Proof. intros o c H. unfold rkb. destruct (Nat.eqb_spec c 0); [contradiction|reflexivity]. Qed.

Lemma grow_perm : forall o n cap s s0, Permutation s (rkb o cap ++ s0) ->
  Permutation (fold_left lsz_ev (grow_ev o n cap) s) (rkb o (gcap n cap) ++ s0).
Proof.
  intros o n cap s s0 H. unfold grow_ev, gcap.
  destruct (Nat.ltb n cap); cbv iota; [exact H|].
  destruct (Nat.eqb_spec cap 0) as [E0|N0]; cbv iota.
  - subst cap. change (rkb o 0) with (@nil nat) in H. cbn [app] in H.
    rewrite rkb_S by discriminate. rewrite !Nat.mul_0_r.
    destruct o; cbn [fold_left app]; rewrite ?lsz_grow_0.
    + eapply Permutation_trans; [apply perm_swap|]. apply perm_skip, perm_skip, H.
    + apply perm_skip, H.
  - rewrite (rkb_S o cap N0) in H. rewrite (rkb_S o (2 * cap)) by lia.
    destruct o; cbn [fold_left app] in *.
    + rewrite !lsz_grow_S by lia. rewrite rm1n_ne by lia.
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip, perm_skip.
      eapply Permutation_trans; [apply rm1n_perm, rm1n_perm, H|]. rewrite !rm1n_hd. apply Permutation_refl.
    + rewrite lsz_grow_S by lia. apply perm_skip.
      eapply Permutation_trans; [apply rm1n_perm, H|]. rewrite rm1n_hd. apply Permutation_refl.
Qed.

Lemma pswap : forall (l1 l2 l3 : list nat), Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof. intros. rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm. Qed.

Lemma tgo_arr_perm : forall l n cap s s0,
  Forall (fun u => forall s, Permutation (fold_left lsz_ev (ttrace u) s) (rtsz u ++ s)) l ->
  Permutation s (rkb false cap ++ s0) ->
  Permutation (fold_left lsz_ev (tgo_arr n cap l) s) (rkb false (rfcap (length l) n cap) ++ flat_map rtsz l ++ s0).
Proof.
  induction l as [|u r IH]; intros n cap s s0 HF H.
  - exact H.
  - apply Forall_cons_iff in HF as [Hu HF].
    cbn [tgo_arr length rfcap flat_map]. rewrite !fold_left_app.
    assert (G : Permutation (fold_left lsz_ev (ttrace u) (fold_left lsz_ev (grow_ev false n cap) s))
                  (rkb false (gcap n cap) ++ rtsz u ++ s0)).
    { eapply Permutation_trans; [apply lszf_perm, grow_perm, H|].
      eapply Permutation_trans; [apply Hu|]. apply pswap. }
    eapply Permutation_trans; [exact (IH (S n) (gcap n cap) _ _ HF G)|].
    apply Permutation_app_head. rewrite <- app_assoc. apply pswap.
Qed.

Lemma tgo_obj_perm : forall l n cap s s0,
  Forall (fun m => forall s, Permutation (fold_left lsz_ev (ttrace (snd m)) s) (rtsz (snd m) ++ s)) l ->
  Permutation s (rkb true cap ++ s0) ->
  Permutation (fold_left lsz_ev (tgo_obj n cap l) s)
    (rkb true (rfcap (length l) n cap) ++ flat_map (fun '(k, u) => S (elen k) :: rtsz u) l ++ s0).
Proof.
  induction l as [|[k u] r IH]; intros n cap s s0 HF H.
  - exact H.
  - apply Forall_cons_iff in HF as [Hu HF]. cbn [snd] in Hu.
    cbn [tgo_obj length rfcap flat_map]. rewrite fold_left_app. cbn [fold_left]. rewrite fold_left_app, lsz_alloc.
    assert (G : Permutation (fold_left lsz_ev (ttrace u) (S (elen k) :: fold_left lsz_ev (grow_ev true n cap) s))
                  (rkb true (gcap n cap) ++ (S (elen k) :: rtsz u) ++ s0)).
    { eapply Permutation_trans; [apply lszf_perm, perm_skip, grow_perm, H|].
      eapply Permutation_trans; [apply Hu|].
      eapply Permutation_trans; [exact (pswap (rtsz u) [S (elen k)] (rkb true (gcap n cap) ++ s0))|].
      eapply Permutation_trans; [exact (perm_skip (S (elen k)) (pswap (rtsz u) (rkb true (gcap n cap)) s0))|].
      exact (pswap [S (elen k)] (rkb true (gcap n cap)) (rtsz u ++ s0)). }
    eapply Permutation_trans; [exact (IH (S n) (gcap n cap) _ _ HF G)|].
    apply Permutation_app_head. rewrite <- app_assoc. apply pswap.
Qed.

Lemma rtsz_perm : forall t s, Permutation (fold_left lsz_ev (ttrace t) s) (rtsz t ++ s).
Proof.
  intros t. induction t as [| | | txt bits | s0 | items IH | ms IH] using jv_ind'; intros s.
  1-5: apply Permutation_refl.
  - rewrite tt_arr, rtsz_arr, <- app_assoc. apply (tgo_arr_perm items 0 0 s s IH). apply Permutation_refl.
  - rewrite tt_obj, rtsz_obj, <- app_assoc. apply (tgo_obj_perm ms 0 0 s s IH). apply Permutation_refl.
Qed.

Theorem lsz_ttrace : forall t, Permutation (lsz (ttrace t)) (rtsz t).
Proof. intros t. unfold lsz. rewrite <- (app_nil_r (rtsz t)). apply rtsz_perm. Qed.

Lemma rfcap_S : forall k n cap, rfcap (S k) n cap = gcap (n + k) (rfcap k n cap).
Proof.
  induction k as [|k IH]; intros n cap.
  - cbn [rfcap]. rewrite Nat.add_0_r. reflexivity.
  - change (rfcap (S (S k)) n cap) with (rfcap (S k) (S n) (gcap n cap)).
    rewrite IH. replace (S n + k)%nat with (n + S k)%nat by lia. reflexivity.
Qed.

Theorem rfcap_shape : forall N, (1 <= N)%nat ->
  exists j, rfcap N 0 0 = (8 * 2 ^ j)%nat /\ (N <= 8 * 2 ^ j)%nat /\ (j = 0%nat \/ 4 * 2 ^ j < N)%nat.
Proof.
  induction N as [|N IH]; intros H; [lia|].
  rewrite rfcap_S. cbn [Nat.add].
  destruct N as [|N'].
  - exists 0%nat. cbn. lia.
  - destruct (IH ltac:(lia)) as (j & E & H1 & H2). rewrite E. unfold gcap.
    pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as P.
    destruct (Nat.ltb_spec (S N') (8 * 2 ^ j)) as [L|L].
    + exists j. lia.
    + destruct (Nat.eqb_spec (8 * 2 ^ j) 0) as [Z0|Z0]; [lia|].
      exists (S j). rewrite Nat.pow_succ_r'. lia.
Qed.

Definition w2_tab : list Z := [0; 1; 6; 12; 17; 1; 28; 33; 38; 9; 49; 60; 17; 92; 102; 2; 33; 188; 220; 10; 65;
  380; 444; 18; 129; 774; 902; 34; 257; 1553; 1809; 66; 513; 3110; 3633; 130; 1025; 6230; 7270; 258; 2049;
  12476; 14556; 514; 4097; 24956; 29116; 1026; 2050].

Definition w2 (k : Z) : Z := nth (Z.to_nat k) w2_tab 0.

Definition gw (b : nat) : Z := w2 (band (Z.of_nat b + 16)).

Fixpoint chkp (f : Z -> bool) (lo : Z) (p : positive) : bool :=
  match p with
  | xH => f lo
  | xO q => chkp f lo q && chkp f (lo + Zpos q) q
  | xI q => f lo && chkp f (lo + 1) q && chkp f (lo + 1 + Zpos q) q
  end.

Lemma chkp_ok : forall f p lo, chkp f lo p = true -> forall z, lo <= z < lo + Zpos p -> f z = true.
Proof.
  intros f p. induction p as [q IH|q IH|]; intros lo H z Hz; cbn [chkp] in H.
  - apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    rewrite Pos2Z.inj_xI in Hz.
    destruct (Z.eq_dec z lo) as [->|N]; [exact H1|].
    destruct (Z_lt_dec z (lo + 1 + Zpos q)) as [L|L].
    + apply (IH (lo + 1) H2). lia.
    + apply (IH (lo + 1 + Zpos q) H3). lia.
  - rewrite Pos2Z.inj_xO in Hz. apply andb_true_iff in H as [H1 H2].
    destruct (Z_lt_dec z (lo + Zpos q)) as [L|L]; [apply (IH lo H1); lia|apply (IH (lo + Zpos q) H2); lia].
  - assert (z = lo) by lia. subst. exact H.
Qed.

Definition leaf_ok (e : Z) : bool :=
  let b := band (e + 17) in let w := w2 b in
  (1 <=? b) && (w <=? (e + 2) / 3 + 2) && (w <=? Z.max 1 e).

Lemma leaf_tab : chkp leaf_ok 0 131035%positive = true.
Proof. vm_compute. reflexivity. Qed.

Lemma leaf_at : forall e, 0 <= e < 131035 ->
  1 <= band (e + 17) /\ w2 (band (e + 17)) <= (e + 2) / 3 + 2 /\ w2 (band (e + 17)) <= Z.max 1 e.
Proof.
  intros e He. pose proof (chkp_ok leaf_ok 131035 0 leaf_tab e ltac:(lia)) as T.
  unfold leaf_ok in T. cbv zeta in T.
  apply andb_true_iff in T as [T T3]. apply andb_true_iff in T as [T1 T2].
  apply Z.leb_le in T1, T2, T3. auto.
Qed.

Lemma band_big : forall n, 131052 <= n -> band n = 48.
Proof.
  intros n H. unfold band.
  replace (YO0i.MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; unfold YO0i.MMAP_THRESHOLD; lia).
  reflexivity.
Qed.

Lemma band_range : forall n, 0 <= n -> 0 <= band n < 49.
Proof.
  intros n H. unfold band. destruct (YO0i.MMAP_THRESHOLD <=? n) eqn:E; cbv iota; [lia|].
  apply Z.leb_gt in E. destruct (YO0f.size_to_class_range n ltac:(lia)) as [R _]. lia.
Qed.

Lemma band_pos : forall n, 17 <= n -> 1 <= band n.
Proof.
  intros n H. destruct (Z_lt_dec n 131052) as [L|L].
  - destruct (leaf_at (n - 17) ltac:(lia)) as [B _]. replace (n - 17 + 17) with n in B by lia. exact B.
  - rewrite band_big by lia. lia.
Qed.

Lemma gw_str : forall s, gw (S (elen s)) <= Z.of_nat (rsl s).
Proof.
  intros s. rewrite rsl_z. unfold gw.
  replace (Z.of_nat (S (elen s)) + 16) with (Z.of_nat (elen s) + 17) by lia.
  destruct (Z_lt_dec (Z.of_nat (elen s)) 131035) as [L|L].
  - destruct (leaf_at (Z.of_nat (elen s)) ltac:(lia)) as (_ & T & _). exact T.
  - rewrite band_big by lia. change (w2 48) with 2050.
    assert (D : 6144 / 3 <= (Z.of_nat (elen s) + 2) / 3) by (apply Z.div_le_mono; lia).
    change (6144 / 3) with 2048 in D. lia.
Qed.

Lemma gw_num : forall L, gw (S L) <= Z.of_nat (Nat.max 1 L).
Proof.
  intros L. unfold gw. rewrite Nat2Z.inj_max. change (Z.of_nat 1) with 1.
  replace (Z.of_nat (S L) + 16) with (Z.of_nat L + 17) by lia.
  destruct (Z_lt_dec (Z.of_nat L) 131035) as [Lt|Lt].
  - destruct (leaf_at (Z.of_nat L) ltac:(lia)) as (_ & _ & T). exact T.
  - rewrite band_big by lia. change (w2 48) with 2050. lia.
Qed.

Lemma gw_big : forall b, 131036 <= Z.of_nat b -> gw b = 2050.
Proof. intros b H. unfold gw. rewrite band_big by lia. reflexivity. Qed.

Lemma gw_kids_tab : forall j, (1 <= j <= 8)%nat -> gw (56 * (8 * 2 ^ j)) <= Z.of_nat (4 * 2 ^ j + 2).
Proof.
  intros j Hj. destruct j as [|j]; [lia|].
  do 8 (destruct j as [|j]; [apply Z.leb_le; vm_compute; reflexivity|]). lia.
Qed.

Lemma gw_keys_tab : forall j, (1 <= j <= 10)%nat -> gw (8 * (8 * 2 ^ j)) <= Z.of_nat (4 * 2 ^ j + 1).
Proof.
  intros j Hj. destruct j as [|j]; [lia|].
  do 10 (destruct j as [|j]; [apply Z.leb_le; vm_compute; reflexivity|]). lia.
Qed.

Lemma gw_kids : forall j N, (1 <= N)%nat -> (j = 0%nat \/ 4 * 2 ^ j < N)%nat ->
  gw (56 * (8 * 2 ^ j)) <= Z.of_nat (S N).
Proof.
  intros j N H1 H2. destruct (Nat.eqb_spec j 0) as [->|Nj].
  - assert (T : gw (56 * (8 * 2 ^ 0)) <= 2) by (apply Z.leb_le; vm_compute; reflexivity). lia.
  - destruct H2 as [H2|H2]; [contradiction|].
    destruct (le_lt_dec j 8) as [Hj|Hj].
    + pose proof (gw_kids_tab j ltac:(lia)). lia.
    + assert (P : (2 ^ 9 <= 2 ^ j)%nat) by (apply Nat.pow_le_mono_r; lia).
      change (2 ^ 9)%nat with 512%nat in P. rewrite gw_big by lia. lia.
Qed.

Lemma gw_keys : forall j N, (1 <= N)%nat -> (j = 0%nat \/ 4 * 2 ^ j < N)%nat ->
  gw (8 * (8 * 2 ^ j)) <= Z.of_nat N.
Proof.
  intros j N H1 H2. destruct (Nat.eqb_spec j 0) as [->|Nj].
  - assert (T : gw (8 * (8 * 2 ^ 0)) <= 1) by (apply Z.leb_le; vm_compute; reflexivity). lia.
  - destruct H2 as [H2|H2]; [contradiction|].
    destruct (le_lt_dec j 10) as [Hj|Hj].
    + pose proof (gw_keys_tab j ltac:(lia)). lia.
    + assert (P : (2 ^ 11 <= 2 ^ j)%nat) by (apply Nat.pow_le_mono_r; lia).
      change (2 ^ 11)%nat with 2048%nat in P. rewrite gw_big by lia. lia.
Qed.

Lemma gw_kb : forall o N, zl (map gw (rkb o (rfcap N 0 0))) <= Z.of_nat (rkw o N).
Proof.
  intros o [|N]; [cbn; lia|].
  destruct (rfcap_shape (S N) ltac:(lia)) as (j & E & H1 & H2). rewrite E.
  pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as P.
  rewrite rkb_S by lia.
  pose proof (gw_kids j (S N) ltac:(lia) H2). pose proof (gw_keys j (S N) ltac:(lia) H2).
  destruct o; cbn [map zl rkw]; lia.
Qed.

Lemma arr_sum : forall items, Forall (fun u => zl (map gw (rtsz u)) <= Z.of_nat (rtw u)) items ->
  zl (map gw (flat_map rtsz items)) <= Z.of_nat (list_sum (map rtw items)).
Proof.
  induction items as [|u r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [flat_map map]. rewrite map_app, zl_app, lsum_cons.
  specialize (IH H2). lia.
Qed.

Lemma obj_sum : forall ms, Forall (fun m => zl (map gw (rtsz (snd m))) <= Z.of_nat (rtw (snd m))) ms ->
  zl (map gw (flat_map (fun '(k, u) => S (elen k) :: rtsz u) ms)) <=
    Z.of_nat (list_sum (map (fun '(k, u) => (rsl k + rtw u)%nat) ms)).
Proof.
  induction ms as [|[k u] r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [snd] in H1. cbn [flat_map map]. rewrite map_app, zl_app, lsum_cons.
  cbn [map zl]. specialize (IH H2). pose proof (gw_str k). lia.
Qed.

Theorem rtsz_tw : forall t, zl (map gw (rtsz t)) <= Z.of_nat (rtw t).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-3: cbn; lia.
  - cbn [rtsz map zl rtw]. pose proof (gw_num (length txt)). lia.
  - cbn [rtsz map zl rtw]. pose proof (gw_str s). lia.
  - rewrite rtsz_arr, rtw_arr, map_app, zl_app. pose proof (gw_kb false (length items)). pose proof (arr_sum items IH). lia.
  - rewrite rtsz_obj, rtw_obj, map_app, zl_app. pose proof (gw_kb true (length ms)). pose proof (obj_sum ms IH). lia.
Qed.

Lemma zsumZ_cons : forall f x l, zsumZ f (x :: l) = f x + zsumZ f l.
Proof. reflexivity. Qed.

Lemma zsumZ_add : forall f h l, zsumZ (fun k => f k + h k) l = zsumZ f l + zsumZ h l.
Proof. intros f h l. induction l as [|x l IH]; [reflexivity|]. rewrite !zsumZ_cons, IH. cbv beta. lia. Qed.

Lemma zsumZ_ext : forall f h l, (forall k, f k = h k) -> zsumZ f l = zsumZ h l.
Proof. intros f h l H. induction l as [|x l IH]; [reflexivity|]. rewrite !zsumZ_cons, IH, H. reflexivity. Qed.

Lemma zsumZ_zero : forall l, zsumZ (fun _ => 0) l = 0.
Proof. induction l as [|x l IH]; [reflexivity|]. rewrite zsumZ_cons, IH. reflexivity. Qed.

Lemma zsum_out : forall l j h, ~ In j l -> zsumZ (fun k => if j =? k then h k else 0) l = 0.
Proof.
  induction l as [|a l IH]; intros j h H; [reflexivity|].
  rewrite zsumZ_cons. cbv beta. destruct (Z.eqb_spec j a) as [->|N]; [exfalso; apply H; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros Hi. apply H. right. exact Hi.
Qed.

Lemma zsum_in : forall l j h, NoDup l -> In j l -> zsumZ (fun k => if j =? k then h k else 0) l = h j.
Proof.
  induction l as [|a l IH]; intros j h Hn Hi; [destruct Hi|].
  apply NoDup_cons_iff in Hn as [Ha Hn]. rewrite zsumZ_cons. cbv beta.
  destruct (Z.eqb_spec j a) as [->|N]; cbv iota.
  - rewrite zsum_out by exact Ha. lia.
  - destruct Hi as [Hi|Hi]; [congruence|]. rewrite IH by assumption. reflexivity.
Qed.

Lemma zsum_count : forall l : list nat,
  zsumZ (fun k => w2 k * Z.of_nat (length (filter (fun b => band (Z.of_nat b + 16) =? k) l))) (YO0f.zseq 0 49) =
  zl (map gw l).
Proof.
  induction l as [|b l IH].
  - cbn [map zl]. transitivity (zsumZ (fun _ => 0) (YO0f.zseq 0 49)); [|apply zsumZ_zero].
    apply zsumZ_ext. intros k. cbn [filter length Z.of_nat]. apply Z.mul_0_r.
  - cbn [map zl]. rewrite <- IH.
    rewrite (zsumZ_ext _ (fun k => w2 k * Z.of_nat (length (filter (fun b => band (Z.of_nat b + 16) =? k) l)) +
                                   (if band (Z.of_nat b + 16) =? k then w2 k else 0))).
    + rewrite zsumZ_add. rewrite (zsum_in _ (band (Z.of_nat b + 16)) w2).
      * unfold gw. lia.
      * apply YO0s.zseq_NoDup.
      * apply YO0g.In_zseq. pose proof (band_range (Z.of_nat b + 16) ltac:(lia)). lia.
    + intros k. cbn [filter]. destruct (band (Z.of_nat b + 16) =? k); cbn [length].
      * rewrite Nat2Z.inj_succ, Z.mul_succ_r. reflexivity.
      * rewrite Z.add_0_r. reflexivity.
Qed.

Definition beta2 (t : jv) (k : Z) : Z :=
  Z.of_nat (length (filter (fun b => band (Z.of_nat b + 16) =? k) (lsz (ttrace t)))).

Theorem pack_reparse : forall sm x t, json_read sm x = Some t ->
  zsumZ (fun k => w2 k * beta2 t k) (YO0f.zseq 0 49) <= Z.of_nat (length x).
Proof.
  intros sm x t H. unfold beta2. rewrite zsum_count.
  rewrite (zl_perm _ _ (Permutation_map gw (lsz_ttrace t))).
  pose proof (rtsz_tw t). pose proof (rtw_read sm x t H). lia.
Qed.

Theorem pack_reparse_doc : forall sm x t p, json_read sm x = Some t ->
  zsumZ (fun k => w2 k * Z.of_nat (length (filter (fun b => band (Z.of_nat b + 16) =? k)
    (lsz (snd (jr_run sm (wdoc t p) [])))))) (YO0f.zseq 0 49) <= Z.of_nat (length x).
Proof.
  intros sm x t p H. rewrite (G9_trace sm t (wf_read sm x t H) p). exact (pack_reparse sm x t H).
Qed.

Lemma rtsz_pos : forall t, Forall (fun b => (1 <= b)%nat) (rtsz t).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-3: constructor.
  - constructor; [lia|constructor].
  - constructor; [lia|constructor].
  - rewrite rtsz_arr. apply Forall_app. split.
    + unfold rkb. destruct (Nat.eqb_spec (rfcap (length items) 0 0) 0); cbv iota; [constructor|].
      repeat (apply Forall_cons; [lia|]); apply Forall_nil.
    + induction items as [|u r IHr]; [constructor|]. apply Forall_cons_iff in IH as [H1 H2].
      cbn [flat_map]. apply Forall_app. split; [exact H1|exact (IHr H2)].
  - rewrite rtsz_obj. apply Forall_app. split.
    + unfold rkb. destruct (Nat.eqb_spec (rfcap (length ms) 0 0) 0); cbv iota; [constructor|].
      repeat (apply Forall_cons; [lia|]); apply Forall_nil.
    + induction ms as [|[k u] r IHr]; [constructor|]. apply Forall_cons_iff in IH as [H1 H2]. cbn [snd] in H1.
      cbn [flat_map]. apply Forall_app. split; [constructor; [lia|exact H1]|exact (IHr H2)].
Qed.

Lemma filter0 : forall l, (forall b, In b l -> (1 <= b)%nat) -> filter (fun b => band (Z.of_nat b + 16) =? 0) l = [].
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|]. cbn [filter].
  assert (B : 1 <= band (Z.of_nat b + 16)) by (apply band_pos; pose proof (H b (or_introl eq_refl)); lia).
  destruct (Z.eqb_spec (band (Z.of_nat b + 16)) 0) as [E|E]; cbv iota; [lia|].
  apply IH. intros c Hc. apply H. right. exact Hc.
Qed.

Theorem beta2_zero : forall t, beta2 t 0 = 0.
Proof.
  intros t. unfold beta2. rewrite filter0; [reflexivity|].
  intros b Hb. apply (Permutation_in _ (lsz_ttrace t)) in Hb.
  exact (proj1 (Forall_forall _ _) (rtsz_pos t) b Hb).
Qed.

Lemma w2_tab_pos : chkp (fun k => 1 <=? w2 k) 1 48%positive = true.
Proof. vm_compute. reflexivity. Qed.

Theorem w2_pos : forall k, 1 <= k < 49 -> 1 <= w2 k.
Proof. intros k Hk. apply Z.leb_le. exact (chkp_ok _ 48 1 w2_tab_pos k ltac:(lia)). Qed.

Theorem w2_zero : w2 0 = 0.
Proof. reflexivity. Qed.

Theorem w2_zero_beta : forall t k, 0 <= k < 49 -> w2 k = 0 -> beta2 t k = 0.
Proof.
  intros t k Hk Hw. destruct (Z.eq_dec k 0) as [->|N]; [apply beta2_zero|].
  pose proof (w2_pos k ltac:(lia)). lia.
Qed.

Theorem beta2_nonneg : forall t k, 0 <= beta2 t k.
Proof. intros t k. unfold beta2. lia. Qed.

Lemma zsumZ_le : forall f h l, (forall k, In k l -> f k <= h k) -> zsumZ f l <= zsumZ h l.
Proof.
  intros f h l H. induction l as [|x l IH]; [apply Z.le_refl|]. rewrite !zsumZ_cons.
  pose proof (H x (or_introl eq_refl)).
  assert (zsumZ f l <= zsumZ h l) by (apply IH; intros k Hk; apply H; right; exact Hk). lia.
Qed.

Lemma zsumZ_scale : forall c f l, zsumZ (fun k => c * f k) l = c * zsumZ f l.
Proof. intros c f l. induction l as [|x l IH]; [cbn; ring|]. rewrite !zsumZ_cons, IH. cbv beta. ring. Qed.

Theorem pack_reparse_scaled : forall sm x t (pw : Z -> Z) c, 0 <= c ->
  (forall k, 0 <= k < 49 -> pw k <= c * w2 k) -> json_read sm x = Some t ->
  zsumZ (fun k => pw k * beta2 t k) (YO0f.zseq 0 49) <= c * Z.of_nat (length x).
Proof.
  intros sm x t pw c Hc Hp H. pose proof (pack_reparse sm x t H) as B.
  apply Z.le_trans with (zsumZ (fun k => c * (w2 k * beta2 t k)) (YO0f.zseq 0 49)).
  - apply zsumZ_le. intros k Hk. apply YO0g.In_zseq in Hk.
    pose proof (beta2_nonneg t k). pose proof (Hp k ltac:(lia)).
    rewrite Z.mul_assoc. apply Z.mul_le_mono_nonneg_r; lia.
  - pose proof (zsumZ_scale c (fun k => w2 k * beta2 t k) (YO0f.zseq 0 49)) as S. cbv beta in S. rewrite S.
    apply Z.mul_le_mono_nonneg_l; assumption.
Qed.

Definition rpos (b a : nat) : Prop := b = a \/ exists E q, b = S E /\ a = S q /\ (E <= 3 * q)%nat.

Lemma rpos_refl : forall l, Forall2 rpos l l.
Proof. induction l as [|a l IH]; constructor; [left; reflexivity|exact IH]. Qed.

Definition ib (o : bool) (m : list Z * jv) : list nat := (if o then [S (elen (fst m))] else []) ++ rtsz (snd m).

Lemma flat_map_snd : forall L, flat_map rtsz (map snd L) = flat_map (ib false) L.
Proof. induction L as [|m L IH]; [reflexivity|]. cbn [map flat_map]. rewrite IH. reflexivity. Qed.

Lemma rtsz_mk : forall o L, rtsz (mk o L) = rkb o (rfcap (length L) 0 0) ++ flat_map (ib o) L.
Proof.
  intros [|] L; cbn [mk].
  - rewrite rtsz_obj. f_equal. apply flat_map_ext. intros [k u]. reflexivity.
  - rewrite rtsz_arr, length_map, flat_map_snd. reflexivity.
Qed.

Lemma grow_ok : forall o n cap ok cap1 tg ok1, grow o n cap ok = (Some cap1, tg, ok1) ->
  cap1 = gcap n cap /\ tg = grow_ev o n cap.
Proof.
  intros o n cap ok cap1 tg ok1 H. revert H. unfold grow, grow_ev, gcap.
  destruct (Nat.ltb n cap); intros H.
  - unfold jret in H. injection H as <- <- _. split; reflexivity.
  - unfold jbind, jrealloc, take, jret in H. cbv zeta in H.
    destruct ok as [|b ok]; [|destruct b]; cbv beta iota in H; [| |discriminate H].
    + destruct o; cbv beta iota in H; injection H as <- <- _; split; reflexivity.
    + destruct o; cbv beta iota in H; [destruct ok as [|b ok]; [|destruct b]; cbv beta iota in H; [| |discriminate H]|];
        injection H as <- <- _; split; reflexivity.
Qed.

Lemma name_blk : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  exists nb, (forall s, fold_left lsz_ev tn s = nb ++ s) /\ Forall2 rpos (if o then [S (elen nm)] else []) nb.
Proof.
  intros o y ok nm y1 tn ok2 H. destruct o.
  - destruct (jr_name_sl true y ok nm y1 tn ok2 H) as [_ Hq]. destruct (Hq eq_refl) as (q & -> & He).
    exists [S q]. split; [intros s; reflexivity|].
    constructor; [right; exists (elen nm), q; split; [reflexivity|split; [reflexivity|exact He]]|constructor].
  - pose proof (jr_name_spec false y ok) as Hs. rewrite H in Hs. cbv beta iota in Hs. destruct Hs as [-> _].
    exists []. split; [intros s; reflexivity|]. constructor.
Qed.

Lemma lit_blk : forall w v x ok t r tr ok', w <> [] -> lit w v x ok = (Some (t, r), tr, ok') -> t = v /\ tr = [].
Proof.
  intros w v x ok t r tr ok' Hw H. pose proof (lit_spec w v x ok Hw) as Hs. rewrite H in Hs. destruct Hs as [Ht _].
  split; [exact (proj1 (lit_tw w v x ok t r tr ok' Hw H))|exact Ht].
Qed.

Section Blocks.

Variable sm : list Z -> Z * Z.

Definition lspec_blk (f : nat) : Prop :=
  forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
    exists L B, t = mk o (rev acc ++ L) /\
      (forall s s0, Permutation s (rkb o cap ++ s0) ->
         Permutation (fold_left lsz_ev tr s) (rkb o (rfcap (length L) n cap) ++ B ++ s0)) /\
      Forall2 rpos (flat_map (ib o) L) B.

Definition vspec_blk (f : nat) : Prop :=
  forall d x ok t r tr ok', jrv sm f d x ok = (Some (t, r), tr, ok') ->
    exists A, (forall s, Permutation (fold_left lsz_ev tr s) (A ++ s)) /\ Forall2 rpos (rtsz t) A.

Lemma cont_blk : forall f d o b y ok t r tr ok', lspec_blk f ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (t, r), tr, ok') ->
  exists A, (forall s, Permutation (fold_left lsz_ev tr s) (A ++ s)) /\ Forall2 rpos (rtsz t) A.
Proof.
  intros f d o b y ok t r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H.
  assert (K : forall y' ok0, jrl sm f (S d) o 0 0 [] y' ok0 = (Some (t, r), tr, ok') ->
     exists A, (forall s, Permutation (fold_left lsz_ev tr s) (A ++ s)) /\ Forall2 rpos (rtsz t) A).
  { intros y' ok0 E. destruct (IHl _ _ _ _ _ _ _ _ _ _ _ E) as (L & B & -> & P & F).
    exists (rkb o (rfcap (length L) 0 0) ++ B). split.
    - intros s. rewrite <- app_assoc. apply P. apply Permutation_refl.
    - cbn [rev app]. rewrite rtsz_mk. apply Forall2_app; [apply rpos_refl|exact F]. }
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  - exact (K _ _ H).
  - destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as <- <- <- _. exists []. split; [intros s; apply Permutation_refl|].
      destruct o; cbn; constructor.
    + exact (K _ _ H).
Qed.

Lemma blk_fuel : forall f, vspec_blk f /\ lspec_blk f.
Proof.
  induction f as [|f [IHv IHl]].
  - split; [intros d x ok t r tr ok' H|intros d o n cap acc y ok t r tr ok' H];
      cbn [jrv jrl] in H; unfold jrefuse in H; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123); cbv beta iota in H; [exact (cont_blk f d true b y ok t r tr ok' IHl H)|].
      destruct (b =? 91); cbv beta iota in H; [exact (cont_blk f d false b y ok t r tr ok' IHl H)|].
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & Ht).
        destruct (jr_string_esc y ok s r1 t1 ok1 Hj) as (q & Ht1 & _ & _ & He).
        cbv beta iota in H. unfold jret in H. injection H as <- <- Ht2 _.
        exists [S q]. split.
        - intros s'. subst tr t1 t2. apply Permutation_refl.
        - constructor; [right; exists (elen s), q; split; [reflexivity|split; [reflexivity|exact He]]|constructor]. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (lit_blk w_true JTrue _ _ _ _ _ _ ltac:(unfold w_true; discriminate) H) as [-> ->].
        exists []. split; [intros s; apply Permutation_refl|constructor]. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (lit_blk w_false JFalse _ _ _ _ _ _ ltac:(unfold w_false; discriminate) H) as [-> ->].
        exists []. split; [intros s; apply Permutation_refl|constructor]. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (lit_blk w_null JNull _ _ _ _ _ _ ltac:(unfold w_null; discriminate) H) as [-> ->].
        exists []. split; [intros s; apply Permutation_refl|constructor]. }
      destruct (jr_number_txt sm (b :: y) ok t r tr ok' H) as (txt & bits & -> & -> & _).
      exists [S (length txt)]. split; [intros s; apply Permutation_refl|apply rpos_refl].
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & Eg & H & Ht2). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & Ht3). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & Ht4). cbv beta iota in H.
      destruct (grow_ok o n cap ok cap1 tg ok1 Eg) as [-> ->].
      destruct (name_blk o y ok1 nm y1 tn ok2 En) as (nb & Fn & Rn).
      destruct (IHv d y1 ok2 v r0 tv ok3 Ev) as (Av & Pv & Rv).
      assert (Pre : forall s s0, Permutation s (rkb o cap ++ s0) ->
                Permutation (fold_left lsz_ev tv (fold_left lsz_ev tn (fold_left lsz_ev (grow_ev o n cap) s)))
                  (rkb o (gcap n cap) ++ (nb ++ Av) ++ s0)).
      { intros s s0 Hs. rewrite Fn.
        eapply Permutation_trans; [apply Pv|].
        eapply Permutation_trans; [apply Permutation_app_head, Permutation_app_head, grow_perm, Hs|].
        rewrite (app_assoc Av nb). eapply Permutation_trans; [apply pswap|].
        apply Permutation_app_head, Permutation_app_tail, Permutation_app_comm. }
      assert (Ri : Forall2 rpos (ib o (nm, v)) (nb ++ Av)) by (unfold ib; cbn [fst snd]; apply Forall2_app; assumption).
      subst tr t2 t3.
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (c =? 44); cbv beta iota in H.
      { destruct (IHl d o (S n) (gcap n cap) ((nm, v) :: acc) r1 ok3 t r t4 ok' H) as (L & B & -> & P & F).
        exists ((nm, v) :: L), ((nb ++ Av) ++ B). split; [|split].
        - cbn [rev]. rewrite <- app_assoc. reflexivity.
        - intros s s0 Hs. rewrite !fold_left_app.
          eapply Permutation_trans; [apply P, Pre, Hs|].
          cbn [length rfcap]. apply Permutation_app_head. rewrite <- (app_assoc (nb ++ Av) B s0). apply pswap.
        - cbn [flat_map]. apply Forall2_app; [exact Ri|exact F]. }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as <- <- Ht _. subst t4.
      exists [(nm, v)], (nb ++ Av). split; [|split].
      * reflexivity.
      * intros s s0 Hs. rewrite !fold_left_app. cbn [fold_left].
        eapply Permutation_trans; [apply Pre, Hs|]. apply Permutation_refl.
      * cbn [flat_map]. rewrite app_nil_r. exact Ri.
Qed.

Theorem input_blocks : forall x t, json_read sm x = Some t ->
  exists A, Permutation (lsz (snd (jr_run sm x []))) A /\ Forall2 rpos (rtsz t) A.
Proof.
  intros x t H. rewrite jr_run_eq. cbn [snd].
  unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  cbn [fst snd]. unfold jr_value in E.
  destruct (proj1 (blk_fuel _) 0%nat x [] t' r tr ok' E) as (A & P & F).
  exists A. split; [|exact F]. unfold lsz. rewrite <- (app_nil_r A). apply P.
Qed.

Theorem input_render_blocks : forall x t, json_read sm x = Some t ->
  exists A B, Permutation (lsz (snd (jr_run sm x []))) A /\ Permutation (lsz (ttrace t)) B /\ Forall2 rpos B A.
Proof.
  intros x t H. destruct (input_blocks x t H) as (A & P & F).
  exists A, (rtsz t). split; [exact P|]. split; [apply lsz_ttrace|exact F].
Qed.

End Blocks.
