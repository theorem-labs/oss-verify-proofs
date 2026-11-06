From Stdlib Require Import ZArith List Bool Lia Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack AllocPackRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackFit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope Z_scope.

Ltac zb := repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
  | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
  end.

Fixpoint po_wl (h : nat -> Z) (l : list nat) : Z :=
  match l with
  | [] => 0
  | a :: r => h a + po_wl h r
  end.

Lemma po_wl_app h l1 l2 : po_wl h (l1 ++ l2) = po_wl h l1 + po_wl h l2.
Proof. induction l1 as [|a l1 IH]; cbn [app po_wl]; [ring | rewrite IH; ring]. Qed.

Lemma po_wl_perm h l l' : Permutation l l' -> po_wl h l = po_wl h l'.
Proof. induction 1; cbn [po_wl]; lia. Qed.

Lemma po_wl_zero l : po_wl (fun _ => 0) l = 0.
Proof. induction l as [|a l IH]; cbn [po_wl]; lia. Qed.

Fixpoint po_rs (t : jv) : list nat :=
  match t with
  | JNum txt _ => [S (length txt)]
  | JStr s => [S (length (flat_map ech s))]
  | JArr items => flat_map po_rs items
  | JObj ms => flat_map (fun '(k, u) => S (length (flat_map ech k)) :: po_rs u) ms
  | _ => []
  end.

Fixpoint po_cap (n : nat) : nat :=
  match n with
  | O => O
  | S m => gcap m (po_cap m)
  end.

Definition po_cb (o : bool) (n : nat) : list nat :=
  match n with
  | O => []
  | S _ => (if o then [8 * po_cap n] else []) ++ [56 * po_cap n]
  end%nat.

Definition po_ext (tr : list ev) (b : list nat) : Prop :=
  forall s, Permutation (fold_left ReaderRes.lsz_ev tr (b ++ s)) (fold_left ReaderRes.lsz_ev tr b ++ s).

Lemma po_rm_perm k s s' : Permutation s s' -> Permutation (ReaderRes.rm1n k s) (ReaderRes.rm1n k s').
Proof.
  induction 1 as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [ReaderRes.rm1n].
  - constructor.
  - destruct (Nat.eqb x k); [exact H | constructor; exact IH].
  - destruct (Nat.eqb_spec y k), (Nat.eqb_spec x k); subst; try apply Permutation_refl. apply perm_swap.
  - eapply perm_trans; eassumption.
Qed.

Lemma po_lsz_perm s s' e : Permutation s s' -> Permutation (ReaderRes.lsz_ev s e) (ReaderRes.lsz_ev s' e).
Proof.
  intros H. destruct e as [n|[|m] n|n|n]; cbn [ReaderRes.lsz_ev].
  - constructor. exact H.
  - constructor. exact H.
  - constructor. apply po_rm_perm, H.
  - exact H.
  - apply po_rm_perm, H.
Qed.

Lemma po_fold_perm tr : forall s s', Permutation s s' ->
  Permutation (fold_left ReaderRes.lsz_ev tr s) (fold_left ReaderRes.lsz_ev tr s').
Proof.
  induction tr as [|e tr IH]; intros s s' H; cbn [fold_left]; [exact H|]. apply IH, po_lsz_perm, H.
Qed.

Lemma po_ext_of tr b R : (forall s, Permutation (fold_left ReaderRes.lsz_ev tr (b ++ s)) (R ++ s)) ->
  po_ext tr b /\ Permutation (fold_left ReaderRes.lsz_ev tr b) R.
Proof.
  intros H. assert (E : Permutation (fold_left ReaderRes.lsz_ev tr b) R).
  { pose proof (H []) as H0. rewrite !app_nil_r in H0. exact H0. }
  split; [|exact E]. intros s. eapply perm_trans; [apply H|]. apply Permutation_app_tail. symmetry. exact E.
Qed.

Lemma po_perm3 (A B C s : list nat) : Permutation (A ++ B ++ C ++ s) (C ++ A ++ B ++ s).
Proof.
  pose proof (Permutation_app_swap_app (A ++ B) C s) as P. rewrite <- !app_assoc in P. exact P.
Qed.

Lemma po_lsz_grow s m n : m <> 0%nat -> ReaderRes.lsz_ev s (EGrow m n) = n :: ReaderRes.rm1n m s.
Proof. intros H. destruct m as [|m]; [contradiction | reflexivity]. Qed.

Lemma po_rm_hd k l : ReaderRes.rm1n k (k :: l) = l.
Proof. cbn [ReaderRes.rm1n]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma po_rm_ne k x l : x <> k -> ReaderRes.rm1n k (x :: l) = x :: ReaderRes.rm1n k l.
Proof. intros H. cbn [ReaderRes.rm1n]. rewrite (proj2 (Nat.eqb_neq x k) H). reflexivity. Qed.

Lemma po_cap_form : forall n, (1 <= n)%nat ->
  exists j, po_cap n = (8 * 2 ^ j)%nat /\ (n <= po_cap n)%nat /\ (j = 0%nat \/ (4 * 2 ^ j < n)%nat).
Proof.
  induction n as [|n IH]; intros Hn; [lia|].
  destruct n as [|n'].
  - exists 0%nat. cbn. split; [reflexivity|]. split; [lia|]. left. reflexivity.
  - destruct (IH ltac:(lia)) as (j & Hc & Hle & Hj).
    change (po_cap (S (S n'))) with (gcap (S n') (po_cap (S n'))). unfold gcap. rewrite Hc. rewrite Hc in Hle.
    assert (Hp : (1 <= 2 ^ j)%nat) by (pose proof (Nat.pow_nonzero 2 j ltac:(lia)); lia).
    destruct (Nat.ltb (S n') (8 * 2 ^ j)) eqn:E; zb.
    + exists j. split; [reflexivity|]. split; [lia|]. destruct Hj as [Hj|Hj]; [left; exact Hj | right; lia].
    + destruct (Nat.eqb (8 * 2 ^ j) 0) eqn:E0; zb; [lia|].
      exists (S j). rewrite Nat.pow_succ_r'. split; [lia|]. split; lia.
Qed.

Lemma po_cap8 n : (1 <= n)%nat -> (8 <= po_cap n)%nat.
Proof.
  intros H. destruct (po_cap_form n H) as (j & Hc & _). rewrite Hc.
  pose proof (Nat.pow_nonzero 2 j ltac:(lia)). lia.
Qed.

Lemma po_grow_cb o n s :
  fold_left ReaderRes.lsz_ev (grow_ev o n (po_cap n)) (po_cb o n ++ s) = po_cb o (S n) ++ s.
Proof.
  destruct n as [|m]; [destruct o; reflexivity|].
  pose proof (po_cap8 (S m) ltac:(lia)) as H8.
  cbn [po_cb]. unfold grow_ev.
  change (po_cap (S (S m))) with (gcap (S m) (po_cap (S m))).
  unfold gcap. set (C := po_cap (S m)) in *.
  destruct (Nat.ltb (S m) C) eqn:E; [reflexivity|].
  destruct (Nat.eqb C 0) eqn:E0; [zb; lia|].
  destruct o; cbn [fold_left app].
  - rewrite (po_lsz_grow ((8 * C)%nat :: (56 * C)%nat :: s) (56 * C)%nat) by lia.
    rewrite (po_rm_ne (56 * C)%nat (8 * C)%nat) by lia. rewrite po_rm_hd.
    rewrite po_lsz_grow by lia.
    rewrite (po_rm_ne (8 * C)%nat (56 * (2 * C))%nat) by lia. rewrite po_rm_hd. reflexivity.
  - rewrite po_lsz_grow by lia. rewrite po_rm_hd. reflexivity.
Qed.

Lemma po_grow : forall o n cap ok cap1 tg ok1, grow o n cap ok = (Some cap1, tg, ok1) ->
  cap1 = gcap n cap /\ tg = grow_ev o n cap.
Proof.
  intros o n cap ok cap1 tg ok1 H. unfold grow in H. unfold grow_ev, gcap.
  destruct (Nat.ltb n cap).
  - unfold jret in H. injection H as <- <- _. split; reflexivity.
  - unfold jbind, jrealloc, take, jret in H. cbv zeta in H.
    destruct ok as [|[|] ok]; cbv beta iota in H; [| |discriminate];
      destruct o; cbv beta iota in H; try (destruct ok as [|[|] ok]; cbv beta iota in H);
      try discriminate; injection H as <- <- _; split; reflexivity.
Qed.

Lemma po_ech_len c : (length (ech c) <= 6)%nat.
Proof.
  unfold ech, esc. destruct (special c); [|cbn; lia].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; lia.
Qed.

Lemma po_fm_len l : (length (flat_map ech l) <= 6 * length l)%nat.
Proof.
  induction l as [|a l IH]; cbn [flat_map length]; [lia|]. rewrite length_app. pose proof (po_ech_len a). lia.
Qed.

Lemma po_fm_app l1 l2 : length (flat_map ech (l1 ++ l2)) = (length (flat_map ech l1) + length (flat_map ech l2))%nat.
Proof. rewrite flat_map_app, length_app. reflexivity. Qed.

Lemma po_utf8_len cp : (length (utf8 cp) <= 4)%nat /\ (cp < 65536 -> (length (utf8 cp) <= 3)%nat).
Proof.
  unfold utf8. destruct (cp <? 128); [cbn; lia|]. destruct (cp <? 2048); [cbn; lia|].
  destruct (cp <? 65536) eqn:E3; [cbn; lia|]. zb. cbn. split; [lia|]. intros H. lia.
Qed.

Lemma po_hexval b v : hexval b = Some v -> 0 <= v < 16.
Proof.
  unfold hexval.
  destruct ((48 <=? b) && (b <=? 57)) eqn:E1; [intros H; injection H as <-; zb; lia|].
  destruct ((97 <=? b) && (b <=? 102)) eqn:E2; [intros H; injection H as <-; zb; lia|].
  destruct ((65 <=? b) && (b <=? 70)) eqn:E3; [intros H; injection H as <-; zb; lia|].
  discriminate.
Qed.

Lemma po_hex4 l cp : hex4 l = Some cp -> 0 <= cp < 65536.
Proof.
  unfold hex4. destruct l as [|h0 [|h1 [|h2 [|h3 r]]]]; try discriminate.
  destruct (hexval h0) as [v0|] eqn:E0; [|discriminate].
  destruct (hexval h1) as [v1|] eqn:E1; [|discriminate].
  destruct (hexval h2) as [v2|] eqn:E2; [|discriminate].
  destruct (hexval h3) as [v3|] eqn:E3; [|discriminate].
  intros H. injection H as <-.
  apply po_hexval in E0, E1, E2, E3. lia.
Qed.

Lemma po_dec3 : forall n y s r, (length y <= n)%nat -> decode y = Some (s, r) ->
  (length (flat_map ech s) + 3 * length r + 3 <= 3 * length y)%nat.
Proof.
  induction n as [|n IH]; intros y s r Hn H; (destruct y as [|b y0]; [discriminate|]).
  - cbn [length] in Hn. lia.
  - cbn [length] in Hn |- *. cbn [decode] in H.
    destruct (b =? 34) eqn:E34; cbv beta iota in H.
    + injection H as <- <-. cbn. lia.
    + destruct (b <? 32) eqn:E32; cbv beta iota in H; [discriminate|].
      destruct (negb (b =? 92)) eqn:E92; cbv beta iota in H.
      * apply emit_inv in H as (s1 & H & ->). pose proof (IH y0 s1 r ltac:(lia) H) as B.
        assert (Hs : special b = false).
        { unfold special. apply negb_true_iff in E92. rewrite E34, E92, E32. reflexivity. }
        rewrite po_fm_app. cbn [flat_map]. unfold ech at 1. rewrite Hs. cbn [length app]. lia.
      * destruct y0 as [|e r2]; cbv beta iota in H; [discriminate|].
        cbn [length] in Hn.
        destruct (e =? 117); cbv beta iota in H.
        -- destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; cbv beta iota in H; try discriminate.
           destruct (hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Eh; cbv beta iota in H; [|discriminate].
           pose proof (po_hex4 _ _ Eh) as Hcp.
           destruct (cp =? 0); cbv beta iota in H; [discriminate|].
           destruct ((55296 <=? cp) && (cp <? 56320)); cbv beta iota in H.
           ++ destruct r3 as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 r4]]]]]]; cbv beta iota in H; try discriminate.
              destruct (low (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: r4)) as [lo|]; cbv beta iota in H; [|discriminate].
              apply emit_inv in H as (s1 & H & ->). cbn [length] in Hn.
              pose proof (IH r4 s1 r ltac:(lia) H) as B.
              rewrite po_fm_app. pose proof (po_fm_len (utf8 (pair_cp cp lo))).
              pose proof (proj1 (po_utf8_len (pair_cp cp lo))). cbn [length]. lia.
           ++ destruct ((56320 <=? cp) && (cp <? 57344)); cbv beta iota in H; [discriminate|].
              apply emit_inv in H as (s1 & H & ->). cbn [length] in Hn.
              pose proof (IH r3 s1 r ltac:(lia) H) as B.
              rewrite po_fm_app. pose proof (po_fm_len (utf8 cp)).
              pose proof (proj2 (po_utf8_len cp) ltac:(lia)). cbn [length]. lia.
        -- destruct (escape e) as [c0|]; cbv beta iota in H; [|discriminate].
           apply emit_inv in H as (s1 & H & ->).
           pose proof (IH r2 s1 r ltac:(lia) H) as B.
           rewrite po_fm_app. pose proof (po_fm_len [c0]). cbn [length] in *. lia.
Qed.

Lemma po_str : forall y ok s r t ok', jr_string y ok = (Some (s, r), t, ok') ->
  exists q, t = [EAlloc (S q)] /\ (length r + S q = length y)%nat /\ (length (flat_map ech s) <= 3 * q)%nat.
Proof.
  intros y ok s r t ok' H. pose proof (jr_string_spec y ok) as S. rewrite H in S.
  destruct S as (q & _ & Hd & Ht & Hl). exists q. split; [exact Ht|]. split; [exact Hl|].
  pose proof (po_dec3 (length y) y s r (le_n _) Hd). lia.
Qed.

Lemma po_name : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  (o = true /\ exists q, tn = [EAlloc (S q)] /\ (length y1 + q + 3 <= length y)%nat /\
     (length (flat_map ech nm) <= 3 * q)%nat) \/
  (o = false /\ tn = [] /\ y1 = y).
Proof.
  intros o y ok nm y1 tn ok2 H. destruct o.
  - left. split; [reflexivity|]. unfold jr_name in H. pose proof (skip_len y) as Hy.
    destruct (skip y) as [|b z] eqn:Ey; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
    cbn [length] in Hy.
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([s r] & t1 & ok1 & t2 & Hj & H & Et).
    apply po_str in Hj as (q & -> & Hl & He). cbv beta iota in H.
    pose proof (skip_len r) as Hr.
    destruct (skip r) as [|c r1]; cbv beta iota in H.
    + apply jbind_some in H as (? & ? & ? & ? & ? & H & ?). unfold jrefuse in H. discriminate.
    + cbn [length] in Hr.
      destruct (c =? 58); cbv beta iota in H.
      * unfold jret in H. injection H as <- <- <- _. exists q. rewrite app_nil_r in Et.
        split; [exact Et|]. split; lia.
      * apply jbind_some in H as (? & ? & ? & ? & ? & H & ?). unfold jrefuse in H. discriminate.
  - right. unfold jr_name, jret in H. injection H as <- <- <- _. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma po_lit : forall w v x ok u r tr ok', w <> [] -> lit w v x ok = (Some (u, r), tr, ok') ->
  u = v /\ tr = [] /\ (length r < length x)%nat.
Proof.
  intros w v x ok u r tr ok' Hw H. pose proof (lit_spec w v x ok Hw) as S. rewrite H in S.
  destruct S as [Ht Hr]. split; [|split; [exact Ht | exact Hr]].
  unfold lit in H. destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as <- _ _ _. reflexivity.
Qed.

Lemma po_bind_none : forall A B (m : M A) (k : A -> M B) ok t ok', jbind m k ok = (None, t, ok') ->
  m ok = (None, t, ok') \/ exists a t1 ok1 t2, m ok = (Some a, t1, ok1) /\ k a ok1 = (None, t2, ok') /\ t = t1 ++ t2.
Proof.
  intros A B m k ok t ok' H. unfold jbind in H.
  destruct (m ok) as [[[a|] t1] ok1].
  - destruct (k a ok1) as [[r t2] ok2] eqn:E. injection H as Hr Ht Ho. subst r t ok2.
    right. exists a, t1, ok1, t2. split; [reflexivity|]. split; [exact E | reflexivity].
  - injection H as Ht Ho. subst t ok1. left. reflexivity.
Qed.

Lemma po_id_ext tr b : (forall l, fold_left ReaderRes.lsz_ev tr l = l) -> po_ext tr b.
Proof. intros H s. rewrite !H. apply Permutation_refl. Qed.

Lemma po_str_none : forall y ok t ok', jr_string y ok = (None, t, ok') ->
  forall l, fold_left ReaderRes.lsz_ev t l = l.
Proof.
  intros y ok t ok' H l. unfold jr_string in H. destruct (scan y) as [q|].
  - unfold jbind, jalloc, take, jret, jfree, jrefuse in H.
    destruct ok as [|[|] ok]; [| |injection H as <- _; reflexivity];
      (destruct (decode y) as [[s r]|]; cbv beta iota in H; [discriminate|]);
      injection H as <- _; cbn [app fold_left ReaderRes.lsz_ev]; apply po_rm_hd.
  - unfold jrefuse in H. injection H as <- _. reflexivity.
Qed.

Lemma po_name_none : forall o y ok t ok', jr_name o y ok = (None, t, ok') ->
  forall l, fold_left ReaderRes.lsz_ev t l = l.
Proof.
  intros o y ok t ok' H l. destruct o; [|unfold jr_name, jret in H; discriminate].
  unfold jr_name in H. destruct (skip y) as [|b z]; [unfold jrefuse in H; injection H as <- _; reflexivity|].
  destruct (b =? 34); [|unfold jrefuse in H; injection H as <- _; reflexivity].
  apply po_bind_none in H as [H | ([nm r] & t1 & ok1 & t2 & Hs & H & ->)].
  - exact (po_str_none z ok t ok' H l).
  - pose proof (jr_string_spec z ok) as S. rewrite Hs in S. destruct S as (q & Hq & _ & -> & _).
    assert (Hb : sblock z = S q) by (unfold sblock; rewrite Hq; reflexivity).
    cbv beta iota in H. rewrite Hb in H.
    destruct (skip r) as [|c1 r1]; [|destruct (c1 =? 58)];
      unfold jbind, jfree, jret, jrefuse in H; cbv beta iota in H; try discriminate;
      injection H as <- _; cbn [app fold_left ReaderRes.lsz_ev]; apply po_rm_hd.
Qed.

Lemma po_lit_none : forall w v x ok t ok', lit w v x ok = (None, t, ok') -> t = [].
Proof.
  intros w v x ok t ok' H. unfold lit in H. destruct (prefixb w x); [unfold jret in H; discriminate|].
  unfold jrefuse in H. injection H as <- _. reflexivity.
Qed.

Lemma po_grow_none : forall o n cap ok tg ok', grow o n cap ok = (None, tg, ok') ->
  tg = [EFail (56 * gcap n cap)] \/ (o = true /\ tg = [EGrow (56 * cap) (56 * gcap n cap); EFail (8 * gcap n cap)]).
Proof.
  intros o n cap ok tg ok' H. unfold grow in H. unfold gcap.
  destruct (Nat.ltb n cap); [unfold jret in H; discriminate|].
  unfold jbind, jrealloc, take, jret in H. cbv zeta in H.
  destruct ok as [|[|] ok]; cbv beta iota in H; [| |injection H as <- _; left; reflexivity];
    destruct o; cbv beta iota in H; try discriminate;
    destruct ok as [|[|] ok]; cbv beta iota in H; try discriminate;
    injection H as <- _; right; split; reflexivity.
Qed.

Lemma po_wl_nonneg h l : (forall s, 0 <= h s) -> 0 <= po_wl h l.
Proof. intros H. induction l as [|a l IH]; cbn [po_wl]; [lia|]. pose proof (H a). lia. Qed.

Definition po_ok (f g : nat -> Z) (c : Z) : Prop :=
  (forall s, 0 <= f s) /\ (forall s, 0 <= g s) /\ 0 <= c /\
  (forall q e, (e <= 3 * q)%nat -> f (S q) + g (S e) <= c * (Z.of_nat q + 2)) /\
  (forall L, (1 <= L)%nat -> f (S L) + g (S L) <= c * Z.of_nat L) /\
  (forall N, (1 <= N)%nat -> f (56 * po_cap N)%nat <= c * (Z.of_nat N + 1) /\
     f (56 * po_cap N)%nat + f (8 * po_cap N)%nat <= c * (2 * Z.of_nat N + 1) /\ f (8 * po_cap N)%nat <= c * Z.of_nat N).

Section Own.

Variable sm : list Z -> Z * Z.
Variables (f g : nat -> Z) (c : Z).
Hypothesis HW : po_ok f g c.

Lemma po_c0 : 0 <= c.
Proof. exact (proj1 (proj2 (proj2 HW))). Qed.

Lemma po_hs q e : (e <= 3 * q)%nat -> f (S q) + g (S e) <= c * (Z.of_nat q + 2).
Proof. exact (proj1 (proj2 (proj2 (proj2 HW))) q e). Qed.

Lemma po_hn L : (1 <= L)%nat -> f (S L) + g (S L) <= c * Z.of_nat L.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HW)))) L). Qed.

Lemma po_hc N : (1 <= N)%nat -> f (56 * po_cap N)%nat <= c * (Z.of_nat N + 1) /\
  f (56 * po_cap N)%nat + f (8 * po_cap N)%nat <= c * (2 * Z.of_nat N + 1) /\ f (8 * po_cap N)%nat <= c * Z.of_nat N.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 HW)))) N). Qed.

Lemma po_f0 s : 0 <= f s.
Proof. exact (proj1 HW s). Qed.

Lemma po_g0 s : 0 <= g s.
Proof. exact (proj1 (proj2 HW) s). Qed.

Lemma po_cm a b : a <= b -> c * a <= c * b.
Proof. intros H. apply Z.mul_le_mono_nonneg_l; [exact po_c0 | exact H]. Qed.

Definition po_iw (o : bool) (m : list Z * jv) : Z :=
  (if o then g (S (length (flat_map ech (fst m)))) else 0) + po_wl g (po_rs (snd m)).

Fixpoint po_accw (o : bool) (L : list (list Z * jv)) : Z :=
  match L with
  | [] => 0
  | m :: L' => po_iw o m + po_accw o L'
  end.

Lemma po_accw_app o l1 l2 : po_accw o (l1 ++ l2) = po_accw o l1 + po_accw o l2.
Proof. induction l1 as [|m l1 IH]; cbn [app po_accw]; [ring | rewrite IH; ring]. Qed.

Lemma po_accw_rev o L : po_accw o (rev L) = po_accw o L.
Proof. induction L as [|m L IH]; [reflexivity|]. cbn [rev po_accw]. rewrite po_accw_app, IH. cbn [po_accw]. ring. Qed.

Lemma po_rs_mk o L : po_wl g (po_rs (mk o L)) = po_accw o L.
Proof.
  destruct o; unfold mk; cbn [po_rs]; induction L as [|[k u] L IH]; cbn [flat_map map po_accw po_wl app]; try reflexivity;
    rewrite ?po_wl_app, IH; unfold po_iw; cbn [fst snd po_wl]; ring.
Qed.

Lemma po_cb_w o N : (1 <= N)%nat -> po_wl f (po_cb o N) <= c * (Z.of_nat N + 1 + (if o then Z.of_nat N else 0)).
Proof.
  intros HN. destruct N as [|m]; [lia|]. destruct (po_hc (S m) HN) as (A & B & _).
  destruct o; cbn [po_cb app po_wl]; lia.
Qed.

Lemma po_name_w o y ok nm y1 tn ok2 : jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  exists N, (forall l, fold_left ReaderRes.lsz_ev tn l = N ++ l) /\
    po_wl f N + (if o then g (S (length (flat_map ech nm))) else 0) <=
      c * (Z.of_nat (length y) - Z.of_nat (length y1) - (if o then 1 else 0)).
Proof.
  intros H. destruct (po_name o y ok nm y1 tn ok2 H) as [(-> & q & -> & Hl & He) | (-> & -> & ->)].
  - exists [S q]. split; [intros l; reflexivity|]. cbn [po_wl]. pose proof (po_hs q _ He) as S.
    assert (M := po_cm (Z.of_nat q + 2) (Z.of_nat (length y) - Z.of_nat (length y1) - 1) ltac:(lia)). lia.
  - exists []. split; [intros l; reflexivity|]. cbn [po_wl].
    replace (Z.of_nat (length y) - Z.of_nat (length y) - 0) with 0 by lia. rewrite Z.mul_0_r. lia.
Qed.

Lemma po_num : forall x ok u r tr ok', x <> [] -> jr_number sm x ok = (Some (u, r), tr, ok') ->
  exists txt bits, u = JNum txt bits /\ tr = [EAlloc (S (length txt))] /\ (1 <= length txt)%nat /\
    (length txt + length r = length x)%nat.
Proof.
  intros x ok u r tr ok' Hx H. unfold jr_number in H.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) in H.
  assert (Hj : (j <= length x)%nat).
  { unfold j. destruct x as [|b x']; [contradiction|]. destruct (b =? 45); cbn [length]; lia. }
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c0 z] eqn:Ez; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c0)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c0 =? 48) && match z with c1 :: _ => digit c1 | [] => false end); cbv beta iota in H;
    [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:Es. cbv beta iota in H.
  pose proof (span_app _ _ _ _ Es) as Hz.
  assert (Ht : (length (firstn j x ++ c0 :: a) + length r' = length x)%nat).
  { rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk. rewrite Hz, length_app in Hsk. lia. }
  assert (Ht1 : (1 <= length (firstn j x ++ c0 :: a))%nat) by (rewrite length_app; cbn [length]; lia).
  unfold jbind, jalloc, take in H.
  destruct ok as [|[|] ok]; cbv beta iota in H; [| |discriminate];
    (destruct (whole sm (firstn j x ++ c0 :: a)); unfold jret, jrefuse in H; [|discriminate];
     injection H as <- <- <- _; eexists; eexists; split; [reflexivity|]; split; [reflexivity|]; split; [exact Ht1 | exact Ht]).
Qed.

Lemma po_num_none : forall x ok tr ok', jr_number sm x ok = (None, tr, ok') ->
  (forall l, fold_left ReaderRes.lsz_ev tr l = l) \/
  exists L, (1 <= L <= length x)%nat /\ forall l, fold_left ReaderRes.lsz_ev tr l = S L :: l.
Proof.
  intros x ok tr ok' H. unfold jr_number in H.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) in H.
  pose proof (length_skipn j x) as Hsk.
  destruct (skipn j x) as [|c0 z] eqn:Ez; cbv beta iota in H;
    [unfold jrefuse in H; injection H as <- _; left; intros l; reflexivity|].
  destruct (negb (digit c0)); cbv beta iota in H; [unfold jrefuse in H; injection H as <- _; left; intros l; reflexivity|].
  destruct ((c0 =? 48) && match z with c1 :: _ => digit c1 | [] => false end); cbv beta iota in H;
    [unfold jrefuse in H; injection H as <- _; left; intros l; reflexivity|].
  destruct (span numch z) as [a r'] eqn:Es. cbv beta iota in H.
  pose proof (span_app _ _ _ _ Es) as Hz.
  assert (Ht : (length (firstn j x ++ c0 :: a) + length r' = length x)%nat).
  { rewrite length_app, length_firstn. cbn [length]. cbn [length] in Hsk. rewrite Hz, length_app in Hsk. lia. }
  assert (Ht1 : (1 <= length (firstn j x ++ c0 :: a))%nat) by (rewrite length_app; cbn [length]; lia).
  unfold jbind, jalloc, take in H.
  destruct ok as [|[|] ok]; cbv beta iota in H;
    [| |injection H as <- _; left; intros l; reflexivity];
    (destruct (whole sm (firstn j x ++ c0 :: a)); unfold jret, jrefuse in H; [discriminate|];
     injection H as <- _; right; exists (length (firstn j x ++ c0 :: a)); split; [lia | intros l; reflexivity]).
Qed.

Definition po_V (k : nat) : Prop := forall d x ok t r tr ok', jrv sm k d x ok = (Some (t, r), tr, ok') ->
  po_ext tr [] /\
  po_wl f (fold_left ReaderRes.lsz_ev tr []) + po_wl g (po_rs t) <= c * (Z.of_nat (length x) - Z.of_nat (length r)).

Definition po_L (k : nat) : Prop := forall d o n acc y ok t r tr ok',
  jrl sm k d o n (po_cap n) acc y ok = (Some (t, r), tr, ok') ->
  po_ext tr (po_cb o n) /\
  po_wl f (fold_left ReaderRes.lsz_ev tr (po_cb o n)) + po_wl g (po_rs t) <=
    c * (Z.of_nat (length y) - Z.of_nat (length r) + 1 + Z.of_nat n + (if o then Z.of_nat n else 0)) + po_accw o acc.

Lemma po_cont k d o b y ok t r tr ok' : po_L k ->
  jr_cont (jrl sm k) d o (b :: y) ok = (Some (t, r), tr, ok') ->
  po_ext tr [] /\
  po_wl f (fold_left ReaderRes.lsz_ev tr []) + po_wl g (po_rs t) <=
    c * (Z.of_nat (length (b :: y)) - Z.of_nat (length r)).
Proof.
  intros IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H. pose proof (skip_len y) as Hy. cbn [length].
  destruct (skip y) as [|c0 r0] eqn:Ey; cbv beta iota in H.
  - destruct (IHl (S d) o 0%nat [] [] ok t r tr ok' H) as [E B]. split; [exact E|].
    change (po_cb o 0) with (@nil nat) in B. cbn [po_accw length] in B.
    destruct o;
      (assert (M := po_cm (Z.of_nat 0 - Z.of_nat (length r) + 1 + Z.of_nat 0 + Z.of_nat 0)
                          (Z.of_nat (S (length y)) - Z.of_nat (length r)) ltac:(lia)); lia).
  - cbn [length] in Hy. destruct (c0 =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as <- <- <- _. split.
      * intros s. cbn. apply Permutation_refl.
      * assert (Z0 : po_wl g (po_rs (mk o [])) = 0) by (destruct o; reflexivity).
        cbn [fold_left po_wl]. rewrite Z0.
        assert (M := po_cm 0 (Z.of_nat (S (length y)) - Z.of_nat (length r0)) ltac:(lia)). lia.
    + destruct (IHl (S d) o 0%nat [] (c0 :: r0) ok t r tr ok' H) as [E B]. split; [exact E|].
      change (po_cb o 0) with (@nil nat) in B. cbn [po_accw length] in B.
      destruct o;
        (assert (M := po_cm (Z.of_nat (S (length r0)) - Z.of_nat (length r) + 1 + Z.of_nat 0 + Z.of_nat 0)
                            (Z.of_nat (S (length y)) - Z.of_nat (length r)) ltac:(lia)); lia).
Qed.

Lemma po_fuel : forall k, po_V k /\ po_L k.
Proof.
  induction k as [|k [IHv IHl]].
  - split; [intros d x ok t r tr ok' H | intros d o n acc y ok t r tr ok' H];
      cbn [jrv jrl] in H; unfold jrefuse in H; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsx.
      destruct (b =? 123); cbv beta iota in H.
      { destruct (po_cont k d true b y ok t r tr ok' IHl H) as [E B]. split; [exact E|].
        assert (M := po_cm (Z.of_nat (length (b :: y)) - Z.of_nat (length r)) (Z.of_nat (length x) - Z.of_nat (length r))
                          ltac:(cbn [length]; lia)). lia. }
      destruct (b =? 91); cbv beta iota in H.
      { destruct (po_cont k d false b y ok t r tr ok' IHl H) as [E B]. split; [exact E|].
        assert (M := po_cm (Z.of_nat (length (b :: y)) - Z.of_nat (length r)) (Z.of_nat (length x) - Z.of_nat (length r))
                          ltac:(cbn [length]; lia)). lia. }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & Et).
        apply po_str in Hj as (q & -> & Hl & He). cbv beta iota in H. unfold jret in H. injection H as <- <- <- _.
        subst tr. split.
        - intros s'. cbn. apply Permutation_refl.
        - cbn [fold_left app ReaderRes.lsz_ev po_wl po_rs]. pose proof (po_hs q _ He) as S.
          assert (M := po_cm (Z.of_nat q + 2) (Z.of_nat (length x) - Z.of_nat (length r1)) ltac:(lia)). lia. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (po_lit w_true JTrue (b :: y) ok t r tr ok' ltac:(unfold w_true; discriminate) H) as (-> & -> & Hr).
        split; [intros s'; cbn; apply Permutation_refl|]. cbn [fold_left po_wl po_rs].
        assert (M := po_cm 0 (Z.of_nat (length x) - Z.of_nat (length r)) ltac:(cbn [length] in Hr; lia)). lia. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (po_lit w_false JFalse (b :: y) ok t r tr ok' ltac:(unfold w_false; discriminate) H) as (-> & -> & Hr).
        split; [intros s'; cbn; apply Permutation_refl|]. cbn [fold_left po_wl po_rs].
        assert (M := po_cm 0 (Z.of_nat (length x) - Z.of_nat (length r)) ltac:(cbn [length] in Hr; lia)). lia. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (po_lit w_null JNull (b :: y) ok t r tr ok' ltac:(unfold w_null; discriminate) H) as (-> & -> & Hr).
        split; [intros s'; cbn; apply Permutation_refl|]. cbn [fold_left po_wl po_rs].
        assert (M := po_cm 0 (Z.of_nat (length x) - Z.of_nat (length r)) ltac:(cbn [length] in Hr; lia)). lia. }
      destruct (po_num (b :: y) ok t r tr ok' ltac:(discriminate) H) as (txt & bits & -> & -> & H1 & H2).
      split; [intros s'; cbn; apply Permutation_refl|]. cbn [fold_left ReaderRes.lsz_ev po_wl po_rs].
      pose proof (po_hn (length txt) H1) as S.
      assert (M := po_cm (Z.of_nat (length txt)) (Z.of_nat (length x) - Z.of_nat (length r))
                        ltac:(cbn [length] in H2; lia)). lia.
    + intros d o n acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & Eg & H & Etr). apply po_grow in Eg as [Ec Etg].
      cbv beta in H. subst cap1.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & Et2). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & Et3). cbv beta iota in H.
      destruct (po_name_w o y ok1 nm y1 tn ok2 En) as (N & HN & WN).
      destruct (IHv d y1 ok2 v r0 tv ok3 Ev) as [EV WV].
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c1 r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      assert (M := po_cm (Z.of_nat (length r1) + 1 - Z.of_nat (length r0)) 0 ltac:(lia)).
      destruct (c1 =? 44); cbv beta iota in H.
      * destruct (IHl d o (S n) ((nm, v) :: acc) r1 ok3 t r t4 ok' H) as [EL WL].
        assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tr (po_cb o n ++ s))
                       ((fold_left ReaderRes.lsz_ev t4 (po_cb o (S n)) ++ fold_left ReaderRes.lsz_ev tv [] ++ N) ++ s)).
        { intros s. subst tr t2 t3. rewrite !fold_left_app, Etg, po_grow_cb, HN.
          pose proof (EV (N ++ po_cb o (S n) ++ s)) as E1. cbn [app] in E1.
          eapply perm_trans; [apply po_fold_perm, E1|].
          eapply perm_trans; [apply po_fold_perm, (po_perm3 (fold_left ReaderRes.lsz_ev tv []) N (po_cb o (S n)) s)|].
          eapply perm_trans; [apply (EL (fold_left ReaderRes.lsz_ev tv [] ++ N ++ s))|].
          rewrite <- !app_assoc. apply Permutation_refl. }
        destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
        rewrite (po_wl_perm f _ _ Pm), !po_wl_app.
        cbn [po_accw] in WL. unfold po_iw in WL. cbn [fst snd] in WL. rewrite Nat2Z.inj_succ in WL.
        destruct o; lia.
      * destruct (c1 =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
        unfold jret in H. injection H as <- <- <- _.
        assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tr (po_cb o n ++ s))
                       ((fold_left ReaderRes.lsz_ev tv [] ++ N ++ po_cb o (S n)) ++ s)).
        { intros s. subst tr t2 t3. rewrite !fold_left_app, Etg, po_grow_cb, HN. cbn [fold_left].
          pose proof (EV (N ++ po_cb o (S n) ++ s)) as E1. cbn [app] in E1.
          eapply perm_trans; [exact E1|]. rewrite <- !app_assoc. apply Permutation_refl. }
        destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
        rewrite (po_wl_perm f _ _ Pm), !po_wl_app, po_rs_mk.
        assert (AR : forall L, po_accw o (L ++ [(nm, v)]) = po_accw o L + po_iw o (nm, v))
          by (intros L; rewrite po_accw_app; cbn [po_accw]; ring).
        cbn [rev]. rewrite AR, po_accw_rev. unfold po_iw. cbn [fst snd].
        pose proof (po_cb_w o (S n) ltac:(lia)) as WC. rewrite Nat2Z.inj_succ in WC.
        destruct o; lia.
Qed.

Theorem po_read : forall x t, json_read sm x = Some t ->
  po_wl f (ReaderRes.lsz (snd (jr_run sm x []))) + po_wl g (po_rs t) <= c * Z.of_nat (length x).
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H |- *. cbn [fst snd] in H |- *.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst snd post] in H |- *; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. destruct (proj1 (po_fuel _) 0%nat x [] t' r tr ok' E) as [_ B].
  unfold ReaderRes.lsz.
  assert (M := po_cm (Z.of_nat (length x) - Z.of_nat (length r)) (Z.of_nat (length x)) ltac:(lia)). lia.
Qed.

Lemma po_cz a : 0 <= a -> 0 <= c * a.
Proof. intros H. pose proof po_c0. nia. Qed.

Lemma po_cb_w0 o n : po_wl f (po_cb o n) <= c * (Z.of_nat n + 1 + (if o then Z.of_nat n else 0)).
Proof.
  destruct n as [|m]; [|apply po_cb_w; lia].
  cbn [po_cb po_wl]. apply po_cz. destruct o; cbv beta iota; lia.
Qed.

Lemma po_grow_nw o n ok tg ok' : grow o n (po_cap n) ok = (None, tg, ok') ->
  po_ext tg (po_cb o n) /\
  po_wl f (fold_left ReaderRes.lsz_ev tg (po_cb o n)) <= c * (Z.of_nat n + 1 + (if o then Z.of_nat n else 0) + 2).
Proof.
  intros H. destruct (po_grow_none o n (po_cap n) ok tg ok' H) as [Etg | [Eo Etg]].
  - assert (I : forall l, fold_left ReaderRes.lsz_ev tg l = l) by (intros l; rewrite Etg; reflexivity).
    split; [apply po_id_ext, I|]. rewrite I.
    eapply Z.le_trans; [apply po_cb_w0|]. apply po_cm. lia.
  - subst o. destruct n as [|m].
    + assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tg (po_cb true 0 ++ s)) ([(56 * po_cap 1)%nat] ++ s)).
      { intros s. rewrite Etg. apply Permutation_refl. }
      destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
      rewrite (po_wl_perm f _ _ Pm). cbn [po_wl].
      destruct (po_hc 1 (le_n 1)) as (A & _ & _). change (Z.of_nat 1) with 1 in A.
      change (Z.of_nat 0) with 0. cbv beta iota.
      assert (M := po_cm (1 + 1) (0 + 1 + 0 + 2) ltac:(lia)). lia.
    + pose proof (po_cap8 (S m) ltac:(lia)) as H8.
      assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tg (po_cb true (S m) ++ s))
                     ([(56 * po_cap (S (S m)))%nat; (8 * po_cap (S m))%nat] ++ s)).
      { intros s. rewrite Etg. cbn [po_cb app fold_left]. rewrite po_lsz_grow by lia.
        rewrite (po_rm_ne (56 * po_cap (S m))%nat (8 * po_cap (S m))%nat) by lia. rewrite po_rm_hd.
        apply Permutation_refl. }
      destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
      rewrite (po_wl_perm f _ _ Pm). cbn [po_wl].
      destruct (po_hc (S (S m)) ltac:(lia)) as (A & _ & _). destruct (po_hc (S m) ltac:(lia)) as (_ & _ & K).
      cbv beta iota. rewrite !Nat2Z.inj_succ in *.
      assert (M := po_cm (Z.succ (Z.succ (Z.of_nat m)) + 1 + Z.succ (Z.of_nat m))
                         (Z.succ (Z.of_nat m) + 1 + Z.succ (Z.of_nat m) + 2) ltac:(lia)). lia.
Qed.

Definition po_VN (k : nat) : Prop := forall d x ok tr ok', jrv sm k d x ok = (None, tr, ok') ->
  po_ext tr [] /\ po_wl f (fold_left ReaderRes.lsz_ev tr []) <= c * (Z.of_nat (length x) + 2 * Z.of_nat (MAXD - d)).

Definition po_LN (k : nat) : Prop := forall d o n acc y ok tr ok',
  jrl sm k d o n (po_cap n) acc y ok = (None, tr, ok') ->
  po_ext tr (po_cb o n) /\
  po_wl f (fold_left ReaderRes.lsz_ev tr (po_cb o n)) <=
    c * (Z.of_nat (length y) + 1 + Z.of_nat n + (if o then Z.of_nat n else 0) + 2 * Z.of_nat (MAXD - d) + 2).

Lemma po_contN k d o b y ok tr ok' : po_LN k ->
  jr_cont (jrl sm k) d o (b :: y) ok = (None, tr, ok') ->
  po_ext tr [] /\ po_wl f (fold_left ReaderRes.lsz_ev tr []) <= c * (Z.of_nat (length (b :: y)) + 2 * Z.of_nat (MAXD - d)).
Proof.
  intros IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota in H.
  { unfold jrefuse in H. injection H as <- _. split; [apply po_id_ext; intros l; reflexivity|].
    cbn [fold_left po_wl]. apply po_cz. lia. }
  apply Nat.ltb_ge in Ed.
  cbn [tl] in H. cbv zeta in H. pose proof (skip_len y) as Hy.
  destruct (skip y) as [|c0 r0] eqn:Ey; cbv beta iota in H.
  - destruct (IHl (S d) o 0%nat [] [] ok tr ok' H) as [E B]. split; [exact E|].
    change (po_cb o 0) with (@nil nat) in B. eapply Z.le_trans; [exact B|]. apply po_cm.
    cbn [length]. destruct o; cbv beta iota; lia.
  - cbn [length] in Hy. destruct (c0 =? closer o); cbv beta iota in H; [unfold jret in H; discriminate|].
    destruct (IHl (S d) o 0%nat [] (c0 :: r0) ok tr ok' H) as [E B]. split; [exact E|].
    change (po_cb o 0) with (@nil nat) in B. eapply Z.le_trans; [exact B|]. apply po_cm.
    cbn [length]. destruct o; cbv beta iota; lia.
Qed.

Lemma po_fuelN : forall k, po_VN k /\ po_LN k.
Proof.
  induction k as [|k [IHv IHl]].
  - split.
    + intros d x ok tr ok' H. cbn [jrv] in H. unfold jrefuse in H. injection H as <- _.
      split; [apply po_id_ext; intros l; reflexivity|]. cbn [fold_left po_wl]. apply po_cz. lia.
    + intros d o n acc y ok tr ok' H. cbn [jrl] in H. unfold jrefuse in H. injection H as <- _.
      split; [apply po_id_ext; intros l; reflexivity|]. cbn [fold_left].
      eapply Z.le_trans; [apply po_cb_w0|]. apply po_cm. lia.
  - split.
    + intros d x ok tr ok' H. cbn [jrv] in H. pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H.
      { unfold jrefuse in H. injection H as <- _. split; [apply po_id_ext; intros l; reflexivity|].
        cbn [fold_left po_wl]. apply po_cz. lia. }
      cbn [length] in Hsx.
      destruct (b =? 123); cbv beta iota in H.
      { destruct (po_contN k d true b y ok tr ok' IHl H) as [E B]. split; [exact E|].
        eapply Z.le_trans; [exact B|]. apply po_cm. cbn [length]. lia. }
      destruct (b =? 91); cbv beta iota in H.
      { destruct (po_contN k d false b y ok tr ok' IHl H) as [E B]. split; [exact E|].
        eapply Z.le_trans; [exact B|]. apply po_cm. cbn [length]. lia. }
      destruct (b =? 34); cbv beta iota in H.
      { apply po_bind_none in H as [H | ([s r1] & t1 & ok1 & t2 & Hj & H & _)].
        - pose proof (po_str_none y ok tr ok' H) as I. split; [apply po_id_ext, I|]. rewrite I.
          cbn [po_wl]. apply po_cz. lia.
        - cbv beta iota in H. unfold jret in H. discriminate. }
      destruct (b =? 116); cbv beta iota in H.
      { apply po_lit_none in H as ->. split; [apply po_id_ext; intros l; reflexivity|].
        cbn [fold_left po_wl]. apply po_cz. lia. }
      destruct (b =? 102); cbv beta iota in H.
      { apply po_lit_none in H as ->. split; [apply po_id_ext; intros l; reflexivity|].
        cbn [fold_left po_wl]. apply po_cz. lia. }
      destruct (b =? 110); cbv beta iota in H.
      { apply po_lit_none in H as ->. split; [apply po_id_ext; intros l; reflexivity|].
        cbn [fold_left po_wl]. apply po_cz. lia. }
      destruct (po_num_none (b :: y) ok tr ok' H) as [I | (L & HL & I)].
      { split; [apply po_id_ext, I|]. rewrite I. cbn [po_wl]. apply po_cz. lia. }
      split; [intros s; rewrite !I; apply Permutation_refl|]. rewrite I. cbn [po_wl].
      pose proof (po_g0 (S L)) as G. pose proof (po_hn L ltac:(lia)) as HS.
      assert (M := po_cm (Z.of_nat L) (Z.of_nat (length x) + 2 * Z.of_nat (MAXD - d))
                        ltac:(cbn [length] in HL; lia)). lia.
    + intros d o n acc y ok tr ok' H. cbn [jrl] in H.
      apply po_bind_none in H as [Hg | (cap1 & tg & ok1 & t2 & Eg & H & Etr)].
      { destruct (po_grow_nw o n ok tr ok' Hg) as [E B]. split; [exact E|].
        eapply Z.le_trans; [exact B|]. apply po_cm. lia. }
      apply po_grow in Eg as [Ec Etg]. cbv beta in H. subst cap1.
      pose proof po_c0 as C0. assert (MD := po_cz (Z.of_nat (MAXD - d)) ltac:(lia)).
      apply po_bind_none in H as [Hn | ([nm y1] & tn & ok2 & t3 & En & H & Et2)].
      { pose proof (po_name_none o y ok1 t2 ok' Hn) as I.
        assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tr (po_cb o n ++ s)) (po_cb o (S n) ++ s)).
        { intros s. rewrite Etr, fold_left_app, Etg, po_grow_cb, I. apply Permutation_refl. }
        destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
        rewrite (po_wl_perm f _ _ Pm). eapply Z.le_trans; [apply po_cb_w; lia|]. apply po_cm.
        rewrite Nat2Z.inj_succ. destruct o; cbv beta iota; lia. }
      cbv beta iota in H. destruct (po_name_w o y ok1 nm y1 tn ok2 En) as (N & HN & WN).
      pose proof (po_g0 (S (length (flat_map ech nm)))) as G.
      pose proof (po_cb_w o (S n) ltac:(lia)) as WC. rewrite Nat2Z.inj_succ in WC.
      apply po_bind_none in H as [Hv | ([v r0] & tv & ok3 & t4 & Ev & H & Et3)].
      { destruct (IHv d y1 ok2 t3 ok' Hv) as [EV WV].
        assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tr (po_cb o n ++ s))
                       ((fold_left ReaderRes.lsz_ev t3 [] ++ N ++ po_cb o (S n)) ++ s)).
        { intros s. rewrite Etr, Et2, !fold_left_app, Etg, po_grow_cb, HN.
          pose proof (EV (N ++ po_cb o (S n) ++ s)) as E1. cbn [app] in E1.
          eapply perm_trans; [exact E1|]. rewrite <- !app_assoc. apply Permutation_refl. }
        destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
        rewrite (po_wl_perm f _ _ Pm), !po_wl_app.
        destruct o; cbv beta iota in WN, WC |- *; lia. }
      cbv beta iota in H.
      destruct (proj1 (po_fuel k) d y1 ok2 v r0 tv ok3 Ev) as [EV WV].
      pose proof (po_wl_nonneg g (po_rs v) po_g0) as GV.
      pose proof (skip_len r0) as Hsr.
      assert (TL : t4 = [] ->
                po_ext tr (po_cb o n) /\
                po_wl f (fold_left ReaderRes.lsz_ev tr (po_cb o n)) <=
                  c * (Z.of_nat (length y) + 1 + Z.of_nat n + (if o then Z.of_nat n else 0) + 2 * Z.of_nat (MAXD - d) + 2)).
      { intros E4. subst t4.
        assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tr (po_cb o n ++ s))
                       ((fold_left ReaderRes.lsz_ev tv [] ++ N ++ po_cb o (S n)) ++ s)).
        { intros s. rewrite Etr, Et2, Et3, app_nil_r, !fold_left_app, Etg, po_grow_cb, HN.
          pose proof (EV (N ++ po_cb o (S n) ++ s)) as E1. cbn [app] in E1.
          eapply perm_trans; [exact E1|]. rewrite <- !app_assoc. apply Permutation_refl. }
        destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
        rewrite (po_wl_perm f _ _ Pm), !po_wl_app.
        assert (M := po_cz (Z.of_nat (length r0)) ltac:(lia)).
        destruct o; cbv beta iota in WN, WC |- *; lia. }
      destruct (skip r0) as [|c1 r1]; [unfold jrefuse in H; injection H as <- _; exact (TL eq_refl)|].
      cbn [length] in Hsr. destruct (c1 =? 44); cbv beta iota in H.
      * destruct (IHl d o (S n) ((nm, v) :: acc) r1 ok3 t4 ok' H) as [EL WL].
        assert (P : forall s, Permutation (fold_left ReaderRes.lsz_ev tr (po_cb o n ++ s))
                       ((fold_left ReaderRes.lsz_ev t4 (po_cb o (S n)) ++ fold_left ReaderRes.lsz_ev tv [] ++ N) ++ s)).
        { intros s. rewrite Etr, Et2, Et3, !fold_left_app, Etg, po_grow_cb, HN.
          pose proof (EV (N ++ po_cb o (S n) ++ s)) as E1. cbn [app] in E1.
          eapply perm_trans; [apply po_fold_perm, E1|].
          eapply perm_trans; [apply po_fold_perm, (po_perm3 (fold_left ReaderRes.lsz_ev tv []) N (po_cb o (S n)) s)|].
          eapply perm_trans; [apply (EL (fold_left ReaderRes.lsz_ev tv [] ++ N ++ s))|].
          rewrite <- !app_assoc. apply Permutation_refl. }
        destruct (po_ext_of _ _ _ P) as [Ex Pm]. split; [exact Ex|].
        rewrite (po_wl_perm f _ _ Pm), !po_wl_app. rewrite Nat2Z.inj_succ in WL.
        assert (M := po_cm (Z.of_nat (length r1) + 1) (Z.of_nat (length r0)) ltac:(lia)).
        destruct o; cbv beta iota in WN, WL |- *; lia.
      * destruct (c1 =? closer o); cbv beta iota in H; [unfold jret in H; discriminate|].
        unfold jrefuse in H. injection H as <- _. exact (TL eq_refl).
Qed.

Theorem po_run : forall ok x, po_wl f (ReaderRes.lsz (snd (jr_run sm x ok))) <= c * (Z.of_nat (length x) + 64).
Proof.
  intros ok x. rewrite jr_run_eq. cbn [snd]. unfold ReaderRes.lsz.
  destruct (jr_value sm 0 x ok) as [[res tr] ok'] eqn:E. cbn [fst snd].
  unfold jr_value in E. destruct res as [[t r]|].
  - destruct (proj1 (po_fuel _) 0%nat x ok t r tr ok' E) as [_ B].
    pose proof (po_wl_nonneg g (po_rs t) po_g0).
    assert (M := po_cm (Z.of_nat (length x) - Z.of_nat (length r)) (Z.of_nat (length x) + 64) ltac:(lia)). lia.
  - destruct (proj1 (po_fuelN _) 0%nat x ok tr ok' E) as [_ B].
    change (2 * Z.of_nat (MAXD - 0)) with 64 in B. exact B.
Qed.

Theorem po_all : forall x,
  po_wl f (ReaderRes.lsz (snd (jr_run sm x []))) +
  po_wl g (match json_read sm x with Some t => po_rs t | None => [] end) <= c * (Z.of_nat (length x) + 64).
Proof.
  intros x. destruct (json_read sm x) as [t|] eqn:H.
  - pose proof (po_read x t H) as B.
    assert (M := po_cm (Z.of_nat (length x)) (Z.of_nat (length x) + 64) ltac:(lia)). lia.
  - cbn [po_wl]. pose proof (po_run [] x). lia.
Qed.

End Own.

Fixpoint po_chk (P : Z -> bool) (k : nat) (n : Z) : bool :=
  match k with
  | O => true
  | S k' => P n && po_chk P k' (n + 1)
  end.

Lemma po_chk_ok P k : forall n, po_chk P k n = true -> forall m, n <= m < n + Z.of_nat k -> P m = true.
Proof.
  induction k as [|k IH]; intros n H m Hm; cbn [po_chk] in H; [lia|].
  apply andb_true_iff in H as [H1 H2]. destruct (Z.eq_dec m n) as [->|Hne]; [exact H1|].
  apply (IH (n + 1) H2). lia.
Qed.

Definition po_P (n : Z) : bool :=
  (1 <=? band (n + 16)) && (band (n + 16) <=? 48) && (pw (band (n + 17)) <=? n + 2) &&
  ((n =? 0) || (pw (band (n + 17)) <=? n)) && (pv (band (n + 17)) <=? n + 2) &&
  ((n =? 0) || (pv (band (n + 17)) <=? n)) && (3 * pv (band (n + 17)) <=? n + 8).

Lemma po_P_tab : po_chk po_P (Z.to_nat 131036) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma po_band48 n : 131052 <= n -> band n = 48.
Proof. intros H. unfold band, MMAP_THRESHOLD. destruct (Z.leb_spec 131052 n); [reflexivity | lia]. Qed.

Lemma po_P_all n : 0 <= n -> po_P n = true.
Proof.
  intros Hn. destruct (Z_lt_le_dec n 131036) as [L|L].
  - apply (po_chk_ok po_P (Z.to_nat 131036) 0 po_P_tab). rewrite Z2Nat.id by lia. lia.
  - unfold po_P. rewrite (po_band48 (n + 16)), (po_band48 (n + 17)) by lia.
    change (pw 48) with 2050. change (pv 48) with 4100.
    repeat (apply andb_true_iff; split); try (apply orb_true_iff; right); apply Z.leb_le; lia.
Qed.

Lemma po_P_props n : 0 <= n ->
  1 <= band (n + 16) <= 48 /\ pw (band (n + 17)) <= n + 2 /\ (1 <= n -> pw (band (n + 17)) <= n) /\
  pv (band (n + 17)) <= n + 2 /\ (1 <= n -> pv (band (n + 17)) <= n) /\ 3 * pv (band (n + 17)) <= n + 8.
Proof.
  intros Hn. pose proof (po_P_all n Hn) as P. unfold po_P in P.
  repeat rewrite andb_true_iff in P. destruct P as ((((((P1 & P2) & P3) & P4) & P5) & P6) & P7).
  rewrite orb_true_iff in P4, P6. apply Z.leb_le in P1, P2, P3, P5, P7.
  split; [lia|]. split; [exact P3|].
  split; [intros H; destruct P4 as [P4|P4]; [apply Z.eqb_eq in P4; lia | apply Z.leb_le in P4; exact P4]|].
  split; [exact P5|].
  split; [intros H; destruct P6 as [P6|P6]; [apply Z.eqb_eq in P6; lia | apply Z.leb_le in P6; exact P6]|].
  exact P7.
Qed.

Lemma po_band_rng s : 1 <= band (Z.of_nat s + 16) <= 48.
Proof. exact (proj1 (po_P_props (Z.of_nat s) ltac:(lia))). Qed.

Definition po_A (j : Z) : Z := if j =? 0 then 2 else 4 * 2 ^ j + 2.

Definition po_B (j : Z) : Z := if j =? 0 then 3 else 8 * 2 ^ j + 3.

Definition po_Q (j : Z) : bool :=
  (pw (band (448 * 2 ^ j + 16)) <=? po_A j) &&
  (pw (band (448 * 2 ^ j + 16)) + pw (band (64 * 2 ^ j + 16)) <=? po_B j) &&
  (pv (band (448 * 2 ^ j + 16)) <=? 2 * po_A j) &&
  (pv (band (448 * 2 ^ j + 16)) + pv (band (64 * 2 ^ j + 16)) <=? 2 * po_B j) &&
  (pw (band (64 * 2 ^ j + 16)) <=? po_A j - 1) && (pv (band (64 * 2 ^ j + 16)) <=? 2 * (po_A j - 1)).

Lemma po_Q_tab : forallb po_Q (zseq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma po_Q_all j : 0 <= j -> po_Q j = true.
Proof.
  intros Hj. destruct (Z_lt_le_dec j 11) as [L|L].
  - pose proof po_Q_tab as T. rewrite forallb_forall in T. apply T. apply In_zseq. lia.
  - assert (P : 2048 <= 2 ^ j) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
    assert (A : po_A j = 4 * 2 ^ j + 2) by (unfold po_A; destruct (Z.eqb_spec j 0); [lia | reflexivity]).
    assert (B : po_B j = 8 * 2 ^ j + 3) by (unfold po_B; destruct (Z.eqb_spec j 0); [lia | reflexivity]).
    unfold po_Q. rewrite (po_band48 (448 * 2 ^ j + 16)), (po_band48 (64 * 2 ^ j + 16)), A, B by lia.
    change (pw 48) with 2050. change (pv 48) with 4100.
    repeat (apply andb_true_iff; split); apply Z.leb_le; lia.
Qed.

Lemma po_Q_props j : 0 <= j ->
  pw (band (448 * 2 ^ j + 16)) <= po_A j /\ pw (band (448 * 2 ^ j + 16)) + pw (band (64 * 2 ^ j + 16)) <= po_B j /\
  pv (band (448 * 2 ^ j + 16)) <= 2 * po_A j /\ pv (band (448 * 2 ^ j + 16)) + pv (band (64 * 2 ^ j + 16)) <= 2 * po_B j /\
  pw (band (64 * 2 ^ j + 16)) <= po_A j - 1 /\ pv (band (64 * 2 ^ j + 16)) <= 2 * (po_A j - 1).
Proof.
  intros Hj. pose proof (po_Q_all j Hj) as Q. unfold po_Q in Q.
  repeat rewrite andb_true_iff in Q. destruct Q as (((((Q1 & Q2) & Q3) & Q4) & Q5) & Q6).
  apply Z.leb_le in Q1, Q2, Q3, Q4, Q5, Q6. repeat split; assumption.
Qed.

Lemma po_cap_w N : (1 <= N)%nat -> exists j, 0 <= j /\
  Z.of_nat (56 * po_cap N) + 16 = 448 * 2 ^ j + 16 /\ Z.of_nat (8 * po_cap N) + 16 = 64 * 2 ^ j + 16 /\
  po_A j <= Z.of_nat N + 1 /\ po_B j <= 2 * Z.of_nat N + 1.
Proof.
  intros HN. destruct (po_cap_form N HN) as (jn & Hc & _ & Hj). exists (Z.of_nat jn). rewrite Hc.
  assert (E : Z.of_nat (2 ^ jn) = 2 ^ Z.of_nat jn) by (rewrite Nat2Z.inj_pow; reflexivity).
  split; [lia|]. split; [rewrite !Nat2Z.inj_mul, E; lia|]. split; [rewrite !Nat2Z.inj_mul, E; lia|].
  unfold po_A, po_B. destruct Hj as [-> | Hj].
  - change (Z.of_nat 0) with 0. cbn [Z.eqb]. lia.
  - destruct (Z.eqb_spec (Z.of_nat jn) 0) as [E0|E0]; [lia|]. cbv beta iota.
    assert (Hz : 4 * 2 ^ Z.of_nat jn < Z.of_nat N) by (rewrite <- E; lia). lia.
Qed.

Definition po_fw (s : nat) : Z := pw (band (Z.of_nat s + 16)).

Definition po_fv (s : nat) : Z := pv (band (Z.of_nat s + 16)).

Lemma po_succ s : Z.of_nat (S s) + 16 = Z.of_nat s + 17.
Proof. lia. Qed.

Lemma po_ok_w : po_ok po_fw (fun _ => 0) 1.
Proof.
  unfold po_ok, po_fw. split; [intros s; apply pw_nonneg|]. split; [intros s; lia|]. split; [lia|].
  split.
  { intros q e _. rewrite po_succ. destruct (po_P_props (Z.of_nat q) ltac:(lia)) as (_ & H & _). lia. }
  split.
  { intros L HL. rewrite po_succ. destruct (po_P_props (Z.of_nat L) ltac:(lia)) as (_ & _ & H & _).
    specialize (H ltac:(lia)). lia. }
  intros N HN. destruct (po_cap_w N HN) as (j & Hj & E1 & E2 & HA & HB). rewrite E1, E2.
  destruct (po_Q_props j Hj) as (Q1 & Q2 & _ & _ & Q5 & _). split; [|split]; lia.
Qed.

Lemma po_ok_v : po_ok po_fv po_fv 2.
Proof.
  unfold po_ok, po_fv. split; [intros s; apply pv_nonneg|]. split; [intros s; apply pv_nonneg|]. split; [lia|].
  split.
  { intros q e He. rewrite !po_succ.
    destruct (po_P_props (Z.of_nat q) ltac:(lia)) as (_ & _ & _ & H1 & _).
    destruct (po_P_props (Z.of_nat e) ltac:(lia)) as (_ & _ & _ & _ & _ & H2). lia. }
  split.
  { intros L HL. rewrite po_succ. destruct (po_P_props (Z.of_nat L) ltac:(lia)) as (_ & _ & _ & _ & H & _).
    specialize (H ltac:(lia)). lia. }
  intros N HN. destruct (po_cap_w N HN) as (j & Hj & E1 & E2 & HA & HB). rewrite E1, E2.
  destruct (po_Q_props j Hj) as (_ & _ & Q3 & Q4 & _ & Q6). split; [|split]; lia.
Qed.

Definition po_bcnt (L : list nat) (k : Z) : Z := Z.of_nat (length (filter (fun s => band (Z.of_nat s + 16) =? k) L)).

Lemma po_bcnt_wl (w : Z -> Z) L :
  zsumZ (fun k => w k * po_bcnt L k) (zseq 0 49) = po_wl (fun s => w (band (Z.of_nat s + 16))) L.
Proof.
  induction L as [|a L IH].
  - cbn [po_wl]. transitivity (zsumZ (fun k => 0 * w k) (zseq 0 49)).
    + apply zsumZ_ext. intros k _. unfold po_bcnt. cbn [filter length Z.of_nat]. ring.
    + rewrite zsumZ_mul_l. ring.
  - cbn [po_wl]. rewrite <- IH.
    transitivity (zsumZ (fun k => (if k =? band (Z.of_nat a + 16) then w k else 0) + w k * po_bcnt L k) (zseq 0 49)).
    + apply zsumZ_ext. intros k _. unfold po_bcnt. cbn [filter].
      rewrite (Z.eqb_sym k). destruct (band (Z.of_nat a + 16) =? k); cbn [length]; [rewrite Nat2Z.inj_succ|]; ring.
    + rewrite zsumZ_add, zsumZ_single; [ring | apply zseq_NoDup | apply In_zseq; pose proof (po_band_rng a); lia].
Qed.

Lemma po_bcnt0 L : po_bcnt L 0 = 0.
Proof.
  unfold po_bcnt. induction L as [|a L IH]; [reflexivity|]. cbn [filter].
  destruct (Z.eqb_spec (band (Z.of_nat a + 16)) 0) as [E|E]; [pose proof (po_band_rng a); lia | exact IH].
Qed.

Lemma po_bcnt_nonneg L k : 0 <= po_bcnt L k.
Proof. unfold po_bcnt. lia. Qed.

Lemma po_zero_k k : 0 <= k < 49 -> pw k = 0 -> k = 0.
Proof. intros Hk E. destruct (Z.eq_dec k 0) as [->|Hne]; [reflexivity|]. pose proof (pw_pos k ltac:(lia)). lia. Qed.

Theorem pack_own : forall sm x t, json_read sm x = Some t ->
  zsumZ (fun k => pw k * po_bcnt (ReaderRes.lsz (snd (jr_run sm x []))) k) (zseq 0 49) <= Z.of_nat (length x).
Proof.
  intros sm x t H. rewrite po_bcnt_wl. pose proof (po_read sm po_fw (fun _ => 0) 1 po_ok_w x t H) as B.
  rewrite po_wl_zero in B. unfold po_fw in B. lia.
Qed.

Theorem pack_own2 : forall sm x t, json_read sm x = Some t ->
  zsumZ (fun k => pv k * po_bcnt (ReaderRes.lsz (snd (jr_run sm x [])) ++ po_rs t) k) (zseq 0 49) <=
    2 * Z.of_nat (length x).
Proof.
  intros sm x t H. rewrite po_bcnt_wl, po_wl_app. pose proof (po_read sm po_fv po_fv 2 po_ok_v x t H) as B.
  unfold po_fv in B. lia.
Qed.

Theorem pack_own_run : forall sm ok x,
  zsumZ (fun k => pw k * po_bcnt (ReaderRes.lsz (snd (jr_run sm x ok))) k) (zseq 0 49) <= Z.of_nat (length x) + 64.
Proof.
  intros sm ok x. rewrite po_bcnt_wl. pose proof (po_run sm po_fw (fun _ => 0) 1 po_ok_w ok x) as B.
  unfold po_fw in B. lia.
Qed.

Theorem pack_own2_run : forall sm x,
  zsumZ (fun k => pv k * po_bcnt (ReaderRes.lsz (snd (jr_run sm x [])) ++
                                 match json_read sm x with Some t => po_rs t | None => [] end) k) (zseq 0 49) <=
    2 * Z.of_nat (length x) + 128.
Proof.
  intros sm x. rewrite po_bcnt_wl, po_wl_app. pose proof (po_all sm po_fv po_fv 2 po_ok_v x) as B.
  unfold po_fv in B. lia.
Qed.

Definition beta_x (x : list Z) (k : Z) : Z := po_bcnt (ReaderRes.lsz (snd (jr_run ReaderRes.jr_strtod x []))) k.

Definition beta2_x (x : list Z) (k : Z) : Z :=
  po_bcnt (ReaderRes.lsz (snd (jr_run ReaderRes.jr_strtod x [])) ++
           match json_read ReaderRes.jr_strtod x with Some t => po_rs t | None => [] end) k.

Theorem beta_x_own : forall x,
  (forall k, 0 <= beta_x x k) /\ beta_x x 0 = 0 /\
  zsumZ (fun k => pw k * beta_x x k) (zseq 0 49) <= Z.of_nat (length x) + 64.
Proof.
  intros x. split; [intros k; apply po_bcnt_nonneg|]. split; [apply po_bcnt0|].
  exact (pack_own_run ReaderRes.jr_strtod [] x).
Qed.

Theorem beta2_x_own : forall x,
  (forall k, 0 <= beta2_x x k) /\ beta2_x x 0 = 0 /\
  zsumZ (fun k => pv k * beta2_x x k) (zseq 0 49) <= 2 * Z.of_nat (length x) + pf_E.
Proof.
  intros x. split; [intros k; apply po_bcnt_nonneg|]. split; [apply po_bcnt0|].
  exact (pack_own2_run ReaderRes.jr_strtod x).
Qed.

Theorem pack_own_fit : forall x, Z.of_nat (length x) <= pf_MAX ->
  CAPOK2 (GALL (CS_of (beta2_x x))) (GMAP (CS_of (beta2_x x))) pf_BMAX pf_NMAX.
Proof.
  intros x Hn. destruct (beta2_x_own x) as (H0 & Hz & Hs).
  apply (pack_fit_CS (beta2_x x) (Z.of_nat (length x))); [lia | intros k _; apply H0 | exact Hs |].
  intros k Hk E. rewrite (po_zero_k k Hk (proj2 (pv_pw k Hk) E)). exact Hz.
Qed.

Theorem pack_own_fit_one : forall x, Z.of_nat (length x) <= pf_MAX ->
  CAPOK2 (GALL (CS_of (beta_x x))) (GMAP (CS_of (beta_x x))) pf_BMAX pf_NMAX.
Proof.
  intros x Hn. destruct (beta_x_own x) as (H0 & Hz & Hs).
  apply (pack_fit_CS_one (beta_x x) (Z.of_nat (length x))); [lia | intros k _; apply H0 | exact Hs |].
  intros k Hk E. rewrite (po_zero_k k Hk E). exact Hz.
Qed.
