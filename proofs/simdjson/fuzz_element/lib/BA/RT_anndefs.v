(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_glue_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Export RT_iface2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ann_ok (n v : Z) : bool := (0 <=? v) && (v <? n) && (v mod 8 =? 0) && (n mod 16 =? 0).
Fixpoint alook (p n : Z) (A : list (Z * Z * Z)) : option Z :=
  match A with
  | [] => None
  | (q, k, v) :: A' => if ((q =? p) && (k =? n)) && ann_ok n v then Some v else alook p n A'
  end.

Definition arem (p : Z) (A : list (Z * Z * Z)) : list (Z * Z * Z) := List.filter (fun e => negb (fst (fst e) =? p)) A.

Lemma ann_ok_spec : forall n v, ann_ok n v = true <-> 0 <= v < n /\ v mod 8 = 0 /\ n mod 16 = 0.
Proof.
  intros n v. unfold ann_ok. rewrite !Bool.andb_true_iff, Z.leb_le, Z.ltb_lt, !Z.eqb_eq. tauto.
Qed.

Lemma arem_cons : forall p q k w A, arem p ((q, k, w) :: A) = if q =? p then arem p A else (q, k, w) :: arem p A.
Proof. intros p q k w A. unfold arem. cbn [List.filter fst]. destruct (q =? p); reflexivity. Qed.

Lemma alook_cons : forall p n q k w A,
  alook p n ((q, k, w) :: A) = if ((q =? p) && (k =? n)) && ann_ok n w then Some w else alook p n A.
Proof. reflexivity. Qed.

Lemma alook_ok : forall p n A v, alook p n A = Some v -> 0 <= v < n /\ v mod 8 = 0 /\ n mod 16 = 0.
Proof.
  intros p n A v. induction A as [|[[q k] w] A IH]; [discriminate|]. rewrite alook_cons.
  destruct ((q =? p) && (k =? n)) eqn:E1; cbn [andb]; [|exact IH].
  destruct (ann_ok n w) eqn:E2; [|exact IH]. intros X. injection X as <-. apply ann_ok_spec. exact E2.
Qed.

Lemma alook_arem_same : forall p n A, alook p n (arem p A) = None.
Proof.
  intros p n A. induction A as [|[[q k] w] A IH]; [reflexivity|]. rewrite arem_cons.
  destruct (Z.eqb_spec q p) as [->|NE]; [exact IH|]. rewrite alook_cons.
  rewrite (proj2 (Z.eqb_neq q p) NE). cbn [andb]. exact IH.
Qed.

Lemma alook_arem_other : forall q p n A, q <> p -> alook q n (arem p A) = alook q n A.
Proof.
  intros q p n A NE. induction A as [|[[r k] w] A IH]; [reflexivity|]. rewrite arem_cons, alook_cons.
  destruct (Z.eqb_spec r p) as [->|NE2].
  - rewrite (proj2 (Z.eqb_neq p q) ltac:(intros E; exact (NE (eq_sym E)))). cbn [andb]. exact IH.
  - rewrite alook_cons, IH. reflexivity.
Qed.

Lemma alook_cons_other : forall q k p n v A, q <> p -> alook q k ((p, n, v) :: A) = alook q k A.
Proof. intros q k p n v A NE. rewrite alook_cons. rewrite (proj2 (Z.eqb_neq p q) ltac:(intros E; exact (NE (eq_sym E)))). reflexivity. Qed.

Lemma alook_cons_same : forall p n v A, alook p n ((p, n, v) :: A) = if ann_ok n v then Some v else alook p n A.
Proof. intros p n v A. rewrite alook_cons. rewrite !Z.eqb_refl. reflexivity. Qed.

Definition fc8 : byte := Z_to_bv 8 252.
Definition fcrun (k : nat) : list byte := repeat fc8 k.
Definition ushadowA (an : option Z) (n : Z) : list byte :=
  match an with
  | None => ushadow n
  | Some v => let L := length (ushadow n) in let k := Nat.min (Z.to_nat (v / 8)) L in repeat z8 k ++ fcrun (L - k)
  end.

Lemma ushadowA_len : forall an n, length (ushadowA an n) = length (ushadow n).
Proof.
  intros [v|] n; cbn [ushadowA]; [|reflexivity]. rewrite length_app, !repeat_length. unfold fcrun. rewrite repeat_length. lia.
Qed.
Lemma ushadowA_none : forall n, ushadowA None n = ushadow n.
Proof. reflexivity. Qed.
Lemma ushadowA_lenZ : forall an n, Z.of_nat (length (ushadowA an n)) = Z.of_nat (length (ushadow n)).
Proof. intros an n. rewrite ushadowA_len. reflexivity. Qed.

Lemma ushadow_len8 : forall n, 0 <= n -> n mod 8 = 0 -> length (ushadow n) = Z.to_nat (n / 8).
Proof.
  intros n Hn H8. unfold ushadow. rewrite H8. cbn [Z.eqb]. rewrite app_nil_r, repeat_length. reflexivity.
Qed.

Lemma ushadowA_some : forall n v, 0 <= v <= n -> v mod 8 = 0 -> n mod 8 = 0 ->
  ushadowA (Some v) n = repeat z8 (Z.to_nat (v / 8)) ++ fcrun (Z.to_nat ((n - v) / 8)).
Proof.
  intros n v Hv V8 N8. cbn [ushadowA]. rewrite (ushadow_len8 n ltac:(lia) N8).
  pose proof (Z.div_mod v 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (HL : (Z.to_nat (v / 8) <= Z.to_nat (n / 8))%nat) by (apply Z2Nat.inj_le; try lia; apply Z.div_pos; lia).
  rewrite (Nat.min_l _ _ HL). f_equal. unfold fcrun. f_equal.
  replace ((n - v) / 8) with (n / 8 - v / 8) by lia. rewrite Z2Nat.inj_sub by (apply Z.div_pos; lia). reflexivity.
Qed.

Definition zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros [a b] [c d]. destruct (Z.eq_dec a c) as [->|N]; [destruct (Z.eq_dec b d) as [->|N]; [left; reflexivity|]|]; right; intros E; injection E; intros; exact (N ltac:(assumption)). Defined.

Definition vis1 (A : list (Z * Z * Z)) (e : Z * Z) : list (Z * Z) :=
  match alook (fst e) (snd e) A with Some v => ann_block (fst e) (snd e) v | None => [e] end.
Definition vis_live (A : list (Z * Z * Z)) (live : list (Z * Z)) : list (Z * Z) := flat_map (vis1 A) live.

Lemma vis_live_nil : forall A, vis_live A [] = [].
Proof. reflexivity. Qed.
Lemma vis_live_cons : forall A e l, vis_live A (e :: l) = vis1 A e ++ vis_live A l.
Proof. reflexivity. Qed.
Lemma vis_live_app : forall A l1 l2, vis_live A (l1 ++ l2) = vis_live A l1 ++ vis_live A l2.
Proof. intros A l1 l2. unfold vis_live. rewrite flat_map_app. reflexivity. Qed.

Lemma vis1_fst : forall A e e', In e' (vis1 A e) -> fst e' = fst e.
Proof.
  intros A [q k] e' H. unfold vis1 in H. cbn [fst snd] in H. destruct (alook q k A) as [v|].
  - exact (ann_block_fst q k v e' H).
  - destruct H as [<-|[]]. reflexivity.
Qed.

Lemma vis1_nonnil : forall A e, vis1 A e <> [].
Proof.
  intros A [q k]. unfold vis1. cbn [fst snd]. destruct (alook q k A) as [v|]; [|discriminate].
  unfold ann_block. destruct (v =? k); discriminate.
Qed.

Lemma vis1_self : forall A q n, alook q n A = None -> vis1 A (q, n) = [(q, n)].
Proof. intros A q n H. unfold vis1. cbn [fst snd]. rewrite H. reflexivity. Qed.
Lemma vis1_block : forall A q n v, alook q n A = Some v -> vis1 A (q, n) = ann_block q n v.
Proof. intros A q n v H. unfold vis1. cbn [fst snd]. rewrite H. reflexivity. Qed.

Lemma In_vis_live : forall A live q k, In (q, k) (vis_live A live) ->
  exists n, In (q, n) live /\
    ((alook q n A = None /\ k = n) \/ (exists v, alook q n A = Some v /\ (k = v \/ k = ann_g1 n \/ k = ann_g2 n))).
Proof.
  intros A live q k H. unfold vis_live in H. apply in_flat_map in H as ([q0 n] & Hin & H).
  pose proof (vis1_fst A (q0, n) (q, k) H) as E. cbn in E. subst q0. exists n. split; [exact Hin|].
  unfold vis1 in H. cbn [fst snd] in H. destruct (alook q n A) as [v|] eqn:EL.
  - right. exists v. split; [reflexivity|]. unfold ann_block in H. destruct (v =? n) eqn:EV.
    + destruct H as [X|[]]. injection X as <-. left. apply Z.eqb_eq in EV. lia.
    + destruct H as [X|[X|[X|[]]]]; injection X as <-; tauto.
  - left. destruct H as [X|[]]. injection X as <-. split; reflexivity.
Qed.

Lemma In_vis_live_le : forall A live q k, In (q, k) (vis_live A live) ->
  exists n, In (q, n) live /\ k <= n /\ (k = n \/ k <= 0 \/ (exists v, alook q n A = Some v /\ k = v)).
Proof.
  intros A live q k H. destruct (In_vis_live A live q k H) as (n & Hin & X). exists n. split; [exact Hin|].
  destruct X as [(HN & ->)|(v & HS & Hk)]; [split; [lia | left; reflexivity]|].
  pose proof (alook_ok q n A v HS) as (V1 & V2 & V3).
  destruct Hk as [ -> | [ -> | -> ] ].
  - split; [lia|]. right; right. exists v. split; [exact HS | reflexivity].
  - unfold ann_g1. pose proof (Z.div_pos (n / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). split; [lia | right; left; lia].
  - unfold ann_g2. pose proof (Z.mod_pos_bound (n / 16) 8192 ltac:(lia)). split; [lia | right; left; lia].
Qed.

Lemma vis_live_In_plain : forall A live q n, In (q, n) live -> alook q n A = None -> In (q, n) (vis_live A live).
Proof.
  intros A live q n Hin HN. unfold vis_live. apply in_flat_map. exists (q, n). split; [exact Hin|]. rewrite (vis1_self A q n HN). left; reflexivity.
Qed.
Lemma vis_live_In_block : forall A live q n v e, In (q, n) live -> alook q n A = Some v -> In e (ann_block q n v) -> In e (vis_live A live).
Proof.
  intros A live q n v e Hin HS He. unfold vis_live. apply in_flat_map. exists (q, n). split; [exact Hin|]. rewrite (vis1_block A q n v HS). exact He.
Qed.

Lemma vis_live_length : forall A live, (length live <= length (vis_live A live))%nat.
Proof.
  intros A live. induction live as [|e l IH]; [cbn; lia|]. rewrite vis_live_cons, length_app.
  pose proof (vis1_nonnil A e) as NN. destruct (vis1 A e) as [|x r]; [exfalso; exact (NN eq_refl)|]. cbn [length]. lia.
Qed.

Lemma vis_live_ext : forall A A' live, (forall q n, In (q, n) live -> alook q n A' = alook q n A) -> vis_live A' live = vis_live A live.
Proof.
  intros A A' live H. induction live as [|[q n] l IH]; [reflexivity|]. rewrite !vis_live_cons. f_equal.
  - unfold vis1. cbn [fst snd]. rewrite (H q n ltac:(left; reflexivity)). reflexivity.
  - apply IH. intros q' n' Hin. exact (H q' n' ltac:(right; exact Hin)).
Qed.

Lemma live_remove_cons' : forall p (e : Z * Z) l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.
Lemma live_remove_app' : forall p l l', live_remove p (l ++ l') = live_remove p l ++ live_remove p l'.
Proof.
  intros p l l'. induction l as [|e l IH]; [reflexivity|]. cbn [app]. rewrite !live_remove_cons', IH. destruct (fst e =? p); reflexivity.
Qed.
Lemma live_remove_all : forall p l, (forall e, In e l -> fst e = p) -> live_remove p l = [].
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. rewrite live_remove_cons'.
  rewrite (proj2 (Z.eqb_eq _ _) (H e ltac:(left; reflexivity))). apply IH. intros e' He'. exact (H e' ltac:(right; exact He')).
Qed.
Lemma live_remove_none' : forall p l, (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. rewrite live_remove_cons'.
  rewrite (proj2 (Z.eqb_neq _ _) (H e ltac:(left; reflexivity))). f_equal. apply IH. intros e' He'. exact (H e' ltac:(right; exact He')).
Qed.

Lemma vis_live_remove : forall A p live, vis_live A (live_remove p live) = live_remove p (vis_live A live).
Proof.
  intros A p live. induction live as [|[q n] l IH]; [reflexivity|].
  rewrite live_remove_cons', vis_live_cons, live_remove_app'. cbn [fst].
  destruct (Z.eqb_spec q p) as [->|NE].
  - rewrite (live_remove_all p (vis1 A (p, n))); [exact IH|]. intros e He. exact (vis1_fst A (p, n) e He).
  - rewrite vis_live_cons, IH. f_equal. symmetry. apply live_remove_none'. intros e He. rewrite (vis1_fst A (q, n) e He). exact NE.
Qed.

Lemma in_live_vis : forall A live a, in_live (vis_live A live) a -> in_live live a.
Proof.
  intros A live a (q & k & Hin & Ha). destruct (In_vis_live_le A live q k Hin) as (n & Hn & Hk & _).
  exists q, n. split; [exact Hn | lia].
Qed.
Lemma aclient_vis : forall A live fr sp a, aclient (vis_live A live) fr sp a -> aclient live fr sp a.
Proof.
  intros A live fr sp a [H|[H|[H|[H|H]]]]; [left; exact H | right; left; exact H | right; right; left; exact (in_live_vis A live a H)
                                             | right; right; right; left; exact H | right; right; right; right; exact H].
Qed.
Lemma rt_pres_vis : forall A live fr sp (m m' : word -> option byte), rt_pres live fr sp m m' -> rt_pres (vis_live A live) fr sp m m'.
Proof. intros A live fr sp m m' H a Ha. exact (H a (aclient_vis A live fr sp _ Ha)). Qed.
Lemma rt_pres_ex_vis : forall A live fr sp d n (m m' : word -> option byte), rt_pres_ex live fr sp d n m m' -> rt_pres_ex (vis_live A live) fr sp d n m m'.
Proof. intros A live fr sp d n m m' H a Ha Hn. exact (H a (aclient_vis A live fr sp _ Ha) Hn). Qed.

Lemma vis_range_real : forall A live q k s len, In (q, k) (vis_live A live) -> q <= s -> s + len <= q + k -> 0 < len ->
  exists n, In (q, n) live /\ q <= s /\ s + len <= q + n.
Proof.
  intros A live q k s len Hin H1 H2 H3. destruct (In_vis_live_le A live q k Hin) as (n & Hn & Hk & _). exists n. split; [exact Hn | lia].
Qed.

Lemma vis_live_split : forall A live p n, List.NoDup (map fst live) -> In (p, n) live ->
  exists L1 L2, live = L1 ++ (p, n) :: L2 /\ (forall e, In e (vis_live A L1) -> fst e <> p) /\ (forall e, In e (vis_live A L2) -> fst e <> p).
Proof.
  intros A live p n ND Hin. apply in_split in Hin as (L1 & L2 & ->). exists L1, L2. split; [reflexivity|].
  rewrite map_app in ND. cbn [map fst] in ND. apply NoDup_remove in ND as [ND NI]. hnf in NI.
  assert (G : forall L e, ~ In p (map fst L) -> In e (vis_live A L) -> fst e <> p).
  { intros L [q k] NIL He E. cbn in E. subst q. destruct (In_vis_live A L p k He) as (n0 & Hn0 & _). apply NIL. apply in_map_iff. exists (p, n0). split; [reflexivity | exact Hn0]. }
  split; intros e He.
  - apply (G L1 e); [|exact He]. intros X. apply NI. apply in_app_iff. left; exact X.
  - apply (G L2 e); [|exact He]. intros X. apply NI. apply in_app_iff. right; exact X.
Qed.

Lemma app_eq_prefix : forall (l1 r1 l2 r2 : list (Z * Z)) p,
  l1 ++ r1 = l2 ++ r2 -> (forall e, In e l1 -> fst e <> p) -> (forall e, In e l2 -> fst e <> p) ->
  (exists x r, r1 = x :: r /\ fst x = p) -> (exists x r, r2 = x :: r /\ fst x = p) -> l1 = l2 /\ r1 = r2.
Proof.
  intros l1. induction l1 as [|a l1 IH]; intros r1 l2 r2 p E H1 H2 (x1 & t1 & -> & X1) (x2 & t2 & -> & X2).
  - destruct l2 as [|b l2]; [split; [reflexivity | exact E]|]. cbn in E. injection E as <- _. exfalso. exact (H2 x1 ltac:(left; reflexivity) X1).
  - destruct l2 as [|b l2].
    + cbn in E. injection E as -> _. exfalso. exact (H1 x2 ltac:(left; reflexivity) X2).
    + cbn in E. injection E as <- E. destruct (IH _ l2 _ p E ltac:(intros e He; exact (H1 e ltac:(right; exact He))) ltac:(intros e He; exact (H2 e ltac:(right; exact He)))
                  ltac:(exists x1, t1; split; [reflexivity | exact X1]) ltac:(exists x2, t2; split; [reflexivity | exact X2])) as (<- & <-).
      split; reflexivity.
Qed.

Lemma vis_live_block : forall A live p n v l1 l2,
  List.NoDup (map fst live) -> (forall q k, In (q, k) live -> 1 <= k < 2 ^ 30) ->
  vis_live A live = l1 ++ ann_block p n v ++ l2 -> (forall e, In e l1 -> fst e <> p) -> 0 <= v <= n -> 1 <= n < 2 ^ 30 -> n mod 16 = 0 ->
  exists L1 L2, live = L1 ++ (p, n) :: L2 /\ vis_live A L1 = l1 /\ vis_live A L2 = l2
    /\ ((v = n /\ alook p n A = None) \/ (v < n /\ alook p n A = Some v)).
Proof.
  intros A live p n v l1 l2 ND SZ E Hl1 Hv Hn N16.
  assert (INV : In (p, v) (vis_live A live)) by (rewrite E; apply in_app_iff; right; apply in_app_iff; left; exact (ann_block_vis p n v)).
  destruct (In_vis_live A live p v INV) as (n0 & Hin0 & _).
  destruct (vis_live_split A live p n0 ND Hin0) as (L1 & L2 & EL & F1 & F2).
  rewrite EL, vis_live_app, vis_live_cons in E.
  pose proof (SZ p n0 Hin0) as B0.

  assert (HX1 : exists x r, vis1 A (p, n0) ++ vis_live A L2 = x :: r /\ fst x = p).
  { pose proof (vis1_nonnil A (p, n0)) as NN. destruct (vis1 A (p, n0)) as [|x r] eqn:EV; [exfalso; exact (NN eq_refl)|].
    exists x, (r ++ vis_live A L2). split; [reflexivity|]. apply (vis1_fst A (p, n0)). rewrite EV. left; reflexivity. }
  assert (HX2 : exists x r, ann_block p n v ++ l2 = x :: r /\ fst x = p).
  { unfold ann_block. destruct (v =? n); cbn; eexists; eexists; (split; [reflexivity | reflexivity]). }
  destruct (app_eq_prefix (vis_live A L1) _ l1 _ p E F1 Hl1 HX1 HX2) as (E1 & E2).

  assert (KEY : n0 = n /\ vis1 A (p, n0) = ann_block p n v /\ vis_live A L2 = l2).
  { unfold vis1 in E2 |- *. cbn [fst snd] in E2 |- *. destruct (alook p n0 A) as [v0|] eqn:EL0.
    - pose proof (alook_ok p n0 A v0 EL0) as (O1 & O2 & O3).
      unfold ann_block in E2 |- *. rewrite (proj2 (Z.eqb_neq v0 n0) ltac:(lia)) in E2 |- *.
      destruct (Z.eqb_spec v n) as [->|NE].
      +
        cbn in E2. injection E2 as E3 _. unfold ann_g1 in E3. pose proof (Z.div_pos (n0 / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). lia.
      + cbn in E2. injection E2 as G1 G2 VV E4. subst v0. unfold ann_g1, ann_g2 in G1, G2.
        pose proof (Z.div_mod (n0 / 16) 8192 ltac:(lia)). pose proof (Z.div_mod (n / 16) 8192 ltac:(lia)).
        pose proof (Z.div_mod n0 16 ltac:(lia)). pose proof (Z.div_mod n 16 ltac:(lia)).
        assert (n0 = n) as -> by lia.
        split; [reflexivity|]. split; [|exact E4]. reflexivity.
    - unfold ann_block in E2 |- *. destruct (Z.eqb_spec v n) as [->|NE].
      + cbn in E2. injection E2 as -> E4. split; [reflexivity|]. split; [reflexivity | exact E4].
      +
        cbn in E2. injection E2 as E3 E4. exfalso.
        assert (HIN : In (p, ann_g2 n) (vis_live A L2)) by (rewrite E4; left; reflexivity).
        exact (F2 _ HIN eq_refl). }
  destruct KEY as (-> & KV & <-). exists L1, L2. split; [exact EL|]. split; [exact E1|]. split; [reflexivity|].
  unfold vis1 in KV. cbn [fst snd] in KV. destruct (alook p n A) as [v0|] eqn:EL0.
  - pose proof (alook_ok p n A v0 EL0) as (O1 & O2 & O3). right.
    destruct (Z.eqb_spec v n) as [->|NE].
    + exfalso. rewrite ann_block_plain in KV. unfold ann_block in KV. rewrite (proj2 (Z.eqb_neq v0 n) ltac:(lia)) in KV. discriminate KV.
    + destruct (ann_block_inj p n v0 n v ltac:(lia) ltac:(lia) O3 N16 ltac:(lia) ltac:(lia) KV) as (_ & ->). split; [lia | reflexivity].
  - left. destruct (Z.eqb_spec v n) as [->|NE]; [split; [reflexivity | reflexivity]|].
    exfalso. unfold ann_block in KV. rewrite (proj2 (Z.eqb_neq v n) NE) in KV. discriminate KV.
Qed.

Lemma vis_live_update : forall A live p n v' L1 L2,
  List.NoDup (map fst live) -> live = L1 ++ (p, n) :: L2 -> 0 <= v' <= n -> v' mod 8 = 0 -> n mod 16 = 0 ->
  vis_live ((p, n, v') :: arem p A) live = vis_live A L1 ++ ann_block p n v' ++ vis_live A L2.
Proof.
  intros A live p n v' L1 L2 ND EL Hv V8 N16. rewrite EL in ND |- *. rewrite vis_live_app, vis_live_cons.
  rewrite map_app in ND. cbn [map fst] in ND. apply NoDup_remove in ND as [ND NI]. hnf in NI.
  assert (OTH : forall L, ~ In p (map fst L) -> vis_live ((p, n, v') :: arem p A) L = vis_live A L).
  { intros L NIL. apply vis_live_ext. intros q k Hq.
    assert (NE : q <> p) by (intros ->; apply NIL; apply in_map_iff; exists (p, k); split; [reflexivity | exact Hq]).
    rewrite (alook_cons_other q k p n v' _ NE). exact (alook_arem_other q p k A NE). }
  rewrite (OTH L1 ltac:(intros X; apply NI; apply in_app_iff; left; exact X)), (OTH L2 ltac:(intros X; apply NI; apply in_app_iff; right; exact X)).
  f_equal. f_equal. unfold vis1. cbn [fst snd]. rewrite alook_cons_same, alook_arem_same.
  destruct (ann_ok n v') eqn:OK; [reflexivity|].
  assert (v' = n) as ->.
  { destruct (Z.eq_dec v' n) as [E|NE]; [exact E|]. exfalso.
    assert (X : ann_ok n v' = true) by (apply ann_ok_spec; lia). rewrite OK in X. discriminate X. }
  rewrite ann_block_plain. reflexivity.
Qed.

Lemma vis_live_fresh_cons : forall A p n live, List.NoDup (map fst ((p, n) :: live)) ->
  vis_live (arem p A) ((p, n) :: live) = (p, n) :: vis_live A live.
Proof.
  intros A p n live ND. cbn [map fst] in ND. apply NoDup_cons_iff in ND as [NI ND].
  rewrite vis_live_cons, (vis1_self (arem p A) p n (alook_arem_same p n A)). cbn [app]. f_equal.
  apply vis_live_ext. intros q k Hq. apply alook_arem_other. intros ->. apply NI. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hq].
Qed.
