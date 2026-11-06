From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterValue.
Import ListNotations.
Open Scope Z_scope.

Ltac zr := repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ || _)%bool = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  end.

Definition ech (c : Z) : list Z := if special c then esc c else [c].

Definition strok (s : list Z) : Prop := Forall (fun b => 0 < b) s.

Definition safe (y : list Z) : Prop := match y with [] => True | b :: _ => numch b = false end.

Definition numtok (txt : list Z) : Prop :=
  exists sg c a, txt = sg ++ c :: a /\ (sg = [] \/ sg = [45]) /\ digit c = true /\ forallb numch a = true /\
    (c = 48 -> match a with c1 :: _ => digit c1 = false | [] => True end).

Lemma spieces_run_concat : forall bs run, concat (spieces_run run bs) = run ++ flat_map ech bs.
Proof.
  induction bs as [|c r IH]; intros run.
  - cbn [spieces_run concat flat_map]. reflexivity.
  - cbn [spieces_run flat_map]. unfold ech. destruct (special c).
    + rewrite concat_cons, concat_cons, IH. reflexivity.
    + rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma wstr_eq : forall bs, concat (spieces bs) = 34 :: flat_map ech bs ++ [34].
Proof.
  intros bs. unfold spieces. rewrite concat_cons, concat_app, spieces_run_concat. reflexivity.
Qed.

Lemma decode_raw : forall c X, 32 <= c -> c <> 34 -> c <> 92 -> decode (c :: X) = emit [c] (decode X).
Proof.
  intros c X H1 H2 H3. cbn [decode].
  rewrite (proj2 (Z.eqb_neq c 34) H2), (proj2 (Z.ltb_ge c 32) H1), (proj2 (Z.eqb_neq c 92) H3).
  reflexivity.
Qed.

Lemma decode_u : forall a0 a1 a2 a3 X cp, hex4 [a0; a1; a2; a3] = Some cp -> 0 < cp < 55296 ->
  decode (92 :: 117 :: a0 :: a1 :: a2 :: a3 :: X) = emit (utf8 cp) (decode X).
Proof.
  intros a0 a1 a2 a3 X cp H1 H2.
  transitivity (match hex4 [a0; a1; a2; a3] with
    | Some v =>
      if v =? 0 then None
      else if (55296 <=? v) && (v <? 56320) then
        match X with
        | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
          match low X with
          | Some lo => emit (utf8 (pair_cp v lo)) (decode r4)
          | None => None
          end
        | _ => None
        end
      else if (56320 <=? v) && (v <? 57344) then None
      else emit (utf8 v) (decode X)
    | None => None
    end); [reflexivity|].
  rewrite H1. rewrite (proj2 (Z.eqb_neq cp 0)) by lia.
  replace ((55296 <=? cp) && (cp <? 56320)) with false
    by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
  replace ((56320 <=? cp) && (cp <? 57344)) with false
    by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma hexval_hexd : forall v, 0 <= v < 16 -> hexval (hexd v) = Some v.
Proof.
  intros v H. unfold hexd, hexval.
  destruct (v <? 10) eqn:E; zr.
  - replace ((48 <=? 48 + v) && (48 + v <=? 57)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    cbv beta iota. f_equal. lia.
  - replace ((48 <=? 87 + v) && (87 + v <=? 57)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    replace ((97 <=? 87 + v) && (87 + v <=? 102)) with true
      by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    cbv beta iota. f_equal. lia.
Qed.

Lemma decode_ech1 : forall c X, 0 < c -> decode (ech c ++ X) = emit [c] (decode X).
Proof.
  intros c X Hc. unfold ech, special.
  destruct (Z.eq_dec c 34) as [->|N34]; [reflexivity|].
  destruct (Z.eq_dec c 92) as [->|N92]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq c 34) N34), (proj2 (Z.eqb_neq c 92) N92). cbn [orb].
  destruct (c <? 32) eqn:E32; zr.
  - destruct (Z.eq_dec c 10) as [->|N10]; [reflexivity|].
    destruct (Z.eq_dec c 9) as [->|N9]; [reflexivity|].
    destruct (Z.eq_dec c 13) as [->|N13]; [reflexivity|].
    unfold esc.
    rewrite (proj2 (Z.eqb_neq c 34) N34), (proj2 (Z.eqb_neq c 92) N92), (proj2 (Z.eqb_neq c 10) N10),
      (proj2 (Z.eqb_neq c 9) N9), (proj2 (Z.eqb_neq c 13) N13).
    cbn [app].
    rewrite (decode_u _ _ _ _ X c).
    + f_equal. unfold utf8. rewrite (proj2 (Z.ltb_lt c 128)) by lia. reflexivity.
    + unfold hex4. cbv beta iota.
      rewrite (hexval_hexd (c / 16)), (hexval_hexd (c mod 16)) by (Z.div_mod_to_equations; lia).
      change (hexval 48) with (Some 0). cbv beta iota. f_equal.
      Z.div_mod_to_equations; lia.
    + lia.
  - cbn [app]. apply decode_raw; assumption.
Qed.

Lemma decode_ech : forall bs rest, strok bs -> decode (flat_map ech bs ++ 34 :: rest) = Some (bs, rest).
Proof.
  induction bs as [|c r IH]; intros rest H; [reflexivity|].
  inversion H as [|? ? Hc Hr]; subst.
  cbn [flat_map]. rewrite <- app_assoc, decode_ech1 by exact Hc. rewrite IH by exact Hr. reflexivity.
Qed.

Lemma jr_string_ech : forall bs rest, strok bs ->
  jr_string (flat_map ech bs ++ 34 :: rest) [] = (Some (bs, rest), [EAlloc (S (length (flat_map ech bs)))], []).
Proof.
  intros bs rest H. pose proof (decode_ech bs rest H) as Hd.
  destruct (decode_stop _ _ _ Hd) as (q & Hs & Hr & _).
  assert (Hq : q = length (flat_map ech bs)).
  { apply (f_equal (@length Z)) in Hr. rewrite length_skipn, length_app in Hr. cbn [length] in Hr.
    pose proof (scan_quote _ _ Hs) as [Hq _]. rewrite length_app in Hq. cbn [length] in Hq. lia. }
  subst q. unfold jr_string. rewrite Hs, Hd. reflexivity.
Qed.

Lemma emit_inv : forall bs d s r, emit bs d = Some (s, r) -> exists s1, d = Some (s1, r) /\ s = bs ++ s1.
Proof. intros bs [[s1 r1]|] s r H; [|discriminate]. cbn in H. injection H as <- <-. eauto. Qed.

Lemma decode_pos : forall x s r, decode x = Some (s, r) -> strok s.
Proof.
  unfold strok.
  intro x. remember (length x) as n eqn:Hn. revert x Hn.
  induction n as [n IH] using lt_wf_ind. intros x Hn s r H.
  destruct x as [|b r0]; [discriminate|]. cbn [decode] in H.
  destruct (b =? 34) eqn:E34; [injection H as <- <-; constructor|].
  destruct (b <? 32) eqn:E32; [discriminate|].
  destruct (negb (b =? 92)) eqn:E92.
  - apply emit_inv in H as (s1 & H & ->). cbn [length] in Hn.
    apply Z.ltb_ge in E32. constructor; [lia|]. exact (IH (length r0) ltac:(lia) r0 eq_refl s1 r H).
  - destruct r0 as [|e r2]; [discriminate|].
    destruct (e =? 117) eqn:Eu.
    + destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; try discriminate.
      destruct (hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Hx; [|discriminate].
      pose proof (hex4_some _ _ Hx) as (a0 & a1 & a2 & a3 & r' & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcp).
      destruct (cp =? 0) eqn:Ec0; [discriminate|]. apply Z.eqb_neq in Ec0.
      destruct ((55296 <=? cp) && (cp <? 56320)) eqn:Ehi.
      * apply andb_true_iff in Ehi as [Eh1 Eh2]. apply Z.leb_le in Eh1. apply Z.ltb_lt in Eh2.
        destruct r3 as [|b1 [|b2 [|m0 [|m1 [|m2 [|m3 r4]]]]]]; try discriminate.
        destruct (low (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: r4)) as [lo|] eqn:Hl; [|discriminate].
        pose proof (low_some _ _ Hl) as (n0 & n1 & n2 & n3 & r'' & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo).
        apply emit_inv in H as (s1 & H & ->).
        apply Forall_app. split.
        -- eapply Forall_impl; [|apply utf8_bytes, pair_cp_range; [split; assumption|exact Hlo]].
           unfold zbyte. intros; lia.
        -- cbn [length] in Hn. exact (IH (length r4) ltac:(lia) r4 eq_refl s1 r H).
      * destruct ((56320 <=? cp) && (cp <? 57344)); [discriminate|].
        apply emit_inv in H as (s1 & H & ->).
        apply Forall_app. split.
        -- eapply Forall_impl; [|apply utf8_bytes; lia]. unfold zbyte. intros; lia.
        -- cbn [length] in Hn. exact (IH (length r3) ltac:(lia) r3 eq_refl s1 r H).
    + destruct (escape e) as [c|] eqn:He; [|discriminate].
      apply emit_inv in H as (s1 & H & ->).
      pose proof (escape_some e c He) as Hc. unfold zbyte in Hc.
      constructor; [lia|]. cbn [length] in Hn. exact (IH (length r2) ltac:(lia) r2 eq_refl s1 r H).
Qed.

Lemma span_numch : forall a y, forallb numch a = true -> safe y -> span numch (a ++ y) = (a, y).
Proof.
  induction a as [|b a IH]; intros y H1 H2.
  - destruct y as [|b y]; [reflexivity|]. cbn [safe] in H2. cbn [app span]. rewrite H2. reflexivity.
  - cbn [forallb] in H1. apply andb_true_iff in H1 as [H1 H3].
    cbn [app span]. rewrite H1, (IH y H3 H2). reflexivity.
Qed.

Lemma span_forall : forall p z a r, span p z = (a, r) -> forallb p a = true /\ z = a ++ r.
Proof.
  intros p z. induction z as [|b z IH]; intros a r H; cbn [span] in H.
  - injection H as <- <-. split; reflexivity.
  - destruct (p b) eqn:Eb.
    + destruct (span p z) as [a1 r1] eqn:E. injection H as <- <-.
      destruct (IH a1 r1 eq_refl) as [H1 H2]. cbn [forallb]. rewrite Eb, H1, H2. split; reflexivity.
    + injection H as <- <-. split; reflexivity.
Qed.

Lemma skipn_len_app : forall (l m : list Z), skipn (length l) (l ++ m) = m.
Proof. induction l as [|a l IH]; intros m; [reflexivity|]. cbn [length app skipn]. apply IH. Qed.

Lemma firstn_len_app : forall (l m : list Z), firstn (length l) (l ++ m) = l.
Proof. induction l as [|a l IH]; intros m; [reflexivity|]. cbn [length app firstn]. rewrite IH. reflexivity. Qed.

Lemma digit_numch : forall b, digit b = true -> numch b = true.
Proof. intros b H. unfold numch. rewrite H. reflexivity. Qed.

Lemma ws_false : forall b, 33 <= b -> ws b = false.
Proof.
  intros b H. unfold ws.
  rewrite (proj2 (Z.eqb_neq b 32)), (proj2 (Z.eqb_neq b 9)), (proj2 (Z.eqb_neq b 10)), (proj2 (Z.eqb_neq b 13))
    by lia.
  reflexivity.
Qed.

Lemma skip_ws_app : forall z X, forallb ws z = true -> skip (z ++ X) = skip X.
Proof.
  induction z as [|b z IH]; intros X H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [H1 H2]. cbn [app skip]. rewrite H1. apply IH, H2.
Qed.

Lemma skip_head : forall U R b U', U = b :: U' -> ws b = false -> skip (U ++ R) = U ++ R.
Proof. intros U R b U' -> H. cbn [app skip]. rewrite H. reflexivity. Qed.

Lemma rep_ws : forall n, forallb ws (concat (repeat [32; 32] n)) = true.
Proof. induction n as [|n IH]; [reflexivity|]. exact IH. Qed.

Lemma wind_ws : forall p d, forallb ws (concat (wind p d)) = true.
Proof. intros [|] d; [exact (rep_ws _)|reflexivity]. Qed.

Ltac lens := rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; cbn [length] in *;
  rewrite ?length_app in *; cbn [length] in *; lia.

Fixpoint tlen (K : nat) (t : jv) : Prop :=
  match t with
  | JNum txt _ => (length txt <= K)%nat
  | JStr s => (length s <= K)%nat
  | JArr items => fold_right (fun u acc => tlen K u /\ acc) True items
  | JObj members => fold_right (fun m acc => match m with (k, u) => (length k <= K)%nat /\ tlen K u end /\ acc) True members
  | _ => True
  end.

Lemma tlen_arr : forall K items, tlen K (JArr items) <-> Forall (tlen K) items.
Proof.
  intros K items. cbn [tlen]. induction items as [|u r IH]; cbn [fold_right].
  - split; [constructor|auto].
  - split.
    + intros [H1 H2]. constructor; [exact H1|apply IH, H2].
    + intros H. inversion H; subst. split; [assumption|apply IH; assumption].
Qed.

Lemma tlen_obj : forall K ms, tlen K (JObj ms) <-> Forall (fun m => (length (fst m) <= K)%nat /\ tlen K (snd m)) ms.
Proof.
  intros K ms. cbn [tlen]. induction ms as [|[k u] r IH]; cbn [fold_right].
  - split; [constructor|auto].
  - split.
    + intros [H1 H2]. constructor; [exact H1|apply IH, H2].
    + intros H. inversion H; subst. split; [assumption|apply IH; assumption].
Qed.

Lemma tlen_mono : forall t K K', (K <= K')%nat -> tlen K t -> tlen K' t.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros K K' HK H.
  - exact I.
  - exact I.
  - exact I.
  - cbn [tlen] in *. lia.
  - cbn [tlen] in *. lia.
  - apply tlen_arr. apply tlen_arr in H. rewrite Forall_forall in *. intros u Hu. exact (IH u Hu K K' HK (H u Hu)).
  - apply tlen_obj. apply tlen_obj in H. rewrite Forall_forall in *. intros m Hm.
    destruct (H m Hm) as [H1 H2]. split; [lia|exact (IH m Hm K K' HK H2)].
Qed.

Fixpoint wgo_arr (p : bool) (d : Z) (i : nat) (l : list jv) : list (list Z) :=
  match l with
  | [] => []
  | x :: r => wcomma i ++ wind p (d + 1) ++ wvpieces x p (d + 1) ++ wgo_arr p d (S i) r
  end.

Fixpoint wgo_obj (p : bool) (d : Z) (i : nat) (l : list (list Z * jv)) : list (list Z) :=
  match l with
  | [] => []
  | (k, x) :: r => wcomma i ++ wind p (d + 1) ++ spieces k ++ [wsep p] ++ wvpieces x p (d + 1) ++ wgo_obj p d (S i) r
  end.

Lemma wv_arr : forall items p d, wvpieces (JArr items) p d =
  [91] :: wgo_arr p d 0 items ++ (match items with [] => [] | _ :: _ => wind p d end) ++ [[93]].
Proof.
  intros items p d. cbn [wvpieces]. do 2 f_equal. generalize 0%nat.
  induction items as [|x r IH]; intros i; [reflexivity|]. simpl. rewrite IH. reflexivity.
Qed.

Lemma wv_obj : forall ms p d, wvpieces (JObj ms) p d =
  [123] :: wgo_obj p d 0 ms ++ (match ms with [] => [] | _ :: _ => wind p d end) ++ [[125]].
Proof.
  intros ms p d. cbn [wvpieces]. do 2 f_equal. generalize 0%nat.
  induction ms as [|[k x] r IH]; intros i; [reflexivity|]. simpl. rewrite IH. reflexivity.
Qed.

Lemma arr_text : forall items p d y, concat (wvpieces (JArr items) p d) ++ y =
  91 :: concat (wgo_arr p d 0 items) ++ concat (match items with [] => [] | _ :: _ => wind p d end) ++ 93 :: y.
Proof. intros. rewrite wv_arr, concat_cons, !concat_app. rewrite <- !app_assoc. reflexivity. Qed.

Lemma obj_text : forall ms p d y, concat (wvpieces (JObj ms) p d) ++ y =
  123 :: concat (wgo_obj p d 0 ms) ++ concat (match ms with [] => [] | _ :: _ => wind p d end) ++ 125 :: y.
Proof. intros. rewrite wv_obj, concat_cons, !concat_app. rewrite <- !app_assoc. reflexivity. Qed.

Lemma wgo_arr_S : forall p d l i, wgo_arr p d (S i) l = wgo_arr p d 1 l.
Proof.
  intros p d l. induction l as [|x r IH]; intros i; [reflexivity|].
  cbn [wgo_arr]. rewrite (IH (S i)), (IH 1%nat). reflexivity.
Qed.

Lemma wgo_obj_S : forall p d l i, wgo_obj p d (S i) l = wgo_obj p d 1 l.
Proof.
  intros p d l. induction l as [|[k x] r IH]; intros i; [reflexivity|].
  cbn [wgo_obj]. rewrite (IH (S i)), (IH 1%nat). reflexivity.
Qed.

Lemma arr_first : forall p d u r, concat (wgo_arr p d 0 (u :: r)) =
  concat (wind p (d + 1)) ++ concat (wvpieces u p (d + 1)) ++ concat (wgo_arr p d 1 r).
Proof. intros. cbn [wgo_arr]. rewrite !concat_app. reflexivity. Qed.

Lemma arr_next : forall p d i u r, concat (wgo_arr p d (S i) (u :: r)) =
  44 :: concat (wind p (d + 1)) ++ concat (wvpieces u p (d + 1)) ++ concat (wgo_arr p d 1 r).
Proof. intros. cbn [wgo_arr]. rewrite (wgo_arr_S p d r (S i)), !concat_app. reflexivity. Qed.

Lemma obj_first : forall p d k u r, concat (wgo_obj p d 0 ((k, u) :: r)) =
  concat (wind p (d + 1)) ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (d + 1)) ++ concat (wgo_obj p d 1 r).
Proof. intros. cbn [wgo_obj]. rewrite !concat_app, concat_cons, <- !app_assoc. reflexivity. Qed.

Lemma obj_next : forall p d i k u r, concat (wgo_obj p d (S i) ((k, u) :: r)) =
  44 :: concat (wind p (d + 1)) ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (d + 1)) ++ concat (wgo_obj p d 1 r).
Proof. intros. cbn [wgo_obj]. rewrite (wgo_obj_S p d r (S i)), !concat_app, concat_cons, <- !app_assoc. reflexivity. Qed.

Lemma wsep_eq : forall p X, wsep p ++ X = 58 :: ((if p then [32] else []) ++ X).
Proof. intros [|] X; reflexivity. Qed.

Lemma sp_ws : forall p : bool, forallb ws (if p then [32] else []) = true.
Proof. intros [|]; reflexivity. Qed.

Lemma wind_safe : forall p d y c, numch c = false -> safe (concat (wind p d) ++ c :: y).
Proof. intros [|] d y c H; [exact eq_refl|exact H]. Qed.

Definition gcap (n cap : nat) : nat :=
  if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.

Definition grow_ev (o : bool) (n cap : nat) : list ev :=
  if Nat.ltb n cap then []
  else EGrow (56 * cap) (56 * gcap n cap) :: (if o then [EGrow (8 * cap) (8 * gcap n cap)] else []).

Fixpoint ttrace (t : jv) : list ev :=
  match t with
  | JNum txt _ => [EAlloc (S (length txt))]
  | JStr s => [EAlloc (S (length (flat_map ech s)))]
  | JArr items =>
    (fix go (n cap : nat) (l : list jv) {struct l} : list ev :=
       match l with
       | [] => []
       | u :: r => grow_ev false n cap ++ ttrace u ++ go (S n) (gcap n cap) r
       end) 0%nat 0%nat items
  | JObj ms =>
    (fix go (n cap : nat) (l : list (list Z * jv)) {struct l} : list ev :=
       match l with
       | [] => []
       | (k, u) :: r => grow_ev true n cap ++ EAlloc (S (length (flat_map ech k))) :: ttrace u ++ go (S n) (gcap n cap) r
       end) 0%nat 0%nat ms
  | _ => []
  end.

Fixpoint tgo_arr (n cap : nat) (l : list jv) : list ev :=
  match l with
  | [] => []
  | u :: r => grow_ev false n cap ++ ttrace u ++ tgo_arr (S n) (gcap n cap) r
  end.

Fixpoint tgo_obj (n cap : nat) (l : list (list Z * jv)) : list ev :=
  match l with
  | [] => []
  | (k, u) :: r => grow_ev true n cap ++ EAlloc (S (length (flat_map ech k))) :: ttrace u ++ tgo_obj (S n) (gcap n cap) r
  end.

Lemma tgo_arr_fix : forall items n cap, tgo_arr n cap items =
  (fix go (n cap : nat) (l : list jv) {struct l} : list ev :=
     match l with
     | [] => []
     | u :: r => grow_ev false n cap ++ ttrace u ++ go (S n) (gcap n cap) r
     end) n cap items.
Proof. induction items as [|u r IH]; intros n cap; [reflexivity|]. cbn [tgo_arr]. rewrite IH. reflexivity. Qed.

Lemma tgo_obj_fix : forall ms n cap, tgo_obj n cap ms =
  (fix go (n cap : nat) (l : list (list Z * jv)) {struct l} : list ev :=
     match l with
     | [] => []
     | (k, u) :: r => grow_ev true n cap ++ EAlloc (S (length (flat_map ech k))) :: ttrace u ++ go (S n) (gcap n cap) r
     end) n cap ms.
Proof. induction ms as [|[k u] r IH]; intros n cap; [reflexivity|]. cbn [tgo_obj]. rewrite IH. reflexivity. Qed.

Lemma tt_arr : forall items, ttrace (JArr items) = tgo_arr 0 0 items.
Proof. intros items. rewrite tgo_arr_fix. reflexivity. Qed.

Lemma tt_obj : forall ms, ttrace (JObj ms) = tgo_obj 0 0 ms.
Proof. intros ms. rewrite tgo_obj_fix. reflexivity. Qed.

Lemma grow_all : forall o n cap, grow o n cap [] = (Some (gcap n cap), grow_ev o n cap, []).
Proof.
  intros o n cap. unfold grow, grow_ev, gcap. destruct (Nat.ltb n cap); [reflexivity|].
  destruct o; reflexivity.
Qed.

Lemma bind_ok : forall A B (m : M A) (k : A -> M B) a t r t',
  m [] = (Some a, t, []) -> k a [] = (r, t', []) -> jbind m k [] = (r, t ++ t', []).
Proof. intros A B m k a t r t' H1 H2. unfold jbind. rewrite H1. cbv beta iota. rewrite H2. reflexivity. Qed.

Lemma jr_name_rt : forall p z k X, forallb ws z = true -> strok k ->
  jr_name true (z ++ concat (spieces k) ++ wsep p ++ X) [] =
    (Some (k, (if p then [32] else []) ++ X), [EAlloc (S (length (flat_map ech k)))], []).
Proof.
  intros p z k X Hz Hk.
  assert (Hs : skip (z ++ concat (spieces k) ++ wsep p ++ X) =
    34 :: (flat_map ech k ++ 34 :: 58 :: ((if p then [32] else []) ++ X))).
  { rewrite skip_ws_app by exact Hz. rewrite wstr_eq, wsep_eq. rewrite <- app_comm_cons, <- app_assoc. reflexivity. }
  pose proof (jr_string_ech k (58 :: ((if p then [32] else []) ++ X)) Hk) as Es.
  unfold jr_name. rewrite Hs. cbv beta iota. rewrite Z.eqb_refl. cbv beta iota.
  unfold jbind. rewrite Es. reflexivity.
Qed.

Lemma jr_cont_empty : forall loop d o b0 X r ok, (S d <= MAXD)%nat -> skip X = closer o :: r ->
  jr_cont loop d o (b0 :: X) ok = jret (mk o [], r) ok.
Proof.
  intros loop d o b0 X r ok H1 H2. unfold jr_cont.
  rewrite (proj2 (Nat.ltb_ge MAXD (S d))) by lia. cbn [tl]. rewrite H2. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma jr_cont_items : forall loop d o b0 X b r ok, (S d <= MAXD)%nat -> skip X = b :: r -> b <> closer o ->
  jr_cont loop d o (b0 :: X) ok = loop (S d) o 0%nat 0%nat [] (skip X) ok.
Proof.
  intros loop d o b0 X b r ok H1 H2 H3. unfold jr_cont.
  rewrite (proj2 (Nat.ltb_ge MAXD (S d))) by lia. cbn [tl]. rewrite H2.
  rewrite (proj2 (Z.eqb_neq b (closer o)) H3). reflexivity.
Qed.

Section RoundTrip.

Variable sm : list Z -> Z * Z.

Fixpoint good (t : jv) : Prop :=
  match t with
  | JNum txt bits => numtok txt /\ whole sm txt = true /\ bits = snd (sm txt)
  | JStr s => strok s
  | JArr items => fold_right (fun u acc => good u /\ acc) True items
  | JObj members => fold_right (fun m acc => match m with (k, u) => strok k /\ good u end /\ acc) True members
  | _ => True
  end.

Lemma good_arr : forall items, good (JArr items) <-> Forall good items.
Proof.
  intros items. cbn [good]. induction items as [|u r IH]; cbn [fold_right].
  - split; [constructor|auto].
  - split.
    + intros [H1 H2]. constructor; [exact H1|apply IH, H2].
    + intros H. inversion H; subst. split; [assumption|apply IH; assumption].
Qed.

Lemma good_obj : forall ms, good (JObj ms) <-> Forall (fun m => strok (fst m) /\ good (snd m)) ms.
Proof.
  intros ms. cbn [good]. induction ms as [|[k u] r IH]; cbn [fold_right].
  - split; [constructor|auto].
  - split.
    + intros [H1 H2]. constructor; [exact H1|apply IH, H2].
    + intros H. inversion H; subst. split; [assumption|apply IH; assumption].
Qed.

Lemma jr_number_tok : forall txt y, numtok txt -> whole sm txt = true -> safe y ->
  jr_number sm (txt ++ y) [] = (Some (JNum txt (snd (sm txt)), y), [EAlloc (S (length txt))], []).
Proof.
  intros txt y (sg & c & a & -> & Hsg & Hc & Ha & H0) Hw Hy.
  assert (Hc1 : 48 <= c <= 57) by (unfold digit in Hc; zr; lia).
  assert (Hj : match (sg ++ c :: a) ++ y with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end = length sg).
  { destruct Hsg as [-> | ->]; cbn [app length].
    - rewrite (proj2 (Z.eqb_neq c 45)) by lia. reflexivity.
    - reflexivity. }
  assert (Hz : ((c =? 48) && match a ++ y with c1 :: _ => digit c1 | [] => false end) = false).
  { destruct (Z.eq_dec c 48) as [E|E].
    - specialize (H0 E). destruct a as [|c1 a].
      + destruct y as [|b y]; [apply andb_false_r|]. cbn [app]. cbn [safe] in Hy.
        destruct (digit b) eqn:Eb; [|apply andb_false_r]. rewrite (digit_numch b Eb) in Hy. discriminate.
      + cbn [app]. rewrite H0. apply andb_false_r.
    - rewrite (proj2 (Z.eqb_neq c 48) E). reflexivity. }
  unfold jr_number. cbv zeta. rewrite Hj.
  replace (skipn (length sg) ((sg ++ c :: a) ++ y)) with (c :: (a ++ y))
    by (rewrite <- app_assoc, skipn_len_app; reflexivity).
  replace (firstn (length sg) ((sg ++ c :: a) ++ y)) with sg
    by (rewrite <- app_assoc, firstn_len_app; reflexivity).
  cbv beta iota. rewrite Hc. cbv beta iota. rewrite Hz. rewrite span_numch by assumption. cbv beta iota.
  rewrite Hw. reflexivity.
Qed.

Lemma jrv_num : forall f d b X ok, 33 <= b -> b <> 123 -> b <> 91 -> b <> 34 -> b <> 116 -> b <> 102 -> b <> 110 ->
  jrv sm (S f) d (b :: X) ok = jr_number sm (b :: X) ok.
Proof.
  intros f d b X ok H0 H1 H2 H3 H4 H5 H6. cbn [jrv].
  assert (Hs : skip (b :: X) = b :: X) by (cbn [skip]; rewrite ws_false by lia; reflexivity).
  rewrite Hs.
  rewrite (proj2 (Z.eqb_neq b 123) H1), (proj2 (Z.eqb_neq b 91) H2), (proj2 (Z.eqb_neq b 34) H3),
    (proj2 (Z.eqb_neq b 116) H4), (proj2 (Z.eqb_neq b 102) H5), (proj2 (Z.eqb_neq b 110) H6).
  reflexivity.
Qed.

Lemma jrv_tok : forall f d txt y ok, numtok txt -> jrv sm (S f) d (txt ++ y) ok = jr_number sm (txt ++ y) ok.
Proof.
  intros f d txt y ok (sg & c & a & -> & Hsg & Hc & _).
  assert (Hc1 : 48 <= c <= 57) by (unfold digit in Hc; zr; lia).
  destruct Hsg as [-> | ->]; cbn [app]; apply jrv_num; lia.
Qed.

Lemma jrv_str : forall f d X ok, jrv sm (S f) d (34 :: X) ok = jbind (jr_string X) (fun '(s, r) => jret (JStr s, r)) ok.
Proof. reflexivity. Qed.

Lemma jrv_arr : forall f d X ok, jrv sm (S f) d (91 :: X) ok = jr_cont (jrl sm f) d false (91 :: X) ok.
Proof. reflexivity. Qed.

Lemma jrv_obj : forall f d X ok, jrv sm (S f) d (123 :: X) ok = jr_cont (jrl sm f) d true (123 :: X) ok.
Proof. reflexivity. Qed.

Lemma jrv_ws : forall f d z X ok, forallb ws z = true -> jrv sm f d (z ++ X) ok = jrv sm f d X ok.
Proof. intros [|f] d z X ok H; [reflexivity|]. cbn [jrv]. rewrite (skip_ws_app z X H). reflexivity. Qed.

Lemma first_byte : forall t p dw, good t ->
  exists b U, concat (wvpieces t p dw) = b :: U /\ ws b = false /\ b <> 93 /\ b <> 125.
Proof.
  intros t p dw Hg. destruct t as [| | | txt bits | s | items | ms].
  - eexists _, _. split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - eexists _, _. split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - eexists _, _. split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - destruct Hg as [(sg & c & a & -> & Hsg & Hc & _) _].
    assert (Hc1 : 48 <= c <= 57) by (unfold digit in Hc; zr; lia).
    destruct Hsg as [-> | ->].
    + exists c, (a ++ []). split; [reflexivity|]. split; [apply ws_false; lia|]. split; lia.
    + exists 45, (c :: a ++ []). split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - exists 34, (flat_map ech s ++ [34]). split; [apply wstr_eq|]. split; [reflexivity|]. split; lia.
  - eexists _, _. split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - eexists _, _. split; [reflexivity|]. split; [reflexivity|]. split; lia.
Qed.

Definition Qv (t : jv) : Prop := forall p dw d, (depth t + d <= MAXD)%nat -> forall y f, safe y ->
  (2 * length (concat (wvpieces t p dw) ++ y) + 1 <= f)%nat ->
  jrv sm f d (concat (wvpieces t p dw) ++ y) [] = (Some (t, y), ttrace t, []).

Lemma rt_arr_loop : forall p dw d y r u acc n cap z f,
  Forall (fun v => Qv v /\ (depth v + S d <= MAXD)%nat) (u :: r) -> forallb ws z = true ->
  (2 * length (z ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93%Z :: y) + 2
     <= f)%nat ->
  jrl sm f (S d) false n cap acc
    (z ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y) [] =
    (Some (JArr (map snd (rev acc) ++ u :: r), y), tgo_arr n cap (u :: r), []).
Proof.
  intros p dw d y r. induction r as [|u' r' IH]; intros u acc n cap z f HF Hz Hf.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Qu Du] _].
    cbn [wgo_arr concat app] in *.
    pose proof (Qu p (dw + 1) (S d) Du (concat (wind p dw) ++ 93 :: y) f (wind_safe p dw y 93 eq_refl)) as Ev.
    lapply Ev; [clear Ev; intro Ev|lens].
    assert (Es : skip (concat (wind p dw) ++ 93 :: y) = 93 :: y)
      by (rewrite skip_ws_app by apply wind_ws; reflexivity).
    replace (map snd (rev acc) ++ [u]) with (map snd (rev (([], u) :: acc)))
      by (cbn [rev]; rewrite map_app; reflexivity).
    change (tgo_arr n cap [u]) with (grow_ev false n cap ++ ([] ++ (ttrace u ++ []))).
    cbn [jrl].
    eapply bind_ok; [apply grow_all|]. cbv beta.
    eapply bind_ok; [reflexivity|]. cbv beta iota.
    eapply bind_ok; [rewrite jrv_ws by exact Hz; exact Ev|]. cbv beta iota.
    rewrite Es. reflexivity.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Qu Du] HF'].
    rewrite (arr_next p dw 0 u' r') in *. cbn [app] in *. rewrite <- !app_assoc in *.
    pose proof (Qu p (dw + 1) (S d) Du
      (44 :: concat (wind p (dw + 1)) ++ concat (wvpieces u' p (dw + 1)) ++ concat (wgo_arr p dw 1 r') ++
         concat (wind p dw) ++ 93 :: y) f eq_refl) as Ev.
    lapply Ev; [clear Ev; intro Ev|lens].
    pose proof (IH u' (([], u) :: acc) (S n) (gcap n cap) (concat (wind p (dw + 1))) f HF' (wind_ws _ _)) as Etr.
    lapply Etr; [clear Etr; intro Etr|lens].
    replace (map snd (rev acc) ++ u :: u' :: r') with (map snd (rev (([], u) :: acc)) ++ u' :: r')
      by (cbn [rev]; rewrite map_app, <- app_assoc; reflexivity).
    change (tgo_arr n cap (u :: u' :: r')) with
      (grow_ev false n cap ++ ([] ++ (ttrace u ++ tgo_arr (S n) (gcap n cap) (u' :: r')))).
    cbn [jrl].
    eapply bind_ok; [apply grow_all|]. cbv beta.
    eapply bind_ok; [reflexivity|]. cbv beta iota.
    eapply bind_ok; [rewrite jrv_ws by exact Hz; exact Ev|]. cbv beta iota.
    match goal with |- context [skip (44 :: ?R)] => change (skip (44 :: R)) with (44 :: R) end.
    cbv beta iota. rewrite Z.eqb_refl. cbv beta iota.
    exact Etr.
Qed.

Lemma rt_obj_loop : forall p dw d y r k u acc n cap z f,
  Forall (fun m => strok (fst m) /\ Qv (snd m) /\ (depth (snd m) + S d <= MAXD)%nat) ((k, u) :: r) ->
  forallb ws z = true ->
  (2 * length (z ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_obj p dw 1 r) ++
     concat (wind p dw) ++ 125%Z :: y) + 2 <= f)%nat ->
  jrl sm f (S d) true n cap acc
    (z ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++ concat (wgo_obj p dw 1 r) ++
     concat (wind p dw) ++ 125 :: y) [] =
    (Some (JObj (rev acc ++ (k, u) :: r), y), tgo_obj n cap ((k, u) :: r), []).
Proof.
  intros p dw d y r. induction r as [|[k' u'] r' IH]; intros k u acc n cap z f HF Hz Hf.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Sk [Qu Du]] _]. cbn [fst snd] in Sk, Qu, Du.
    cbn [wgo_obj concat app] in *.
    pose proof (jr_name_rt p z k (concat (wvpieces u p (dw + 1)) ++ concat (wind p dw) ++ 125 :: y) Hz Sk) as En.
    pose proof (Qu p (dw + 1) (S d) Du (concat (wind p dw) ++ 125 :: y) f (wind_safe p dw y 125 eq_refl)) as Ev.
    lapply Ev; [clear Ev; intro Ev|lens].
    assert (Es : skip (concat (wind p dw) ++ 125 :: y) = 125 :: y)
      by (rewrite skip_ws_app by apply wind_ws; reflexivity).
    change (tgo_obj n cap [(k, u)]) with
      (grow_ev true n cap ++ ([EAlloc (S (length (flat_map ech k)))] ++ (ttrace u ++ []))).
    cbn [jrl].
    eapply bind_ok; [apply grow_all|]. cbv beta.
    eapply bind_ok; [exact En|]. cbv beta iota.
    eapply bind_ok; [rewrite jrv_ws by apply sp_ws; exact Ev|]. cbv beta iota.
    rewrite Es. reflexivity.
  - destruct f as [|f]; [lia|].
    apply Forall_cons_iff in HF as [[Sk [Qu Du]] HF']. cbn [fst snd] in Sk, Qu, Du.
    rewrite (obj_next p dw 0 k' u' r') in *. cbn [app] in *. rewrite <- !app_assoc in *.
    pose proof (jr_name_rt p z k (concat (wvpieces u p (dw + 1)) ++
      44 :: concat (wind p (dw + 1)) ++ concat (spieces k') ++ wsep p ++ concat (wvpieces u' p (dw + 1)) ++
      concat (wgo_obj p dw 1 r') ++ concat (wind p dw) ++ 125 :: y) Hz Sk) as En.
    pose proof (Qu p (dw + 1) (S d) Du
      (44 :: concat (wind p (dw + 1)) ++ concat (spieces k') ++ wsep p ++ concat (wvpieces u' p (dw + 1)) ++
      concat (wgo_obj p dw 1 r') ++ concat (wind p dw) ++ 125 :: y) f eq_refl) as Ev.
    lapply Ev; [clear Ev; intro Ev|lens].
    pose proof (IH k' u' ((k, u) :: acc) (S n) (gcap n cap) (concat (wind p (dw + 1))) f HF' (wind_ws _ _)) as Etr.
    lapply Etr; [clear Etr; intro Etr|lens].
    replace (rev acc ++ (k, u) :: (k', u') :: r') with (rev ((k, u) :: acc) ++ (k', u') :: r')
      by (cbn [rev]; rewrite <- app_assoc; reflexivity).
    change (tgo_obj n cap ((k, u) :: (k', u') :: r')) with
      (grow_ev true n cap ++ ([EAlloc (S (length (flat_map ech k)))] ++
        (ttrace u ++ tgo_obj (S n) (gcap n cap) ((k', u') :: r')))).
    cbn [jrl].
    eapply bind_ok; [apply grow_all|]. cbv beta.
    eapply bind_ok; [exact En|]. cbv beta iota.
    eapply bind_ok; [rewrite jrv_ws by apply sp_ws; exact Ev|]. cbv beta iota.
    match goal with |- context [skip (44 :: ?R)] => change (skip (44 :: R)) with (44 :: R) end.
    cbv beta iota. rewrite Z.eqb_refl. cbv beta iota.
    exact Etr.
Qed.

Lemma rt_value : forall t, good t -> Qv t.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind';
    intros Hg p dw d Hd y f Hy Hf; (destruct f as [|f]; [lia|]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct Hg as [Ht [Hw ->]].
    assert (Ein : concat (wvpieces (JNum txt (snd (sm txt))) p dw) ++ y = txt ++ y)
      by (cbn [wvpieces concat]; rewrite app_nil_r; reflexivity).
    rewrite Ein. rewrite jrv_tok by exact Ht. exact (jr_number_tok txt y Ht Hw Hy).
  - cbn [good] in Hg.
    assert (Ein : concat (wvpieces (JStr s) p dw) ++ y = 34 :: (flat_map ech s ++ 34 :: y)).
    { cbn [wvpieces]. rewrite wstr_eq, <- app_comm_cons, <- app_assoc. reflexivity. }
    rewrite Ein, jrv_str. unfold jbind. rewrite (jr_string_ech s y Hg). reflexivity.
  - apply good_arr in Hg.
    assert (HF : Forall (fun v => Qv v /\ (depth v + S d <= MAXD)%nat) items).
    { rewrite Forall_forall in *. intros v Hv. split; [exact (IH v Hv (Hg v Hv))|].
      pose proof (depth_item items v Hv). lia. }
    clear IH.
    assert (HD : (S d <= MAXD)%nat) by (cbn [depth] in Hd; lia).
    rewrite arr_text in *. rewrite jrv_arr. rewrite tt_arr.
    destruct items as [|u r].
    + rewrite (jr_cont_empty (jrl sm f) d false 91 _ y []); [| exact HD | reflexivity]. reflexivity.
    + cbv beta iota in *. rewrite arr_first in *. rewrite <- !app_assoc in *.
      apply Forall_cons_iff in Hg as [Gu _].
      destruct (first_byte u p (dw + 1) Gu) as (b & U' & EU & Hb1 & Hb2 & _).
      assert (Hs : skip (concat (wind p (dw + 1)) ++ concat (wvpieces u p (dw + 1)) ++
          concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y) =
        concat (wvpieces u p (dw + 1)) ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y).
      { rewrite skip_ws_app by apply wind_ws. exact (skip_head _ _ b U' EU Hb1). }
      rewrite (jr_cont_items (jrl sm f) d false 91 _ b (U' ++ concat (wgo_arr p dw 1 r) ++ concat (wind p dw) ++ 93 :: y) []);
        [| exact HD | rewrite Hs, EU; reflexivity | exact Hb2].
      rewrite Hs.
      pose proof (rt_arr_loop p dw d y r u [] 0%nat 0%nat [] f HF eq_refl) as E.
      lapply E; [clear E; intro E; exact E|lens].
  - apply good_obj in Hg.
    assert (HF : Forall (fun m => strok (fst m) /\ Qv (snd m) /\ (depth (snd m) + S d <= MAXD)%nat) ms).
    { rewrite Forall_forall in *. intros [k v] Hv. destruct (Hg (k, v) Hv) as [H1 H2].
      split; [exact H1|]. split; [exact (IH (k, v) Hv H2)|].
      pose proof (depth_member ms k v Hv). cbn [snd]. lia. }
    clear IH.
    assert (HD : (S d <= MAXD)%nat) by (cbn [depth] in Hd; lia).
    rewrite obj_text in *. rewrite jrv_obj. rewrite tt_obj.
    destruct ms as [|[k u] r].
    + rewrite (jr_cont_empty (jrl sm f) d true 123 _ y []); [| exact HD | reflexivity]. reflexivity.
    + cbv beta iota in *. rewrite obj_first in *. rewrite <- !app_assoc in *.
      assert (Hs : skip (concat (wind p (dw + 1)) ++ concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++
          concat (wgo_obj p dw 1 r) ++ concat (wind p dw) ++ 125 :: y) =
        concat (spieces k) ++ wsep p ++ concat (wvpieces u p (dw + 1)) ++
          concat (wgo_obj p dw 1 r) ++ concat (wind p dw) ++ 125 :: y).
      { rewrite skip_ws_app by apply wind_ws. exact (skip_head _ _ 34 _ (wstr_eq k) eq_refl). }
      rewrite (jr_cont_items (jrl sm f) d true 123 _ 34 ((flat_map ech k ++ [34]) ++ wsep p ++
          concat (wvpieces u p (dw + 1)) ++ concat (wgo_obj p dw 1 r) ++ concat (wind p dw) ++ 125 :: y) []);
        [| exact HD | rewrite Hs, wstr_eq; reflexivity | cbn; lia].
      rewrite Hs.
      pose proof (rt_obj_loop p dw d y r k u [] 0%nat 0%nat [] f HF eq_refl) as E.
      lapply E; [clear E; intro E; exact E|lens].
Qed.

Lemma jr_number_good : forall x ok u r t o, jr_number sm x ok = (Some (u, r), t, o) ->
  exists txt, u = JNum txt (snd (sm txt)) /\ numtok txt /\ whole sm txt = true /\ (length txt <= length x)%nat.
Proof.
  intros x ok u r t o H. unfold jr_number in H. cbv zeta in H.
  remember (match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) as j eqn:Ej.
  destruct (skipn j x) as [|c z] eqn:Ez; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)) eqn:Ed; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end) eqn:E0; cbv beta iota in H;
    [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:Es. cbv beta iota in H.
  apply span_forall in Es as [Ha Hz].
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & ? & H & ?).
  destruct (whole sm (firstn j x ++ c :: a)) eqn:Ew; [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as Hu _ _.
  exists (firstn j x ++ c :: a). split; [symmetry; exact Hu|]. split; [|split; [exact Ew|]].
  - apply negb_false_iff in Ed.
    destruct x as [|b0 x']; [rewrite skipn_nil in Ez; discriminate|].
    exists (firstn j (b0 :: x')), c, a. split; [reflexivity|]. split.
    + destruct (b0 =? 45) eqn:E45; subst j; cbn [firstn].
      * apply Z.eqb_eq in E45. subst b0. right. reflexivity.
      * left. reflexivity.
    + split; [exact Ed|]. split; [exact Ha|].
      intros Hc. subst c. cbn [Z.eqb Pos.eqb andb] in E0.
      destruct a as [|c1 a]; [exact I|]. cbn [app] in Hz. subst z. exact E0.
  - pose proof (firstn_skipn j x) as Hx. rewrite Ez, Hz in Hx.
    rewrite <- Hx at 2. rewrite !length_app. cbn [length]. rewrite length_app. lia.
Qed.

Lemma jr_name_good : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  (length y1 <= length y)%nat /\ (o = true -> strok nm /\ (length nm <= length y)%nat).
Proof.
  intros o y ok nm y1 tn ok2 H. destruct o.
  - unfold jr_name in H. pose proof (skip_len y) as Hy.
    destruct (skip y) as [|b z] eqn:Ey; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
    cbn [length] in Hy.
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([s r] & t1 & ok1 & t2 & Hj & H & _).
    pose proof (jr_string_spec z ok) as Hs. rewrite Hj in Hs.
    destruct Hs as (q & Hq & Hd & _ & Hl).
    destruct (decode_stop z s r Hd) as (q' & Hq' & _ & Hls & _). rewrite Hq in Hq'. injection Hq' as <-.
    cbv beta iota in H.
    pose proof (skip_len r) as Hr.
    destruct (skip r) as [|c r1]; cbv beta iota in H.
    + apply jbind_some in H as (? & ? & ? & ? & ? & H & ?). unfold jrefuse in H. discriminate.
    + cbn [length] in Hr.
      destruct (c =? 58); cbv beta iota in H.
      * unfold jret in H. injection H as <- <- _ _.
        split; [lia|]. intros _. split; [exact (decode_pos z s r Hd)|lia].
      * apply jbind_some in H as (? & ? & ? & ? & ? & H & ?). unfold jrefuse in H. discriminate.
  - unfold jr_name, jret in H. injection H as <- <- _ _. split; [lia|]. discriminate.
Qed.

Definition item_inv (o : bool) (d K : nat) (m : list Z * jv) : Prop :=
  (o = true -> strok (fst m) /\ (length (fst m) <= K)%nat) /\ good (snd m) /\
  (depth (snd m) + d <= MAXD)%nat /\ tlen K (snd m).

Lemma mk_inv : forall o d K L, (d <= MAXD)%nat -> Forall (item_inv o d K) L ->
  good (mk o L) /\ (depth (mk o L) + d <= S MAXD)%nat /\ tlen K (mk o L).
Proof.
  intros o d K L Hd H. destruct o; unfold mk.
  - split; [|split].
    + apply good_obj. eapply Forall_impl; [|exact H]. intros m (H1 & H2 & _). split; [apply H1; reflexivity|exact H2].
    + cbn [depth].
      assert (list_max (map (fun '(_, v) => depth v) L) <= MAXD - d)%nat; [|lia].
      apply list_max_le, Forall_map. eapply Forall_impl; [|exact H]. intros [k v] (_ & _ & H3 & _). cbn [snd] in H3. lia.
    + apply tlen_obj. eapply Forall_impl; [|exact H]. intros m (H1 & _ & _ & H4).
      split; [apply H1; reflexivity|exact H4].
  - split; [|split].
    + apply good_arr, Forall_map. eapply Forall_impl; [|exact H]. intros m (_ & H2 & _). exact H2.
    + cbn [depth]. rewrite map_map.
      assert (list_max (map (fun x => depth (snd x)) L) <= MAXD - d)%nat; [|lia].
      apply list_max_le, Forall_map. eapply Forall_impl; [|exact H]. intros m (_ & _ & H3 & _). lia.
    + apply tlen_arr, Forall_map. eapply Forall_impl; [|exact H]. intros m (_ & _ & _ & H4). exact H4.
Qed.

Lemma read_lit : forall w v x ok t r tr ok' d K, (d <= MAXD)%nat -> (v = JTrue \/ v = JFalse \/ v = JNull) ->
  lit w v x ok = (Some (t, r), tr, ok') -> good t /\ (depth t + d <= MAXD)%nat /\ tlen K t.
Proof.
  intros w v x ok t r tr ok' d K Hd Hv H. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as <- _ _ _.
  destruct Hv as [-> | [-> | ->]]; (split; [exact I|]; split; [cbn [depth]; lia|exact I]).
Qed.

Lemma read_cont : forall f d o b y ok t r tr ok', (d <= MAXD)%nat ->
  (forall d o n cap acc y ok t r tr ok' K, (d <= MAXD)%nat -> (length y <= K)%nat -> Forall (item_inv o d K) acc ->
     jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') -> good t /\ (depth t + d <= S MAXD)%nat /\ tlen K t) ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (t, r), tr, ok') ->
  good t /\ (depth t + d <= MAXD)%nat /\ tlen (length (b :: y)) t.
Proof.
  intros f d o b y ok t r tr ok' Hd IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)) eqn:Ed; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  apply Nat.ltb_ge in Ed. cbn [tl] in H. cbv zeta in H.
  pose proof (skip_len y) as Hy.
  assert (HL : forall y', (length y' <= length y)%nat -> jrl sm f (S d) o 0%nat 0%nat [] y' ok = (Some (t, r), tr, ok') ->
    good t /\ (depth t + d <= MAXD)%nat /\ tlen (length (b :: y)) t).
  { intros y' Hy' H'.
    destruct (IHl (S d) o 0%nat 0%nat [] y' ok t r tr ok' (length (b :: y)) Ed ltac:(cbn [length]; lia)
      (Forall_nil _) H') as (A & B & C).
    split; [exact A|]. split; [lia|exact C]. }
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H; [exact (HL [] Hy H)|].
  destruct (c =? closer o); cbv beta iota in H; [|exact (HL _ Hy H)].
  unfold jret in H. injection H as Ht _ _ _. subst t.
  split; [destruct o; exact I|]. split; [destruct o; cbn [mk depth map list_max fold_right]; lia|destruct o; exact I].
Qed.

Lemma read_fuel : forall f,
  (forall d x ok t r tr ok', (d <= MAXD)%nat -> jrv sm f d x ok = (Some (t, r), tr, ok') ->
     good t /\ (depth t + d <= MAXD)%nat /\ tlen (length x) t) /\
  (forall d o n cap acc y ok t r tr ok' K, (d <= MAXD)%nat -> (length y <= K)%nat -> Forall (item_inv o d K) acc ->
     jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     good t /\ (depth t + d <= S MAXD)%nat /\ tlen K t).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' Hd H. cbn [jrv] in H.
      pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (Hmono : forall t, tlen (length (b :: y)) t -> tlen (length x) t)
        by (intros t0; apply tlen_mono; exact Hsx).
      destruct (b =? 123); cbv beta iota in H.
      { destruct (read_cont f d true b y ok t r tr ok' Hd IHl H) as (A & B & C). auto. }
      destruct (b =? 91); cbv beta iota in H.
      { destruct (read_cont f d false b y ok t r tr ok' Hd IHl H) as (A & B & C). auto. }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
        pose proof (jr_string_spec y ok) as Hs. rewrite Hj in Hs. destruct Hs as (q & Hq & Hd2 & _ & Hl).
        destruct (decode_stop y s r1 Hd2) as (q' & Hq' & _ & Hls & _). rewrite Hq in Hq'. injection Hq' as <-.
        cbv beta iota in H. unfold jret in H. injection H as <- _ _ _.
        split; [exact (decode_pos y s r1 Hd2)|]. split; [cbn [depth]; lia|]. cbn [tlen length] in *. lia. }
      destruct (b =? 116); cbv beta iota in H.
      { exact (read_lit w_true JTrue _ _ _ _ _ _ d (length x) Hd (or_introl eq_refl) H). }
      destruct (b =? 102); cbv beta iota in H.
      { exact (read_lit w_false JFalse _ _ _ _ _ _ d (length x) Hd (or_intror (or_introl eq_refl)) H). }
      destruct (b =? 110); cbv beta iota in H.
      { exact (read_lit w_null JNull _ _ _ _ _ _ d (length x) Hd (or_intror (or_intror eq_refl)) H). }
      destruct (jr_number_good _ _ _ _ _ _ H) as (txt & -> & Ht & Hw & Hl).
      split; [cbn [good]; auto|]. split; [cbn [depth]; lia|]. cbn [tlen length] in *. lia.
    + intros d o n cap acc y ok t r tr ok' K Hd HK Hacc H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & Eg & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      destruct (jr_name_good o y ok1 nm y1 tn ok2 En) as [Hy1 Hnm].
      destruct (IHv d y1 ok2 v r0 tv ok3 Hd Ev) as (Gv & Dv & Tv).
      pose proof (proj1 (spec_fuel sm f) d y1 ok2) as Hsp. rewrite Ev in Hsp. destruct Hsp as (_ & _ & Hsp).
      destruct (Hsp v r0 eq_refl) as (Hr0 & _ & _).
      assert (Hit : item_inv o d K (nm, v)).
      { unfold item_inv. cbn [fst snd]. split; [intros E; destruct (Hnm E); split; [assumption|lia]|].
        split; [exact Gv|]. split; [exact Dv|]. apply (tlen_mono v (length y1)); [lia|exact Tv]. }
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c r1] eqn:Er; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      destruct (c =? 44); cbv beta iota in H.
      { exact (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' K Hd ltac:(lia) (Forall_cons _ Hit Hacc) H). }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as Ht _ _ _. subst t.
      apply mk_inv; [exact Hd|]. apply Forall_app. split; [apply Forall_rev; exact Hacc|constructor; [exact Hit|constructor]].
Qed.

Lemma read_json : forall x t, json_read sm x = Some t -> good t /\ (depth t <= MAXD)%nat /\ tlen (length x) t.
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. destruct (proj1 (read_fuel _) 0%nat x [] t' r tr ok' ltac:(unfold MAXD; lia) E) as (A & B & C).
  split; [exact A|]. split; [lia|exact C].
Qed.

Lemma set_good : forall ms kname tv, Forall (fun m => strok (fst m) /\ good (snd m)) ms -> strok kname -> good tv ->
  Forall (fun m => strok (fst m) /\ good (snd m)) (pj_set_model ms kname tv).
Proof.
  induction ms as [|[k v] r IH]; intros kname tv H Hk Ht; cbn [pj_set_model].
  - constructor; [split; assumption|constructor].
  - apply Forall_cons_iff in H as [[H1 H2] H3].
    destruct (list_eq_dec Z.eq_dec k kname).
    + constructor; [split; assumption|exact H3].
    + constructor; [split; assumption|apply IH; assumption].
Qed.

Inductive pj_wf : jv -> Prop :=
| wf_read : forall x t, json_read sm x = Some t -> pj_wf t
| wf_object : pj_wf (JObj [])
| wf_string : forall cs, Forall (fun b => 0 < b < 256) cs -> pj_wf (JStr cs)
| wf_set : forall ms kname tv, pj_wf (JObj ms) -> pj_wf tv -> Forall (fun b => 0 < b < 256) kname ->
    (depth (JObj (pj_set_model ms kname tv)) <= MAXD)%nat -> pj_wf (JObj (pj_set_model ms kname tv))
| wf_item : forall items u, pj_wf (JArr items) -> In u items -> pj_wf u
| wf_member : forall ms k u, pj_wf (JObj ms) -> In (k, u) ms -> pj_wf u.

Lemma wf_good : forall t, pj_wf t -> good t /\ (depth t <= MAXD)%nat.
Proof.
  induction 1 as [x t H | | cs H | ms kname tv _ [G1 _] _ [G2 _] Hk Hd | items u _ [G Hd] Hin | ms k u _ [G Hd] Hin].
  - destruct (read_json x t H) as (A & B & _). auto.
  - split; [exact I|]. cbn [depth map list_max fold_right]. unfold MAXD. lia.
  - split; [|cbn [depth]; unfold MAXD; lia]. cbn [good]. unfold strok. eapply Forall_impl; [|exact H]. intros b [Hb _]. exact Hb.
  - split; [|exact Hd]. apply good_obj, set_good; [apply good_obj; exact G1| |exact G2].
    unfold strok. eapply Forall_impl; [|exact Hk]. intros b [Hb _]. exact Hb.
  - apply good_arr in G. rewrite Forall_forall in G. split; [exact (G u Hin)|].
    pose proof (depth_item items u Hin). lia.
  - apply good_obj in G. rewrite Forall_forall in G. split; [exact (proj2 (G (k, u) Hin))|].
    pose proof (depth_member ms k u Hin). lia.
Qed.

Lemma jr_value_wdoc : forall t, pj_wf t -> forall p,
  jr_value sm 0 (wdoc t p) [] = (Some (t, if p then [10] else []), ttrace t, []).
Proof.
  intros t Hw p. destruct (wf_good t Hw) as [Hg Hd].
  assert (Hdoc : wdoc t p = concat (wvpieces t p 0) ++ (if p then [10] else [])).
  { unfold wdoc, wdpieces. rewrite concat_app. destruct p; reflexivity. }
  unfold jr_value. rewrite Hdoc.
  exact (rt_value t Hg p 0 0%nat ltac:(lia) (if p then [10] else [])
    (S (2 * length (concat (wvpieces t p 0) ++ (if p then [10] else []))))
    ltac:(destruct p; [exact eq_refl|exact I]) ltac:(lia)).
Qed.

Theorem G9 : forall t, pj_wf t -> forall p, json_read sm (wdoc t p) = Some t.
Proof.
  intros t Hw p. unfold json_read, jr_run. rewrite (jr_value_wdoc t Hw p). destruct p; reflexivity.
Qed.

Theorem G9_trace : forall t, pj_wf t -> forall p, snd (jr_run sm (wdoc t p) []) = ttrace t.
Proof. intros t Hw p. unfold jr_run. rewrite (jr_value_wdoc t Hw p). destruct p; reflexivity. Qed.

Theorem G9_read : forall x t, json_read sm x = Some t -> forall p, json_read sm (wdoc t p) = Some t.
Proof. intros x t H. apply G9. exact (wf_read x t H). Qed.

Fixpoint mr (c : nat) (x : list Z) : nat :=
  match x with
  | [] => c
  | b :: r => if numch b then mr (S c) r else Nat.max c (mr 0 r)
  end.

Definition maxrun (x : list Z) : nat := mr 0 x.

Definition nn (z : list Z) : Prop := forallb (fun b => negb (numch b)) z = true.

Lemma mr_ge : forall x c, (c <= mr c x)%nat.
Proof.
  induction x as [|b r IH]; intros c; cbn [mr]; [lia|].
  destruct (numch b); [specialize (IH (S c)); lia|lia].
Qed.

Lemma mr_mono : forall x c c', (c <= c')%nat -> (mr c x <= mr c' x)%nat.
Proof.
  induction x as [|b r IH]; intros c c' H; cbn [mr]; [lia|].
  destruct (numch b); [apply IH; lia|lia].
Qed.

Lemma mr_len : forall x c, (mr c x <= c + length x)%nat.
Proof.
  induction x as [|b r IH]; intros c; cbn [mr length]; [lia|].
  destruct (numch b); [specialize (IH (S c)); lia|specialize (IH 0%nat); lia].
Qed.

Lemma mr_step : forall a X c, (mr c (a :: X) <= mr (S c) X)%nat.
Proof.
  intros a X c. cbn [mr]. destruct (numch a); [lia|].
  pose proof (mr_ge X (S c)). pose proof (mr_mono X 0 (S c)). lia.
Qed.

Lemma mr_cons_nn : forall b X c, numch b = false -> mr c (b :: X) = Nat.max c (mr 0 X).
Proof. intros b X c H. cbn [mr]. rewrite H. reflexivity. Qed.

Lemma mr_app_safe : forall U R c, safe R -> mr c (U ++ R) = Nat.max (mr c U) (mr 0 R).
Proof.
  induction U as [|b U IH]; intros R c H; cbn [app mr].
  - destruct R as [|s R]; cbn [mr]; [lia|]. cbn [safe] in H. rewrite H. pose proof (mr_ge R 0). lia.
  - destruct (numch b); [apply IH; exact H|rewrite IH by exact H; lia].
Qed.

Lemma mr_nn : forall z X, nn z -> mr 0 (z ++ X) = mr 0 X.
Proof.
  induction z as [|b z IH]; intros X H; [reflexivity|].
  unfold nn in H. cbn [forallb] in H. apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H1.
  cbn [app]. rewrite mr_cons_nn by exact H1. rewrite IH by exact H2. lia.
Qed.

Lemma ws_nonum : forall b, ws b = true -> numch b = false.
Proof.
  intros b H. unfold ws in H. zr.
  destruct (b =? 32) eqn:E1; [zr; subst; reflexivity|].
  destruct (b =? 9) eqn:E2; [zr; subst; reflexivity|].
  destruct (b =? 10) eqn:E3; [zr; subst; reflexivity|].
  destruct (b =? 13) eqn:E4; [zr; subst; reflexivity|].
  cbn [orb] in H. discriminate.
Qed.

Lemma ws_nn : forall z, forallb ws z = true -> nn z.
Proof.
  unfold nn. induction z as [|b z IH]; intros H; [reflexivity|].
  cbn [forallb] in *. apply andb_true_iff in H as [H1 H2]. rewrite (ws_nonum b H1), (IH H2). reflexivity.
Qed.

Lemma esc_mr : forall v X c, (mr c (esc v ++ X) <= Nat.max c (mr 4 X))%nat.
Proof.
  intros v X c. pose proof (mr_mono X 0 4) as M04. pose proof (mr_mono X 1 4) as M14. unfold esc.
  destruct (v =? 34); [cbn; lia|].
  destruct (v =? 92); [cbn; lia|].
  destruct (v =? 10); [cbn; lia|].
  destruct (v =? 9); [cbn; lia|].
  destruct (v =? 13); [cbn; lia|].
  set (h1 := hexd (v / 16)). set (h2 := hexd (v mod 16)).
  change (mr c ([92; 117; 48; 48; h1; h2] ++ X)) with (Nat.max c (Nat.max 0 (mr 2 (h1 :: h2 :: X)))).
  pose proof (mr_step h1 (h2 :: X) 2). pose proof (mr_step h2 X 3). lia.
Qed.

Lemma mr_E : forall s c, (mr c (flat_map ech s) <= Nat.max c 3 + length s)%nat.
Proof.
  induction s as [|v s IH]; intros c; cbn [flat_map length]; [cbn [mr]; lia|].
  change (ech v) with (if special v then esc v else [v]). destruct (special v).
  - pose proof (esc_mr v (flat_map ech s) c). specialize (IH 4%nat). lia.
  - cbn [app mr]. destruct (numch v); [specialize (IH (S c)); lia|specialize (IH 0%nat); lia].
Qed.

Lemma mr_str : forall s, (maxrun (concat (spieces s)) <= length s + 3)%nat.
Proof.
  intros s. unfold maxrun. rewrite wstr_eq, mr_cons_nn by reflexivity.
  rewrite mr_app_safe by exact eq_refl. change (mr 0 [34]) with 0%nat. pose proof (mr_E s 0). lia.
Qed.

Lemma go_arr_bound : forall p d B items i R,
  Forall (fun u => (maxrun (concat (wvpieces u p (d + 1))) <= B)%nat) items ->
  safe R -> (mr 0 R <= B)%nat -> (mr 0 (concat (wgo_arr p d i items) ++ R) <= B)%nat.
Proof.
  intros p d B items. induction items as [|u r IH]; intros i R HF HR HB; [exact HB|].
  apply Forall_cons_iff in HF as [Hu HF].
  cbn [wgo_arr]. rewrite !concat_app, <- !app_assoc.
  rewrite mr_nn by (unfold nn, wcomma; destruct (Nat.eqb i 0); reflexivity).
  rewrite mr_nn by apply ws_nn, wind_ws.
  rewrite mr_app_safe by (destruct r; [exact HR|exact eq_refl]).
  specialize (IH (S i) R HF HR HB). unfold maxrun in Hu. lia.
Qed.

Lemma go_obj_bound : forall p d K items i R,
  Forall (fun m => (length (fst m) <= K)%nat /\ (maxrun (concat (wvpieces (snd m) p (d + 1))) <= K + 3)%nat) items ->
  safe R -> (mr 0 R <= K + 3)%nat -> (mr 0 (concat (wgo_obj p d i items) ++ R) <= K + 3)%nat.
Proof.
  intros p d K items. induction items as [|[k u] r IH]; intros i R HF HR HB; [exact HB|].
  apply Forall_cons_iff in HF as [[Hk Hu] HF]. cbn [fst snd] in Hk, Hu.
  cbn [wgo_obj]. rewrite !concat_app, <- !app_assoc.
  rewrite mr_nn by (unfold nn, wcomma; destruct (Nat.eqb i 0); reflexivity).
  rewrite mr_nn by apply ws_nn, wind_ws.
  rewrite wstr_eq, <- app_comm_cons. rewrite mr_cons_nn by reflexivity. rewrite <- app_assoc.
  rewrite mr_app_safe by exact eq_refl. cbn [app]. rewrite (mr_cons_nn 34) by reflexivity.
  rewrite mr_nn by (unfold nn; destruct p; reflexivity).
  rewrite mr_app_safe by (destruct r as [|[]]; [exact HR|exact eq_refl]).
  specialize (IH (S i) R HF HR HB). unfold maxrun in Hu. pose proof (mr_E k 0). lia.
Qed.

Lemma mr_value : forall t K p d, tlen K t -> (maxrun (concat (wvpieces t p d)) <= K + 3)%nat.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros K p d H.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - cbn [wvpieces concat tlen] in *. unfold maxrun. rewrite app_nil_r. pose proof (mr_len txt 0). lia.
  - cbn [wvpieces tlen] in *. pose proof (mr_str s). lia.
  - apply tlen_arr in H. unfold maxrun.
    rewrite <- (app_nil_r (concat (wvpieces (JArr items) p d))), arr_text. rewrite mr_cons_nn by reflexivity.
    assert (HC : nn (concat (match items with [] => [] | _ :: _ => wind p d end)))
      by (destruct items; [reflexivity|apply ws_nn, wind_ws]).
    pose proof (go_arr_bound p d (K + 3) items 0 (concat (match items with [] => [] | _ :: _ => wind p d end) ++ [93])) as G.
    rewrite mr_nn in G by exact HC.
    assert (G1 : (mr 0 (concat (wgo_arr p d 0 items) ++ concat (match items with [] => [] | _ :: _ => wind p d end) ++ [93%Z])
      <= K + 3)%nat).
    { apply G.
      - rewrite Forall_forall in *. intros u Hu. exact (IH u Hu K p (d + 1) (H u Hu)).
      - destruct items; [exact eq_refl|exact (wind_safe p d [] 93 eq_refl)].
      - cbn. lia. }
    lia.
  - apply tlen_obj in H. unfold maxrun.
    rewrite <- (app_nil_r (concat (wvpieces (JObj ms) p d))), obj_text. rewrite mr_cons_nn by reflexivity.
    assert (HC : nn (concat (match ms with [] => [] | _ :: _ => wind p d end)))
      by (destruct ms; [reflexivity|apply ws_nn, wind_ws]).
    pose proof (go_obj_bound p d K ms 0 (concat (match ms with [] => [] | _ :: _ => wind p d end) ++ [125])) as G.
    rewrite mr_nn in G by exact HC.
    assert (G1 : (mr 0 (concat (wgo_obj p d 0 ms) ++ concat (match ms with [] => [] | _ :: _ => wind p d end) ++ [125%Z])
      <= K + 3)%nat).
    { apply G.
      - rewrite Forall_forall in *. intros m Hm. destruct (H m Hm) as [H1 H2].
        split; [exact H1|exact (IH m Hm K p (d + 1) H2)].
      - destruct ms; [exact eq_refl|exact (wind_safe p d [] 125 eq_refl)].
      - cbn. lia. }
    lia.
Qed.

Theorem G12_1 : forall x, (maxrun x <= length x)%nat.
Proof. intros x. exact (mr_len x 0). Qed.

Theorem G12_2 : forall t p K, tlen K t -> (maxrun (wdoc t p) <= K + 3)%nat.
Proof.
  intros t p K H. unfold wdoc, wdpieces, maxrun. rewrite concat_app.
  rewrite mr_app_safe by (destruct p; [exact eq_refl|exact I]).
  pose proof (mr_value t K p 0 H) as V. unfold maxrun in V.
  assert (mr 0 (concat (if p then [[10]] else [])) = 0%nat) by (destruct p; reflexivity). lia.
Qed.

Theorem G12_read_len : forall x t, json_read sm x = Some t -> tlen (length x) t.
Proof. intros x t H. exact (proj2 (proj2 (read_json x t H))). Qed.

Theorem G12_read : forall x t p, json_read sm x = Some t -> (maxrun (wdoc t p) <= length x + 3)%nat.
Proof. intros x t p H. exact (G12_2 t p (length x) (G12_read_len x t H)). Qed.

Lemma lsum_cons : forall (a : nat) l, list_sum (a :: l) = (a + list_sum l)%nat.
Proof. reflexivity. Qed.

Lemma lsum_app : forall l m, list_sum (l ++ m) = (list_sum l + list_sum m)%nat.
Proof. induction l as [|a l IH]; intros m; [reflexivity|]. cbn [app]. rewrite !lsum_cons, IH. lia. Qed.

Lemma lsum_rev : forall l, list_sum (rev l) = list_sum l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [rev]. rewrite lsum_app, IH, lsum_cons, lsum_cons.
  change (list_sum []) with 0%nat. lia.
Qed.

Fixpoint ngrow (k n cap : nat) : nat :=
  match k with
  | O => O
  | S k' => ((if Nat.ltb n cap then 0 else 1) + ngrow k' (S n) (gcap n cap))%nat
  end.

Fixpoint tcalls (t : jv) : nat :=
  match t with
  | JNum _ _ => 1%nat
  | JStr _ => 1%nat
  | JArr items => (ngrow (length items) 0 0 + list_sum (map tcalls items))%nat
  | JObj ms => (2 * ngrow (length ms) 0 0 + length ms + list_sum (map (fun '(_, u) => tcalls u) ms))%nat
  | _ => 0%nat
  end.

Fixpoint nnames (t : jv) : nat :=
  match t with
  | JArr items => list_sum (map nnames items)
  | JObj ms => (length ms + list_sum (map (fun '(_, u) => nnames u) ms))%nat
  | _ => 0%nat
  end.

Fixpoint tblocks (t : jv) : nat :=
  match t with
  | JNum _ _ => 1%nat
  | JStr _ => 1%nat
  | JArr items => ((match items with [] => 0 | _ :: _ => 1 end) + list_sum (map tblocks items))%nat
  | JObj ms => ((match ms with [] => 0 | _ :: _ => 2 end) + length ms +
      list_sum (map (fun '(_, u) => tblocks u) ms))%nat
  | _ => 0%nat
  end.

Lemma calls_grow_ev : forall o n cap,
  calls (grow_ev o n cap) = (if Nat.ltb n cap then 0 else if o then 2 else 1)%nat.
Proof. intros o n cap. unfold grow_ev. destruct (Nat.ltb n cap); [reflexivity|]. destruct o; reflexivity. Qed.

Lemma calls_tgo_arr : forall l n cap, Forall (fun u => calls (ttrace u) = tcalls u) l ->
  calls (tgo_arr n cap l) = (ngrow (length l) n cap + list_sum (map tcalls l))%nat.
Proof.
  induction l as [|u r IH]; intros n cap H; [reflexivity|].
  apply Forall_cons_iff in H as [H1 H2].
  cbn [tgo_arr length ngrow map]. rewrite lsum_cons.
  rewrite !calls_app, calls_grow_ev, H1, (IH (S n) (gcap n cap) H2).
  destruct (Nat.ltb n cap); lia.
Qed.

Lemma calls_tgo_obj : forall l n cap, Forall (fun m => calls (ttrace (snd m)) = tcalls (snd m)) l ->
  calls (tgo_obj n cap l) =
    (2 * ngrow (length l) n cap + length l + list_sum (map (fun '(_, u) => tcalls u) l))%nat.
Proof.
  induction l as [|[k u] r IH]; intros n cap H; [reflexivity|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [fst snd] in H1.
  cbn [tgo_obj length ngrow map]. rewrite lsum_cons.
  rewrite calls_app, calls_grow_ev. cbn [calls is_call].
  rewrite calls_app, H1, (IH (S n) (gcap n cap) H2).
  destruct (Nat.ltb n cap); lia.
Qed.

Lemma tcalls_trace : forall t, calls (ttrace t) = tcalls t.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; try reflexivity.
  - rewrite tt_arr. cbn [tcalls]. apply calls_tgo_arr. exact IH.
  - rewrite tt_obj. cbn [tcalls]. apply calls_tgo_obj. exact IH.
Qed.

Lemma ngrow_le : forall k n cap, (ngrow k n cap <= k)%nat.
Proof.
  induction k as [|k IH]; intros n cap; cbn [ngrow]; [lia|].
  specialize (IH (S n) (gcap n cap)). destruct (Nat.ltb n cap); lia.
Qed.

Lemma tb_arr : forall l : list jv, Forall (fun u => (tcalls u + 2 <= 3 * (size u + nnames u))%nat) l ->
  (list_sum (map tcalls l) + 2 * length l <= 3 * (list_sum (map size l) + list_sum (map nnames l)))%nat.
Proof.
  induction l as [|u r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [map length]. rewrite !lsum_cons. specialize (IH H2). lia.
Qed.

Lemma tb_obj : forall l : list (list Z * jv), Forall (fun m => (tcalls (snd m) + 2 <= 3 * (size (snd m) + nnames (snd m)))%nat) l ->
  (list_sum (map (fun '(_, u) => tcalls u) l) + 2 * length l <=
   3 * (list_sum (map (fun '(_, v) => size v) l) + list_sum (map (fun '(_, u) => nnames u) l)))%nat.
Proof.
  induction l as [|[k u] r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [fst snd] in H1. cbn [map length]. rewrite !lsum_cons.
  specialize (IH H2). lia.
Qed.

Lemma tcalls_bound : forall t, (tcalls t + 2 <= 3 * (size t + nnames t))%nat.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; try (cbn; lia).
  - cbn [tcalls size nnames]. pose proof (tb_arr items IH). pose proof (ngrow_le (length items) 0 0). lia.
  - cbn [tcalls size nnames]. pose proof (tb_obj ms IH). pose proof (ngrow_le (length ms) 0 0). lia.
Qed.

Theorem G9_calls : forall t, pj_wf t -> forall p, ncalls sm (wdoc t p) = tcalls t.
Proof. intros t Hw p. unfold ncalls. rewrite (G9_trace t Hw p). apply tcalls_trace. Qed.

Theorem G9_calls_bound : forall t, pj_wf t -> forall p,
  (ncalls sm (wdoc t p) + 2 <= 3 * (size t + nnames t))%nat.
Proof. intros t Hw p. rewrite (G9_calls t Hw p). apply tcalls_bound. Qed.

Definition accb (o : bool) (L : list (list Z * jv)) : nat :=
  (list_sum (map (fun '(_, u) => tblocks u) L) + (if o then length L else 0))%nat.

Lemma accb_cons : forall o k v L, accb o ((k, v) :: L) = (tblocks v + (if o then 1 else 0) + accb o L)%nat.
Proof. intros o k v L. unfold accb. cbn [map length]. rewrite lsum_cons. destruct o; lia. Qed.

Lemma accb_rev_snoc : forall o L k v, accb o (rev L ++ [(k, v)]) = (accb o L + tblocks v + (if o then 1 else 0))%nat.
Proof.
  intros o L k v. unfold accb. rewrite map_app, lsum_app, map_rev, lsum_rev, length_app, length_rev.
  cbn [map length list_sum fold_right]. destruct o; lia.
Qed.

Lemma tblocks_mk : forall o L, L <> [] -> tblocks (mk o L) = (1 + (if o then 1 else 0) + accb o L)%nat.
Proof.
  intros o L H. unfold mk, accb. destruct L as [|m L']; [contradiction|]. destruct o.
  - cbn [tblocks]. lia.
  - cbn [tblocks map]. rewrite lsum_cons, lsum_cons.
    replace (list_sum (map tblocks (map snd L'))) with (list_sum (map (fun '(_, u) => tblocks u) L')).
    + destruct m. cbn [snd]. lia.
    + rewrite map_map. f_equal. apply map_ext. intros [k u]. reflexivity.
Qed.

Lemma lit_blocks : forall w v x ok t r tr ok', w <> [] -> (v = JTrue \/ v = JFalse \/ v = JNull) ->
  lit w v x ok = (Some (t, r), tr, ok') -> tblocks t = 0%nat /\ (length r < length x)%nat.
Proof.
  intros w v x ok t r tr ok' Hw Hv H. pose proof (lit_spec w v x ok Hw) as Hs. rewrite H in Hs.
  destruct Hs as [_ Hr]. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as <- _ _ _. split; [destruct Hv as [-> | [-> | ->]]; reflexivity|exact Hr].
Qed.

Lemma cont_blocks : forall f d o b y ok t r tr ok',
  (forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     (3 * tblocks t + 2 * length r <= 2 * length y + 2 + 3 * accb o acc)%nat) ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (t, r), tr, ok') ->
  (3 * tblocks t + 2 * length r <= 2 * length (b :: y))%nat.
Proof.
  intros f d o b y ok t r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H. pose proof (skip_len y) as Hy. cbn [length].
  assert (Ha : accb o [] = 0%nat) by (unfold accb; destruct o; reflexivity).
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  - pose proof (IHl _ _ _ _ _ _ _ _ _ _ _ H) as E. rewrite Ha in E. cbn [length] in E. lia.
  - destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as <- <- _ _. cbn [length] in Hy.
      assert (tblocks (mk o []) = 0%nat) by (destruct o; reflexivity). lia.
    + pose proof (IHl _ _ _ _ _ _ _ _ _ _ _ H) as E. rewrite Ha in E. lia.
Qed.

Lemma blocks_fuel : forall f,
  (forall d x ok t r tr ok', jrv sm f d x ok = (Some (t, r), tr, ok') ->
     (3 * tblocks t + 2 * length r <= 2 * length x + 1)%nat) /\
  (forall d o n cap acc y ok t r tr ok', jrl sm f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     (3 * tblocks t + 2 * length r <= 2 * length y + 2 + 3 * accb o acc)%nat).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      pose proof (skip_len x) as Hsx.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123); cbv beta iota in H.
      { pose proof (cont_blocks f d true b y ok t r tr ok' IHl H). lia. }
      destruct (b =? 91); cbv beta iota in H.
      { pose proof (cont_blocks f d false b y ok t r tr ok' IHl H). lia. }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
        pose proof (jr_string_spec y ok) as Hs. rewrite Hj in Hs. destruct Hs as (q & _ & _ & _ & Hl).
        cbv beta iota in H. unfold jret in H. injection H as <- <- _ _.
        cbn [tblocks]. cbn [length] in Hsx. lia. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (lit_blocks w_true JTrue _ _ _ _ _ _ ltac:(unfold w_true; discriminate) (or_introl eq_refl) H) as [A B]. lia. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (lit_blocks w_false JFalse _ _ _ _ _ _ ltac:(unfold w_false; discriminate) (or_intror (or_introl eq_refl)) H) as [A B]. lia. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (lit_blocks w_null JNull _ _ _ _ _ _ ltac:(unfold w_null; discriminate) (or_intror (or_intror eq_refl)) H) as [A B]. lia. }
      pose proof (jr_number_spec sm (b :: y) ok ltac:(discriminate)) as Hn. rewrite H in Hn.
      destruct Hn as (k & _ & Hk & Hkr).
      destruct (jr_number_good _ _ _ _ _ _ H) as (txt & -> & _).
      cbn [tblocks]. lia.
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (IHv d y1 ok2 v r0 tv ok3 Ev) as Bv.
      assert (Hy1 : (length y1 + (if o then 3 else 0) <= length y)%nat).
      { pose proof (jr_name_spec o y ok1) as Hn. rewrite En in Hn.
        destruct o; [destruct Hn as (q & _ & Hq); lia|destruct Hn as [_ ->]; lia]. }
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      destruct (c =? 44); cbv beta iota in H.
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' H) as E.
        rewrite accb_cons in E. destruct o; lia. }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as <- <- _ _.
      cbn [rev]. rewrite tblocks_mk by (intro E; apply app_eq_nil in E; destruct E as [_ E]; discriminate E).
      rewrite accb_rev_snoc. destruct o; lia.
Qed.

Theorem tblocks_read3 : forall x t, json_read sm x = Some t -> (3 * tblocks t <= 2 * length x + 1)%nat.
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. pose proof (proj1 (blocks_fuel _) 0%nat x [] t' r tr ok' E). lia.
Qed.

Theorem tblocks_read : forall x t, json_read sm x = Some t -> (tblocks t <= length x)%nat.
Proof.
  intros x t H. pose proof (tblocks_read3 x t H) as B.
  unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  pose proof (jr_value_rest sm 0 x [] t' r tr ok' E). lia.
Qed.

End RoundTrip.
