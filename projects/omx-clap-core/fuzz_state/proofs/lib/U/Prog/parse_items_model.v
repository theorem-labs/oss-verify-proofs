From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint okf (c f : Z) (n : nat) : list bool :=
  match n with
  | O => []
  | S n' => negb (c =? f) :: okf (c + 1) f n'
  end.

Lemma okf_nth : forall n c f i, (i < n)%nat -> nth i (okf c f n) true = negb (c + Z.of_nat i =? f).
Proof.
  induction n as [|n IH]; intros c f i H; [lia|].
  destruct i as [|i]; cbn [okf nth].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. do 2 f_equal. lia.
Qed.

Lemma okf_skipn : forall n c f k, skipn k (okf c f n) = okf (c + Z.of_nat k) f (n - k).
Proof.
  induction n as [|n IH]; intros c f k.
  - rewrite skipn_nil. reflexivity.
  - destruct k as [|k]; cbn [skipn okf].
    + rewrite Z.add_0_r. reflexivity.
    + rewrite IH. replace (c + 1 + Z.of_nat k) with (c + Z.of_nat (S k)) by lia. reflexivity.
Qed.

Lemma okf_cons : forall n c f, (1 <= n)%nat -> okf c f n = negb (c =? f) :: okf (c + 1) f (n - 1).
Proof. intros [|n] c f H; [lia|]. cbn [okf]. replace (S n - 1)%nat with n by lia. reflexivity. Qed.

Lemma split_call_uniq : forall P E R P' E' R', P ++ E :: R = P' ++ E' :: R' ->
  calls P = calls P' -> is_call E = true -> is_call E' = true -> P = P' /\ E = E'.
Proof.
  induction P as [|x P IH]; intros E R P' E' R' H Hc HE HE'; destruct P' as [|y P']; cbn [app calls] in *.
  - injection H as -> _. auto.
  - injection H as Hy _. subst y. rewrite HE in Hc. discriminate.
  - injection H as Hx _. subst x. rewrite HE' in Hc. discriminate.
  - injection H as Hxy H'. subst y.
    destruct (is_call x); [injection Hc as Hc|];
      destruct (IH _ _ _ _ _ H' Hc HE HE') as [-> ->]; auto.
Qed.

Lemma agrees_det : forall (A : Type) (m : M A) ok1 ok2 r t o1, agrees m -> m ok1 = (r, t, o1) ->
  (forall i, (i < calls t)%nat -> nth i ok2 true = nth i ok1 true) ->
  m ok2 = (r, t, skipn (calls t) ok2).
Proof.
  intros A m ok1 ok2 r t o1 H E Hag.
  pose proof (agrees_nil A m H) as N0.
  pose proof (proj1 (H ok1)) as K1. pose proof (proj2 (H ok1)) as K1'.
  pose proof (proj1 (H ok2)) as K2. pose proof (proj2 (H ok2)) as K2'.
  destruct (m []) as [[r0 t0] o0] eqn:E0. cbn [fst snd] in *.
  destruct (ok_upto_dec ok1 (calls t0)) as [Hu|(j & Hj & Hf & Hu)].
  - rewrite (K1 Hu) in E. injection E as <- <- _.
    apply K2. intros i Hi. rewrite Hag by exact Hi. apply Hu. exact Hi.
  - destruct (K1' j Hj Hf Hu) as (P & e & rest & Em & Et & Hc & Hic).
    rewrite Em in E. injection E as <- <- _.
    assert (CP : calls (P ++ [EFail (esize e)]) = S j) by (rewrite calls_app; cbn [calls is_call]; lia).
    rewrite CP in Hag |- *.
    assert (Hf2 : nth j ok2 true = false) by (rewrite Hag by lia; exact Hf).
    assert (Hu2 : ok_upto ok2 j) by (intros i Hi; rewrite Hag by lia; apply Hu; exact Hi).
    destruct (K2' j Hj Hf2 Hu2) as (P' & e' & rest' & Em' & Et' & Hc' & Hic').
    rewrite Et in Et'. destruct (split_call_uniq _ _ _ _ _ _ Et' ltac:(lia) Hic Hic') as [<- <-].
    exact Em'.
Qed.

Lemma agrees_some_upto : forall (A : Type) (m : M A) ok a t o, agrees m -> m ok = (Some a, t, o) ->
  ok_upto ok (calls t).
Proof.
  intros A m ok a t o H E.
  destruct (agrees_some A m ok a t o H E) as [E0 _].
  destruct (ok_upto_dec ok (calls t)) as [Hu|(j & Hj & Hf & Hu)]; [exact Hu|].
  pose proof (proj2 (H ok) j) as K. rewrite E0 in K. cbn [fst snd] in K.
  destruct (K Hj Hf Hu) as (P & e & rest & Em & _). rewrite E in Em. discriminate.
Qed.

Definition ext {A : Type} (full : option A * list ev * list bool) (tr : list ev)
    (part : option A * list ev * list bool) : Prop :=
  full = (fst (fst part), tr ++ snd (fst part), snd part).

Lemma ext_bind_some : forall (A B : Type) (full : option B * list ev * list bool) tr (m : M A) (k : A -> M B)
    ok a t1 ok1,
  m ok = (Some a, t1, ok1) -> ext full tr (jbind m k ok) -> ext full (tr ++ t1) (k a ok1).
Proof.
  intros A B full tr m k ok a t1 ok1 E H. unfold ext, jbind in *. rewrite E in H.
  destruct (k a ok1) as [[r t'] o'] eqn:Ek. cbn [fst snd] in *. rewrite <- app_assoc. exact H.
Qed.

Lemma ext_bind_none : forall (A B : Type) (full : option B * list ev * list bool) tr (m : M A) (k : A -> M B)
    ok t1 ok1,
  m ok = (None, t1, ok1) -> ext full tr (jbind m k ok) -> full = (None, tr ++ t1, ok1).
Proof. intros A B full tr m k ok t1 ok1 E H. unfold ext, jbind in *. rewrite E in H. exact H. Qed.

Lemma ext_eq : forall (A : Type) (full : option A * list ev * list bool) tr part r t o,
  part = (r, t, o) -> ext full tr part -> full = (r, tr ++ t, o).
Proof. intros A full tr part r t o -> H. exact H. Qed.

Lemma bind_nil_trace : forall (A B : Type) (m : M A) (k : A -> M B) a t,
  agrees m -> m [] = (Some a, t, []) -> snd (fst (jbind m k [])) = t ++ snd (fst (k a [])).
Proof.
  intros A B m k a t H E. unfold jbind. rewrite E.
  destruct (k a []) as [[r t'] o']. reflexivity.
Qed.

Lemma hpeak_nonneg : forall t, 0 <= hpeak t.
Proof. destruct t; cbn [hpeak]; lia. Qed.

Lemma hpeak_app : forall t1 t2, hpeak (t1 ++ t2) = Z.max (hpeak t1) (held t1 + hpeak t2).
Proof.
  induction t1 as [|e t1 IH]; intros t2; cbn [app hpeak held].
  - pose proof (hpeak_nonneg t2). lia.
  - rewrite IH. lia.
Qed.

Lemma hpeak_le : forall t Bd, 0 <= Bd -> (forall p r, t = p ++ r -> held p <= Bd) -> hpeak t <= Bd.
Proof.
  induction t as [|e t IH]; intros Bd HB H; cbn [hpeak]; [lia|].
  assert (H0 : held_ev e <= Bd) by (pose proof (H [e] t eq_refl) as K; cbn [held] in K; lia).
  assert (H1 : hpeak t <= Bd - held_ev e).
  { apply IH; [lia|]. intros p r E. pose proof (H (e :: p) r ltac:(rewrite E; reflexivity)) as K.
    cbn [held] in K. lia. }
  lia.
Qed.

Section Rf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma rf_run_app : forall F b t1 t2, rf_run F b (t1 ++ t2) = rf_run F (rf_run F b t1) t2.
Proof. intros F b t1 t2. unfold rf_run. apply fold_left_app. Qed.

Lemma rf_run_cons : forall F b e t, rf_run F b (e :: t) = rf_run F (rf_ev F b e) t.
Proof. reflexivity. Qed.

Lemma room_run_app : forall F t1 b t2, room_run F b (t1 ++ t2) -> room_run F b t1 /\ room_run F (rf_run F b t1) t2.
Proof.
  intros F. induction t1 as [|e t1 IH]; intros b t2 H; cbn [app room_run] in *.
  - split; [exact I | exact H].
  - destruct H as [H1 H2]. destruct (IH _ _ H2) as [K1 K2]. split; [split; [exact H1 | exact K1]|].
    rewrite rf_run_cons. exact K2.
Qed.

End Rf.

Lemma fail_after_app : forall cnt fail c t fail',
  ~ (cnt <= fail < cnt + Z.of_nat c) ->
  fail_after (cnt + Z.of_nat c) fail t fail' -> fail_after cnt fail (c + t) fail'.
Proof.
  intros cnt fail c t fail' H0 [H1 H2]. split; intros H.
  - apply H1. lia.
  - apply H2. lia.
Qed.

Lemma fail_after_none : forall cnt fail k, ~ (cnt <= fail < cnt + Z.of_nat k) -> fail_after cnt fail k fail.
Proof. intros cnt fail k H. split; intros H'; [contradiction | reflexivity]. Qed.

Lemma oks_okf : forall N cnt fail k, (k <= N)%nat -> oks (okf cnt fail N) cnt fail k.
Proof. intros N cnt fail k H i Hi. apply okf_nth. lia. Qed.

Definition jturn (d : nat) (o : bool) (n cap : nat) (acc : list (list Z * jv)) (y : list Z) : M (jv * list Z) :=
  jrl jr_strtod (2 * length y + 2) (S d) o n cap acc y.

Definition jtail (d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * jv)) (nm : list Z) (v : jv)
    (r : list Z) : M (jv * list Z) :=
  match skip r with
  | c :: r1 =>
      if c =? 44 then jturn d o (S n) cap1 ((nm, v) :: acc) r1
      else if c =? closer o then jret (mk o (rev ((nm, v) :: acc)), r1) else jrefuse
  | [] => jrefuse
  end.

Definition jval (d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * jv)) (nm y1 : list Z) : M (jv * list Z) :=
  jbind (jr_value jr_strtod (S d) y1) (fun vr => jtail d o n cap1 acc nm (fst vr) (snd vr)).

Definition jafter (d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * jv)) (y : list Z) : M (jv * list Z) :=
  jbind (jr_name o y) (fun ny => jval d o n cap1 acc (fst ny) (snd ny)).

Lemma jturn_eq : forall d o n cap acc y ok,
  jturn d o n cap acc y ok = jbind (grow o n cap) (fun cap1 => jafter d o n cap1 acc y) ok.
Proof.
  intros d o n cap acc y ok. unfold jturn.
  replace (2 * length y + 2)%nat with (S (2 * length y + 1)) by lia. cbn [jrl].
  unfold jafter, jval, jtail, jbind.
  destruct (grow o n cap ok) as [[[cap1|] tg] ok1]; [|reflexivity].
  pose proof (jr_name_spec o y ok1) as Hn.
  destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2] eqn:En; [|reflexivity]. cbn [fst snd].
  assert (Hy1 : (length y1 <= length y)%nat)
    by (destruct o; cbv iota in Hn; [destruct Hn as (q & _ & Hq); lia | destruct Hn as [_ ->]; lia]).
  rewrite (jr_value_fuel jr_strtod) by lia.
  pose proof (vspec_jr_value jr_strtod (S d) y1 ok2) as Hv.
  destruct (jr_value jr_strtod (S d) y1 ok2) as [[[[v r]|] tv] ok3] eqn:Ev; [|reflexivity]. cbn [fst snd].
  unfold vspec in Hv. cbn [fst snd] in Hv. destruct Hv as (_ & _ & Hv).
  destruct (Hv v r eq_refl) as (Hr & _ & _).
  pose proof (skip_len r) as Hsr.
  destruct (skip r) as [|c r1] eqn:Er; [reflexivity|]. cbn [length] in Hsr.
  destruct (c =? 44); [|reflexivity].
  rewrite (proj2 (fuel_mono jr_strtod (2 * length r1 + 2)%nat) (S d) o (S n) cap1 ((nm, v) :: acc) r1
             (2 * length y + 1)%nat ok3) by lia.
  reflexivity.
Qed.

Lemma jr_items_deep : forall d o x ok, (MAXD < S d)%nat -> jr_items jr_strtod d o x ok = (None, [], ok).
Proof.
  intros d o x ok H. unfold jr_items, jr_cont. replace (Nat.ltb MAXD (S d)) with true by (symmetry; apply Nat.ltb_lt; exact H).
  reflexivity.
Qed.

Lemma jr_items_eq : forall d o b y ok, (S d <= MAXD)%nat ->
  jr_items jr_strtod d o (b :: y) ok =
  match skip y with
  | c :: r => if c =? closer o then jret (mk o [], r) ok else jturn d o 0 0 [] (skip y) ok
  | [] => jturn d o 0 0 [] [] ok
  end.
Proof.
  intros d o b y ok H. unfold jr_items, jr_cont.
  replace (Nat.ltb MAXD (S d)) with false by (symmetry; apply Nat.ltb_ge; exact H).
  cbn [tl]. pose proof (skip_len y) as Hs. unfold jturn.
  destruct (skip y) as [|c r] eqn:Ey.
  - apply (proj2 (fuel_mono jr_strtod (2 * length (@nil Z) + 2))); cbn [length]; lia.
  - destruct (c =? closer o); [reflexivity|].
    apply (proj2 (fuel_mono jr_strtod (2 * length (c :: r) + 2))); cbn [length] in *; lia.
Qed.
