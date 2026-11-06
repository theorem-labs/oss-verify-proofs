From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes PvDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require literal_c strtod_c.
Import ListNotations.
Open Scope Z_scope.

Section Model.
Variable f : list Z -> Z * Z.

Lemma jr_value_unfold : forall d x ok, jr_value f d x ok =
  match skip x with
  | [] => (None, [], ok)
  | b :: y =>
      if b =? 123 then jr_items f d true (b :: y) ok
      else if b =? 91 then jr_items f d false (b :: y) ok
      else if b =? 34 then jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)) ok
      else if b =? 116 then lit w_true JTrue (b :: y) ok
      else if b =? 102 then lit w_false JFalse (b :: y) ok
      else if b =? 110 then lit w_null JNull (b :: y) ok
      else jr_number f (b :: y) ok
  end.
Proof.
  intros d x ok. unfold jr_value. cbn [jrv].
  pose proof (skip_len x) as Hs.
  destruct (skip x) as [|b y] eqn:E; [reflexivity|].
  cbn [length] in Hs.
  assert (C : forall o, jr_cont (jrl f (2 * length x)) d o (b :: y) ok = jr_items f d o (b :: y) ok).
  { intros o. unfold jr_items, jr_cont. destruct (Nat.ltb MAXD (S d)); [reflexivity|]. cbn [tl].
    pose proof (skip_len y) as Hy.
    assert (E1 : forall ok', jrl f (2 * length x) (S d) o 0 0 [] (skip y) ok' =
                             jrl f (2 * length (skip y) + 2) (S d) o 0 0 [] (skip y) ok')
      by (intros ok'; apply (proj2 (fuel_mono f (2 * length (skip y) + 2))); lia).
    assert (E2 : forall ok', jrl f (2 * length (b :: y) + 2) (S d) o 0 0 [] (skip y) ok' =
                             jrl f (2 * length (skip y) + 2) (S d) o 0 0 [] (skip y) ok')
      by (intros ok'; apply (proj2 (fuel_mono f (2 * length (skip y) + 2))); cbn [length]; lia).
    destruct (skip y) as [|c r] eqn:Ey.
    - rewrite E1, E2. reflexivity.
    - destruct (c =? closer o); [reflexivity|]. rewrite E1, E2. reflexivity. }
  destruct (b =? 123); [apply C|].
  destruct (b =? 91); [apply C|].
  destruct (b =? 34); [reflexivity|]. destruct (b =? 116); [reflexivity|].
  destruct (b =? 102); [reflexivity|]. destruct (b =? 110); reflexivity.
Qed.

Lemma jr_number_tok : forall x ok, jr_number f x ok =
  match num_tok x with
  | None => (None, [], ok)
  | Some (txt, r) =>
      let (b, ok1) := take ok in
      if b then
        (if whole f txt then (Some (JNum txt (snd (f txt)), r), [EAlloc (S (length txt))], ok1)
         else (None, [EAlloc (S (length txt))], ok1))
      else (None, [EFail (S (length txt))], ok1)
  end.
Proof.
  intros x ok. unfold jr_number, num_tok.
  destruct (skipn _ x) as [|c z]; [reflexivity|].
  destruct (negb (digit c)); [reflexivity|].
  destruct (_ && _); [reflexivity|].
  destruct (span numch z) as [a r].
  unfold jbind, jalloc, jret, jrefuse. destruct ok as [|b ok1]; cbn [take].
  - destruct (whole f _); reflexivity.
  - destruct b; [|reflexivity]. destruct (whole f _); reflexivity.
Qed.

Lemma jr_string_unfold : forall y ok,
  jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)) ok =
  match scan y with
  | None => (None, [], ok)
  | Some q =>
      let (b, ok1) := take ok in
      if b then
        match decode y with
        | Some (s, r) => (Some (JStr s, r), [EAlloc (S q)], ok1)
        | None => (None, [EAlloc (S q); EFree (S q)], ok1)
        end
      else (None, [EFail (S q)], ok1)
  end.
Proof.
  intros y ok. unfold jr_string.
  destruct (scan y) as [q|]; [|reflexivity].
  unfold jbind, jalloc, jret, jrefuse, jfree. destruct ok as [|b ok1]; cbn [take].
  - destruct (decode y) as [[s r]|]; reflexivity.
  - destruct b; [|reflexivity]. destruct (decode y) as [[s r]|]; reflexivity.
Qed.

Lemma lit_unfold : forall w v x ok,
  lit w v x ok = if prefixb w x then (Some (v, skipn (length w) x), [], ok) else (None, [], ok).
Proof. intros w v x ok. unfold lit. destruct (prefixb w x); reflexivity. Qed.

End Model.

Lemma span_numch : forall z a r, span numch z = (a, r) ->
  z = a ++ r /\ Forall (fun c => numch c = true) a /\ match r with c :: _ => numch c = false | [] => True end.
Proof.
  induction z as [|b z IH]; intros a r H; cbn [span] in H.
  - injection H as <- <-. split; [reflexivity|]. split; [constructor | exact I].
  - destruct (numch b) eqn:Eb.
    + destruct (span numch z) as [a' r'] eqn:E. injection H as <- <-.
      destruct (IH a' r' eq_refl) as (H1 & H2 & H3). subst z.
      split; [reflexivity|]. split; [constructor; assumption | exact H3].
    + injection H as <- <-. split; [reflexivity|]. split; [constructor | exact Eb].
Qed.

Lemma num_tok_some : forall x txt r, num_tok x = Some (txt, r) ->
  x = txt ++ r /\ Forall (fun c => numch c = true) txt /\ (1 <= length txt)%nat /\
  match r with c :: _ => numch c = false | [] => True end.
Proof.
  intros x txt r H. unfold num_tok in H.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end) in H.
  assert (Hj : firstn j x = match x with b :: _ => if b =? 45 then [45] else [] | [] => [] end /\
               Forall (fun c => numch c = true) (firstn j x)).
  { unfold j. destruct x as [|b x']; [split; [reflexivity | constructor]|].
    destruct (b =? 45) eqn:E; cbn [firstn].
    - apply Z.eqb_eq in E. subst b. split; [reflexivity|]. constructor; [reflexivity | constructor].
    - split; [reflexivity | constructor]. }
  destruct (skipn j x) as [|c z] eqn:Es; [discriminate|].
  destruct (negb (digit c)) eqn:Ed; [discriminate|].
  destruct (_ && _); [discriminate|].
  destruct (span numch z) as [a r'] eqn:Esp. injection H as <- <-.
  destruct (span_numch z a r' Esp) as (Z1 & Z2 & Z3).
  apply negb_false_iff in Ed.
  split.
  { rewrite <- (firstn_skipn j x) at 1. rewrite Es, Z1. rewrite <- app_assoc. reflexivity. }
  split.
  { apply Forall_app. split; [exact (proj2 Hj)|]. constructor; [|exact Z2].
    unfold numch. rewrite Ed. reflexivity. }
  split; [rewrite length_app; cbn [length]; lia | exact Z3].
Qed.

Lemma mr_cons_ge : forall b X c, (PjRoundTrip.mr 0 X <= PjRoundTrip.mr c (b :: X))%nat.
Proof.
  intros b X c. cbn [PjRoundTrip.mr]. destruct (numch b).
  - apply PjRoundTrip.mr_mono. lia.
  - lia.
Qed.

Lemma mr_app_ge : forall l X c, (PjRoundTrip.mr 0 X <= PjRoundTrip.mr c (l ++ X))%nat.
Proof.
  induction l as [|b l IH]; intros X c; cbn [app].
  - apply PjRoundTrip.mr_mono. lia.
  - pose proof (IH X 0%nat). pose proof (mr_cons_ge b (l ++ X) c). lia.
Qed.

Lemma mr_run : forall t X c, Forall (fun b => numch b = true) t -> (c + length t <= PjRoundTrip.mr c (t ++ X))%nat.
Proof.
  induction t as [|b t IH]; intros X c H; cbn [app length].
  - pose proof (PjRoundTrip.mr_ge X c). lia.
  - inversion H as [|b' t' Hb Ht]; subst. cbn [PjRoundTrip.mr]. rewrite Hb.
    specialize (IH X (S c) Ht). lia.
Qed.

Lemma txt_maxrun : forall tb k txt r, zb (skipn k tb) = txt ++ r -> Forall (fun c => numch c = true) txt ->
  (length txt <= PjRoundTrip.maxrun (zb tb))%nat.
Proof.
  intros tb k txt r H Hf. unfold PjRoundTrip.maxrun.
  rewrite <- (firstn_skipn k tb). unfold zb in *. rewrite map_app, H.
  pose proof (mr_app_ge (map (fun b : byte => bv_unsigned b) (firstn k tb)) (txt ++ r) 0) as A.
  pose proof (mr_run txt r 0 Hf) as B. lia.
Qed.

Lemma rest_at_len : forall tb text len P, Z.of_nat (length tb) = len -> text <= P <= text + len ->
  Z.of_nat (length (rest_at tb text P)) = text + len - P.
Proof.
  intros tb text len P Hl HP. unfold rest_at, zb. rewrite length_map, length_skipn. lia.
Qed.

Lemma rest_at_app : forall tb text P l r, text <= P -> rest_at tb text P = l ++ r ->
  rest_at tb text (P + Z.of_nat (length l)) = r.
Proof.
  intros tb text P l r HP H. unfold rest_at, zb in *.
  replace (Z.to_nat (P + Z.of_nat (length l) - text)) with (length l + Z.to_nat (P - text))%nat by lia.
  rewrite <- skipn_skipn, <- skipn_map, H. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma rest_at_cons : forall tb text P b y, text <= P -> rest_at tb text P = b :: y -> rest_at tb text (P + 1) = y.
Proof. intros tb text P b y HP H. apply (rest_at_app tb text P [b] y HP H). Qed.

Lemma rest_at_pos : forall tb text len P r, Z.of_nat (length tb) = len -> text <= P <= text + len ->
  (exists l, rest_at tb text P = l ++ r) -> text <= text + len - Z.of_nat (length r) <= text + len.
Proof.
  intros tb text len P r Hl HP (l & H). pose proof (rest_at_len tb text len P Hl HP) as L.
  rewrite H, length_app in L. lia.
Qed.

Lemma rest_at_suffix : forall tb text len P l r, Z.of_nat (length tb) = len -> text <= P <= text + len ->
  rest_at tb text P = l ++ r -> P + Z.of_nat (length l) = text + len - Z.of_nat (length r).
Proof.
  intros tb text len P l r Hl HP H. pose proof (rest_at_len tb text len P Hl HP) as L.
  rewrite H, length_app in L. lia.
Qed.

Lemma prefixb_bytes : forall (w : list Z) (l : list byte),
  Forall (fun c => 0 <= c < 256) w ->
  ((length w <= length l)%nat /\ firstn (length w) l = map (Z_to_bv 8) w) <-> prefixb w (zb l) = true.
Proof.
  induction w as [|a w IH]; intros l Hw; cbn [length firstn map prefixb].
  - split; [intros _; reflexivity | intros _; split; [lia | reflexivity]].
  - inversion Hw as [|a' w' Ha Hw']; subst.
    destruct l as [|b l]; cbn [length firstn zb map].
    + split; [intros [H _]; lia | discriminate].
    + unfold zb in IH. cbn [map]. rewrite andb_true_iff, Z.eqb_eq, <- (IH l Hw').
      split.
      * intros [H1 H2]. injection H2 as E1 E2. split; [|split; [lia | exact E2]].
        rewrite E1. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
      * intros (E & H1 & H2). split; [lia|]. f_equal; [|exact H2].
        subst a. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
        pose proof (bv_unsigned_in_range 8 b). exact H.
Qed.

Lemma lit_hit_prefixb : forall tb text len P (w : list Z),
  Z.of_nat (length tb) = len -> text <= P <= text + len -> Forall (fun c => 0 <= c < 256) w ->
  literal_c.lit_hit tb (P - text) (map (Z_to_bv 8) w) <-> prefixb w (rest_at tb text P) = true.
Proof.
  intros tb text len P w Hl HP Hw. unfold literal_c.lit_hit, rest_at.
  rewrite <- prefixb_bytes by exact Hw. rewrite length_map, length_skipn. split.
  - intros [H1 H2]. split; [lia | exact H2].
  - intros [H1 H2]. split; [lia | exact H2].
Qed.

Lemma hpeak_nil : hpeak [] = 0.
Proof. reflexivity. Qed.

Lemma hpeak_alloc : forall n, hpeak [EAlloc n] = Z.of_nat n.
Proof. intros n. cbn [hpeak held_ev]. lia. Qed.

Lemma hpeak_fail : forall n, hpeak [EFail n] = 0.
Proof. intros n. cbn [hpeak held_ev]. lia. Qed.

Lemma hpeak_alloc_free : forall n, hpeak [EAlloc n; EFree n] = Z.of_nat n.
Proof. intros n. cbn [hpeak held_ev]. lia. Qed.

Lemma lsz_one_alloc : forall (a k : Z) n, k = Z.of_nat n ->
  Permutation (map snd [(a, k)]) (map Z.of_nat (lsz [EAlloc n])).
Proof. intros a k n ->. apply Permutation_refl. Qed.

Lemma lsz_alloc_free : forall n, lsz [EAlloc n; EFree n] = [].
Proof. intros n. unfold lsz. cbn [fold_left lsz_ev rm1n]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma oks_one : forall cnt fail, oks [negb (cnt =? fail)] cnt fail 1.
Proof. intros cnt fail i Hi. destruct i as [|i]; [cbn; f_equal; f_equal; lia | lia]. Qed.

Lemma oks_zero : forall ok cnt fail, oks ok cnt fail 0.
Proof. intros ok cnt fail i Hi. lia. Qed.

Lemma fail_after_zero : forall cnt fail, fail_after cnt fail 0 fail.
Proof. intros cnt fail. split; intros H; [lia | reflexivity]. Qed.

Lemma fail_after_one_hit : forall fail, fail_after fail fail 1 (2 ^ 64 - 1).
Proof. intros fail. split; intros H; [reflexivity | exfalso; apply H; lia]. Qed.

Lemma fail_after_one_miss : forall cnt fail, cnt <> fail -> fail_after cnt fail 1 fail.
Proof. intros cnt fail H. split; intros H'; [lia | reflexivity]. Qed.

Lemma jr_strtod_some : forall txt bits c, strtod_c.strtod_model txt = Some (bits, c) ->
  jr_strtod txt = (c, bits) /\ whole jr_strtod txt = (c =? Z.of_nat (length txt)) && finite bits.
Proof.
  intros txt bits c H. unfold whole, jr_strtod. rewrite H. split; reflexivity.
Qed.
