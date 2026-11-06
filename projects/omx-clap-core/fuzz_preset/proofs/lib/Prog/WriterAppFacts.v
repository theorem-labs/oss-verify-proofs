From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterSpecFacts WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Lemma piece_lens_cons : forall b P, piece_lens (b :: P) = Z.of_nat (length b) :: piece_lens P.
Proof. reflexivity. Qed.

Lemma grow_calls_cons : forall x c l ls,
  grow_calls x c (l :: ls) =
  if c <? x + l + 1 then newcap c (x + l + 1) :: grow_calls (x + l) (newcap c (x + l + 1)) ls
  else grow_calls (x + l) c ls.
Proof. reflexivity. Qed.

Lemma grow_cap_cons : forall x c l ls,
  grow_cap x c (l :: ls) =
  if c <? x + l + 1 then grow_cap (x + l) (newcap c (x + l + 1)) ls else grow_cap (x + l) c ls.
Proof. reflexivity. Qed.

Lemma put1_fit : forall t c n fl cs b,
  Z.of_nat (length t) + Z.of_nat (length b) + 1 <= c ->
  put1 (mkW 0 t c n fl cs) b = mkW 0 (t ++ b) c n fl cs.
Proof.
  intros t c n fl cs b H. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls negb Z.eqb].
  destruct (Z.leb_spec (Z.of_nat (length t) + Z.of_nat (length b) + 1) c); [reflexivity|lia].
Qed.

Lemma put1_grow : forall t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 -> n <> fl ->
  put1 (mkW 0 t c n fl cs) b =
  mkW 0 (t ++ b) (newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) ((n + 1) mod 2 ^ 64) fl
    (cs ++ [newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)]).
Proof.
  intros t c n fl cs b H1 H2. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls negb Z.eqb].
  destruct (Z.leb_spec (Z.of_nat (length t) + Z.of_nat (length b) + 1) c); [lia|].
  destruct (Z.eqb_spec n fl); [contradiction|reflexivity].
Qed.

Lemma put1_starve : forall t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 -> n = fl ->
  put1 (mkW 0 t c n fl cs) b =
  mkW 1 t c ((n + 1) mod 2 ^ 64) (2 ^ 64 - 1) (cs ++ [newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)]).
Proof.
  intros t c n fl cs b H1 H2. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls negb Z.eqb].
  destruct (Z.leb_spec (Z.of_nat (length t) + Z.of_nat (length b) + 1) c); [lia|].
  destruct (Z.eqb_spec n fl); [reflexivity|contradiction].
Qed.

Theorem putN_ok : forall P st,
  w_failed st = 0 -> 0 <= w_cnt st ->
  w_cnt st + Z.of_nat (length (grow_calls (Z.of_nat (length (w_text st))) (w_cap st) (piece_lens P))) < 2 ^ 64 ->
  w_fail st < w_cnt st \/
    w_cnt st + Z.of_nat (length (grow_calls (Z.of_nat (length (w_text st))) (w_cap st) (piece_lens P))) <= w_fail st ->
  putN st P =
  mkW 0 (w_text st ++ concat P) (grow_cap (Z.of_nat (length (w_text st))) (w_cap st) (piece_lens P))
    (w_cnt st + Z.of_nat (length (grow_calls (Z.of_nat (length (w_text st))) (w_cap st) (piece_lens P))))
    (w_fail st) (w_calls st ++ grow_calls (Z.of_nat (length (w_text st))) (w_cap st) (piece_lens P)).
Proof.
  induction P as [|b P IH]; intros [f t c n fl cs]; cbn [w_failed w_text w_cap w_cnt w_fail w_calls];
    intros Hf Hn Hlen Hfail; subst f.
  - rewrite putN_nil. change (piece_lens []) with (@nil Z). cbn [grow_calls grow_cap concat length Z.of_nat].
    rewrite !app_nil_r. f_equal; lia.
  - revert Hlen Hfail. rewrite putN_cons, !piece_lens_cons, !grow_calls_cons, !grow_cap_cons.
    destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hg|Hg]; intros Hlen Hfail.
    + cbn [length] in Hlen, Hfail. rewrite put1_grow by lia.
      rewrite (Z.mod_small (n + 1) (2 ^ 64)) by lia.
      rewrite IH; cbn [w_failed w_text w_cap w_cnt w_fail w_calls]; rewrite ?length_app, ?Nat2Z.inj_add;
        [|lia..].
      cbn [concat]. rewrite <- !app_assoc. f_equal; try reflexivity. cbn [length]. lia.
    + rewrite put1_fit by lia.
      rewrite IH; cbn [w_failed w_text w_cap w_cnt w_fail w_calls]; rewrite ?length_app, ?Nat2Z.inj_add;
        [|lia..].
      cbn [concat]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma putN_starve_gen : forall P k t c n cs,
  0 <= n -> (k < length (grow_calls (Z.of_nat (length t)) c (piece_lens P)))%nat -> n + Z.of_nat k + 1 < 2 ^ 64 ->
  exists t' c', putN (mkW 0 t c n (n + Z.of_nat k) cs) P =
    mkW 1 t' c' (n + Z.of_nat k + 1) (2 ^ 64 - 1)
      (cs ++ firstn (S k) (grow_calls (Z.of_nat (length t)) c (piece_lens P))).
Proof.
  induction P as [|b P IH]; intros k t c n cs Hn Hk Hlt.
  - change (piece_lens []) with (@nil Z) in Hk. cbn [grow_calls length] in Hk. lia.
  - revert Hk. rewrite putN_cons, !piece_lens_cons, !grow_calls_cons.
    destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hg|Hg]; intros Hk.
    + cbn [length] in Hk. destruct k as [|k].
      * rewrite put1_starve by lia. rewrite putN_failed by (cbn [w_failed]; lia).
        exists t, c. cbn [firstn]. rewrite Z.mod_small by lia. f_equal; lia.
      * rewrite put1_grow by lia. rewrite Z.mod_small by lia.
        replace (n + Z.of_nat (S k)) with (n + 1 + Z.of_nat k) by lia.
        destruct (IH k (t ++ b) (newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) (n + 1)
          (cs ++ [newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)])) as [t' [c' E]].
        { lia. }
        { rewrite length_app, Nat2Z.inj_add. lia. }
        { lia. }
        rewrite length_app, Nat2Z.inj_add in E. rewrite E. exists t', c'. cbn [firstn].
        rewrite <- app_assoc. first [reflexivity | f_equal; lia].
    + rewrite put1_fit by lia.
      specialize (IH k (t ++ b) c n cs Hn). rewrite length_app, Nat2Z.inj_add in IH.
      apply IH; assumption.
Qed.

Theorem putN_starved : forall P cnt fail k,
  0 <= cnt -> fail = cnt + Z.of_nat k ->
  (k < length (grow_calls 0 0 (piece_lens P)))%nat -> cnt + Z.of_nat k + 1 < 2 ^ 64 ->
  w_failed (putN (w0 cnt fail) P) = 1 /\
  w_cnt (putN (w0 cnt fail) P) = cnt + Z.of_nat k + 1 /\
  w_fail (putN (w0 cnt fail) P) = 2 ^ 64 - 1 /\
  w_calls (putN (w0 cnt fail) P) = firstn (S k) (grow_calls 0 0 (piece_lens P)).
Proof.
  intros P cnt fail k Hn -> Hk Hlt. unfold w0.
  destruct (putN_starve_gen P k [] 0 cnt [] Hn Hk Hlt) as [t' [c' E]]. rewrite E.
  cbn [w_failed w_cnt w_fail w_calls app]. repeat split; reflexivity.
Qed.

Definition cap_pow (v : Z) : Prop := exists j, 0 <= j <= 51 /\ v = 4096 * 2 ^ j.

Definition wcap_ok (st : wst) : Prop :=
  w_cap st = 0 \/ (cap_pow (w_cap st) /\ Z.of_nat (length (w_text st)) < w_cap st).

Theorem putN_cap_pow : forall P st, wcap_ok st -> Forall cap_pow (w_calls st) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat P)) + 1 <= 2 ^ 63 ->
  wcap_ok (putN st P) /\ Forall cap_pow (w_calls (putN st P)).
Proof.
  induction P as [|b P IH]; intros [f t c n fl cs] Hw Hc Hb; [split; assumption|].
  destruct (Z.eqb_spec f 0) as [->|Hf].
  2:{ rewrite putN_failed by (cbn [w_failed]; exact Hf). split; assumption. }
  rewrite putN_cons. cbn [concat w_text w_calls] in Hb, Hc. rewrite length_app, Nat2Z.inj_add in Hb.
  assert (Hcw : c = 0 \/ cap_pow c).
  { unfold wcap_ok in Hw. cbn [w_cap w_text] in Hw. destruct Hw as [H0|[Hp _]]; [left|right]; assumption. }
  destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  - destruct (newcap_bound c (Z.of_nat (length t) + Z.of_nat (length b) + 1) Hcw ltac:(lia))
      as [j [Hj [Hnc [Hneed [H63 Hcle]]]]].
    assert (Hcp : cap_pow (newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)))
      by (exists j; split; assumption).
    destruct (Z.eqb_spec n fl) as [Heq|Hne].
    + rewrite put1_starve by assumption. rewrite putN_failed by (cbn [w_failed]; lia).
      split; [exact Hw|]. cbn [w_calls]. apply Forall_app. split; [exact Hc|].
      apply Forall_cons; [exact Hcp|apply Forall_nil].
    + rewrite put1_grow by assumption. apply IH; cbn [w_text w_cap w_calls].
      * unfold wcap_ok. cbn [w_cap w_text]. right. split; [exact Hcp|].
        rewrite length_app, Nat2Z.inj_add. lia.
      * apply Forall_app. split; [exact Hc|]. apply Forall_cons; [exact Hcp|apply Forall_nil].
      * rewrite length_app, Nat2Z.inj_add. lia.
  - rewrite put1_fit by assumption. apply IH; cbn [w_text w_cap w_calls].
    + unfold wcap_ok in Hw |- *. cbn [w_cap w_text] in Hw |- *. right.
      destruct Hw as [H0|[Hp Hl]]; [exfalso; lia|].
      split; [exact Hp|]. rewrite length_app, Nat2Z.inj_add. lia.
    + exact Hc.
    + rewrite length_app, Nat2Z.inj_add. lia.
Qed.

Fixpoint grow_needs (x c : Z) (ls : list Z) : list Z :=
  match ls with
  | [] => []
  | l :: rest =>
      if c <? x + l + 1 then (x + l + 1) :: grow_needs (x + l) (newcap c (x + l + 1)) rest
      else grow_needs (x + l) c rest
  end.

Theorem grow_calls_need : forall P x c, (c = 0 \/ cap_pow c) -> 0 <= x ->
  x + Z.of_nat (length (concat P)) + 1 <= 2 ^ 63 ->
  Forall2 (fun need v => 0 < need <= v /\ v <= 2 ^ 63 /\ cap_pow v)
    (grow_needs x c (piece_lens P)) (grow_calls x c (piece_lens P)).
Proof.
  induction P as [|b P IH]; intros x c Hc Hx Hb; [constructor|].
  rewrite piece_lens_cons. cbn [grow_needs]. rewrite grow_calls_cons.
  cbn [concat] in Hb. rewrite length_app, Nat2Z.inj_add in Hb.
  destruct (Z.ltb_spec c (x + Z.of_nat (length b) + 1)) as [Hg|Hg].
  - destruct (newcap_bound c (x + Z.of_nat (length b) + 1) Hc ltac:(lia)) as [j [Hj [Hnc [Hneed [H63 Hcle]]]]].
    constructor.
    + split; [lia|]. split; [exact H63|]. exists j. split; assumption.
    + apply IH; [right; exists j; split; assumption|lia|lia].
  - apply IH; [exact Hc|lia|lia].
Qed.

Theorem grow_calls_nonempty : forall P, P <> [] -> grow_calls 0 0 (piece_lens P) <> [].
Proof.
  intros [|b P] H; [exfalso; exact (H eq_refl)|]. rewrite piece_lens_cons, grow_calls_cons.
  destruct (Z.ltb_spec 0 (0 + Z.of_nat (length b) + 1)); [discriminate|lia].
Qed.

Fixpoint jv_bytes_ok (t : jv) : Prop :=
  match t with
  | JNum txt _ => bytes_ok txt /\ no_zero txt
  | JStr s => bytes_ok s /\ no_zero s
  | JArr items =>
      (fix go (l : list jv) : Prop :=
         match l with
         | [] => True
         | x :: r => jv_bytes_ok x /\ go r
         end) items
  | JObj members =>
      (fix go (l : list (list Z * jv)) : Prop :=
         match l with
         | [] => True
         | (k, x) :: r => bytes_ok k /\ no_zero k /\ jv_bytes_ok x /\ go r
         end) members
  | _ => True
  end.

Definition pok (P : list (list Z)) : Prop := Forall (Forall (fun b => 0 < b < 256)) P.

Ltac lit := try unfold pok; repeat first [apply Forall_nil | apply Forall_cons]; cbv beta; lia.

Ltac papp := apply Forall_app; split.

Lemma pok_concat : forall P, pok P -> Forall (fun b => 0 < b < 256) (concat P).
Proof.
  unfold pok. induction P as [|a P IH]; intros H; [constructor|].
  inversion H; subst. cbn [concat]. apply Forall_app. split; [assumption|apply IH; assumption].
Qed.

Lemma concat_pok : forall P, Forall (fun b => 0 < b < 256) (concat P) -> pok P.
Proof.
  unfold pok. induction P as [|a P IH]; intros H; [constructor|].
  cbn [concat] in H. apply Forall_app in H. destruct H as [H1 H2].
  apply Forall_cons; [exact H1|apply IH; exact H2].
Qed.

Lemma str_chr : forall s, bytes_ok s -> no_zero s -> Forall (fun b => 0 < b < 256) s.
Proof.
  unfold bytes_ok, no_zero. intros s Hb Hz. rewrite Forall_forall in *. intros x Hx.
  specialize (Hb x Hx). specialize (Hz x Hx). cbv beta in *. lia.
Qed.

Lemma spieces_ok : forall s, bytes_ok s -> no_zero s -> pok (spieces s).
Proof.
  intros s Hb Hz. apply concat_pok. rewrite concat_spieces.
  destruct (wstr_no_zero s Hb Hz) as [Hz' Hb']. apply str_chr; assumption.
Qed.

Lemma wind_ok : forall p d, pok (wind p d).
Proof.
  intros p d. unfold pok, wind. destruct p; [|apply Forall_nil].
  apply Forall_cons; [apply Forall_cons; [cbv beta; lia|apply Forall_nil]|].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. lit.
Qed.

Lemma wcomma_ok : forall i, pok (wcomma i).
Proof. intros i. unfold wcomma. destruct (Nat.eqb i 0); [apply Forall_nil|lit]. Qed.

Lemma wsep_ok : forall p, pok [wsep p].
Proof. intros p. unfold wsep. destruct p; lit. Qed.

Lemma wvpieces_ok : forall t p d, jv_bytes_ok t -> pok (wvpieces t p d).
Proof.
  intros t p.
  refine (jv_ind' (fun t => forall d, jv_bytes_ok t -> pok (wvpieces t p d)) _ _ _ _ _ _ _ t).
  - intros d _. cbn [wvpieces]. lit.
  - intros d _. cbn [wvpieces]. lit.
  - intros d _. cbn [wvpieces]. lit.
  - intros txt bits d H. cbn [wvpieces jv_bytes_ok] in *. destruct H as [Hb Hz]. unfold pok.
    apply Forall_cons; [apply str_chr; assumption|apply Forall_nil].
  - intros s d H. cbn [wvpieces jv_bytes_ok] in *. destruct H as [Hb Hz]. apply spieces_ok; assumption.
  - intros items IH d H. cbn [wvpieces]. cbn [jv_bytes_ok] in H. unfold pok.
    apply Forall_cons; [lit|].
    papp; [|papp; [destruct items; [apply Forall_nil|apply wind_ok]|lit]].
    revert H. generalize 0%nat. induction IH as [|x r Hx Hr IHr]; intros i H; [apply Forall_nil|].
    cbv beta in Hx. cbv beta iota in H |- *. destruct H as [H1 H2].
    papp; [apply wcomma_ok|]. papp; [apply wind_ok|]. papp; [apply Hx; exact H1|].
    apply IHr; exact H2.
  - intros members IH d H. cbn [wvpieces]. cbn [jv_bytes_ok] in H. unfold pok.
    apply Forall_cons; [lit|].
    papp; [|papp; [destruct members; [apply Forall_nil|apply wind_ok]|lit]].
    revert H. generalize 0%nat. induction IH as [|m r Hm Hr IHr]; intros i H; [apply Forall_nil|].
    destruct m as [k x]. cbn [snd] in Hm. cbv beta iota in H |- *. destruct H as [Hk1 [Hk2 [H1 H2]]].
    papp; [apply wcomma_ok|]. papp; [apply wind_ok|]. papp; [apply spieces_ok; assumption|].
    papp; [apply wsep_ok|]. papp; [apply Hm; exact H1|].
    apply IHr; exact H2.
Qed.

Theorem wdoc_no_zero : forall t p, jv_bytes_ok t -> no_zero (wdoc t p) /\ bytes_ok (wdoc t p).
Proof.
  intros t p H. apply chars_ok. unfold wdoc, wdpieces. apply pok_concat. unfold pok.
  papp; [apply wvpieces_ok; exact H|]. destruct p; [lit|apply Forall_nil].
Qed.
