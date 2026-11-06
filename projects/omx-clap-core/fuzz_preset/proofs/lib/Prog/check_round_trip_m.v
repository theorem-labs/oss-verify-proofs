From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue ReaderRes check_round_trip_c.
Import ListNotations.
Open Scope Z_scope.

Lemma crt_at_le : forall ms, (crt_at ms <= length ms)%nat.
Proof.
  induction ms as [|[k v] r IH]; cbn [crt_at length]; [lia|].
  destruct (list_eq_dec Z.eq_dec k MOD_AT); lia.
Qed.

Lemma crt_at_in : forall ms, (crt_at ms < length ms)%nat <-> In MOD_AT (map fst ms).
Proof.
  induction ms as [|[k v] r IH]; cbn [crt_at length map fst In].
  - split; [intros H; lia|contradiction].
  - destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E].
    + split; [intros _; left; exact E|intros _; lia].
    + split.
      * intros H. right. apply IH. lia.
      * intros [H|H]; [contradiction|]. apply IH in H. lia.
Qed.

Lemma crt_set_len : forall ms, length (pj_set_model ms MOD_AT (JStr STAMP)) = (if Nat.eqb (crt_at ms) (length ms) then S (length ms) else length ms).
Proof.
  induction ms as [|[k v] r IH]; cbn [pj_set_model crt_at length]; [reflexivity|].
  destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E]; cbn [length].
  - reflexivity.
  - rewrite IH. cbn [Nat.eqb]. destruct (Nat.eqb (crt_at r) (length r)); reflexivity.
Qed.

Lemma crtm_before : forall ms j nm u, (j < crt_at ms)%nat -> nth_error ms j = Some (nm, u) -> nm <> MOD_AT.
Proof.
  induction ms as [|[k v] r IH]; intros j nm u Hj He; cbn [crt_at] in Hj; [lia|].
  destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E]; [lia|].
  destruct j as [|j]; cbn [nth_error] in He.
  - injection He as <- <-. exact E.
  - apply (IH j nm u); [lia|exact He].
Qed.

Lemma crtm_at_some : forall ms, (crt_at ms < length ms)%nat -> exists u, nth_error ms (crt_at ms) = Some (MOD_AT, u).
Proof.
  induction ms as [|[k v] r IH]; intros H; [cbn in H; lia|].
  cbn [crt_at length] in H |- *. destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E]; cbn [nth_error] in H |- *.
  - exists v. rewrite E. reflexivity.
  - apply IH. lia.
Qed.

Lemma crtm_keep : forall ms j nm u, nth_error ms j = Some (nm, u) ->
  exists u', nth_error (pj_set_model ms MOD_AT (JStr STAMP)) j = Some (nm, u') /\ (j <> crt_at ms -> u' = u).
Proof.
  induction ms as [|[k v] r IH]; intros j nm u H; [destruct j; cbn in H; discriminate|].
  cbn [pj_set_model crt_at].
  destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E]; destruct j as [|j]; cbn [nth_error] in H |- *.
  - injection H as <- <-. exists (JStr STAMP). split; [reflexivity|]. intros N. contradiction N. reflexivity.
  - exists u. split; [exact H|intros _; reflexivity].
  - injection H as <- <-. exists v. split; [reflexivity|intros _; reflexivity].
  - destruct (IH j nm u H) as (u' & H1 & H2). exists u'. split; [exact H1|]. intros N. apply H2. intros M. apply N. rewrite M. reflexivity.
Qed.

Lemma crtm_at_set : forall ms, nth_error (pj_set_model ms MOD_AT (JStr STAMP)) (crt_at ms) = Some (MOD_AT, JStr STAMP).
Proof.
  induction ms as [|[k v] r IH]; [reflexivity|].
  cbn [pj_set_model crt_at]. destruct (list_eq_dec Z.eq_dec k MOD_AT) as [E|E]; cbn [nth_error].
  - rewrite E. reflexivity.
  - exact IH.
Qed.

Lemma crt_set_rel_model : forall ms, crt_set_rel ms (pj_set_model ms MOD_AT (JStr STAMP)) (crt_at ms).
Proof.
  intros ms. unfold crt_set_rel.
  split; [apply crt_at_le|]. split; [apply crtm_before|]. split; [apply crtm_at_some|].
  split; [apply crt_set_len|]. split; [apply crtm_keep|apply crtm_at_set].
Qed.

Lemma crtm_set_depth : forall ms k tv, (depth (JObj (pj_set_model ms k tv)) <= Nat.max (depth (JObj ms)) (S (depth tv)))%nat.
Proof.
  induction ms as [|[k0 v0] r IH]; intros k tv; cbn [pj_set_model].
  - cbn [depth map list_max fold_right]. lia.
  - specialize (IH k tv). destruct (list_eq_dec Z.eq_dec k0 k); cbn [depth map list_max fold_right] in *; unfold list_max in *; lia.
Qed.

Lemma crt_depth : forall t, (depth (crt_tree t) <= Nat.max (depth t) 2)%nat.
Proof.
  intros t. destruct t as [| | | txt bits | s | items | ms]; cbn [crt_tree]; try lia.
  pose proof (crtm_set_depth ms MOD_AT (JStr STAMP)) as D. change (depth (JStr STAMP)) with 0%nat in D. lia.
Qed.

Lemma crt_wf : forall x t, json_read jr_strtod x = Some t -> pj_wf jr_strtod (crt_tree t).
Proof.
  intros x t H. destruct t as [| | | txt bits | s | items | ms]; cbn [crt_tree]; try (eapply wf_read; exact H).
  destruct (read_json jr_strtod x (JObj ms) H) as (_ & Hd & _).
  apply wf_set.
  - eapply wf_read. exact H.
  - apply wf_string. unfold STAMP. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
  - unfold MOD_AT. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
  - pose proof (crtm_set_depth ms MOD_AT (JStr STAMP)) as D. change (depth (JStr STAMP)) with 0%nat in D.
    unfold MAXD in *. lia.
Qed.

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

Lemma crt_len : forall t, (length (wdoc (crt_tree t) true) <= length (wdoc t true) + 40)%nat.
Proof.
  intros t. destruct t as [| | | txt bits | s | items | ms]; cbn [crt_tree]; try lia.
  rewrite !crtm_wdoc_len, !crtm_obj_len.
  pose proof (crtm_wgo_set true 0 MOD_AT (JStr STAMP) ms 0) as H.
  assert (L1 : length (concat (wind true (0 + 1))) = 3%nat) by reflexivity.
  assert (L2 : length (concat (spieces MOD_AT)) = 12%nat) by reflexivity.
  assert (L3 : length (wsep true) = 2%nat) by reflexivity.
  assert (L4 : length (concat (wvpieces (JStr STAMP) true (0 + 1))) = 22%nat) by reflexivity.
  rewrite L1, L2, L3, L4, crtm_wcomma_len in H.
  destruct ms as [|[k v] r]; cbn [pj_set_model length Nat.add Nat.eqb] in *.
  - lia.
  - destruct (list_eq_dec Z.eq_dec k MOD_AT); cbn [length] in *; lia.
Qed.
