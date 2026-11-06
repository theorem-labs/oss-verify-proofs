(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Sorted.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma t_space_false : forall c, t_space c = false -> c <> 32 /\ c <> 9 /\ c <> 10 /\ c <> 13.
Proof. intros c H. repeat split; intros ->; vm_compute in H; discriminate. Qed.

Lemma t_ascii_stop_false : forall c, t_ascii_stop c = false -> c <> 34 /\ c <> 92.
Proof. intros c H. split; intros ->; vm_compute in H; discriminate. Qed.

Lemma is_cont_ord : forall c, is_cont c = true -> c <> 34 /\ c <> 92 /\ c <> 0.
Proof. intros c H. unfold is_cont in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. lia. Qed.

Section S1Out.
Variable bs : list Z.
Hypothesis BOK : bytes_ok bs.
Notation len := (blen bs).
Notation Bi := (B bs).

Lemma B_nonzero_lt : forall p, Bi p <> 0 -> p < len.
Proof. intros p H. destruct (Z.lt_ge_cases p len); [assumption|]. exfalso. apply H. apply B_pad. assumption. Qed.

Lemma ws_run_nonspace : forall f k, k < len -> len - k <= Z.of_nat f -> ws_run bs f k < len -> t_space (Bi (ws_run bs f k)) = false.
Proof.
  induction f as [|f IH]; intros k Hk Hf Hr; [lia|].
  rewrite ws_run_S in Hr |- *. destruct (t_space (Bi k)) eqn:TS; [|exact TS].
  destruct (Z.ltb_spec (k + 1) len); [|lia]. apply IH; lia.
Qed.

Lemma closes_from_ascii : forall f k j, 0 <= k < len -> closes bs (ascii_run bs f k) j -> closes bs k j.
Proof.
  induction f as [|f IH]; intros k j Hk H; [exact H|].
  rewrite ascii_run_S in H. destruct (t_ascii_stop (Bi k)) eqn:TS; [exact H|].
  destruct (t_ascii_stop_false _ TS) as [N34 N92].
  destruct (Z.ltb_spec (k + 1) len).
  - apply closes_ord; try assumption. apply IH; [lia|exact H].
  - apply closes_pos in H. lia.
Qed.

Lemma utf8_step_skips : forall k err k2 err2, utf8_step bs k err = (k2, err2) ->
  k < k2 /\ forall p, k < p < k2 -> is_cont (Bi p) = true.
Proof.
  intros k err k2 err2 H. unfold utf8_step in H.
  repeat match type of H with
  | (if ?c then _ else _) = _ => let E := fresh "E" in destruct c eqn:E
  end; inversion H; subst; clear H; (split; [lia|]); intros p Hp; try lia;
  repeat match goal with
  | E : (_ || _)%bool = false |- _ => apply orb_false_iff in E; destruct E
  | E : negb _ = false |- _ => apply negb_false_iff in E
  end;
  assert (C : p = k + 1 \/ p = k + 2 \/ p = k + 3) by lia; destruct C as [->|[->| ->]]; try assumption; lia.
Qed.

Lemma closes_skip_conts : forall n k j, 0 <= k -> (forall p, k <= p < k + Z.of_nat n -> Bi p <> 34 /\ Bi p <> 92) ->
  closes bs (k + Z.of_nat n) j -> closes bs k j.
Proof.
  induction n as [|n IH]; intros k j Hk Hb H.
  - replace (k + Z.of_nat 0) with k in H by lia. exact H.
  - pose proof (closes_bounds _ _ _ H) as CB.
    destruct (Hb k ltac:(lia)) as [N34 N92].
    apply closes_ord; [lia| exact N34| exact N92|].
    apply IH; [lia| |replace (k + 1 + Z.of_nat n) with (k + Z.of_nat (S n)) by lia; exact H].
    intros p Hp. apply Hb. lia.
Qed.

Lemma closes_from_token : forall k err k2 err2 j, 0 <= k < len -> Bi k <> 34 ->
  str_token bs k err = (k2, err2) -> closes bs k2 j -> closes bs k j.
Proof.
  intros k err k2 err2 j Hk N34 H HC. unfold str_token in H.
  destruct (Z.eqb_spec (Bi k) 92) as [E92|N92].
  - inversion H; subst. apply closes_esc; assumption.
  - destruct (Z.leb_spec 128 (Bi k)) as [G|G].
    + destruct (utf8_step_skips _ _ _ _ H) as [LT SK].
      replace k2 with (k + Z.of_nat (Z.to_nat (k2 - k))) in HC by lia.
      apply (closes_skip_conts (Z.to_nat (k2 - k)) k j); [lia| |exact HC].
      intros p Hp. destruct (Z.eq_dec p k) as [->|NE]; [split; assumption|].
      destruct (is_cont_ord _ (SK p ltac:(lia))) as (A & A' & _). split; assumption.
    + inversion H; subst. apply closes_ord; assumption.
Qed.

Lemma closes_from_str_loop : forall f k err i' err', 0 <= k ->
  str_loop bs f k err = (i', err', false) -> closes bs k i'.
Proof.
  induction f as [|f IH]; intros k err i' err' Hk H; [cbn in H; discriminate|].
  rewrite str_loop_S in H. destruct (Z.ltb_spec k len) as [L|L]; [|discriminate].
  cbv zeta in H.
  pose proof (ascii_run_bounds bs (length bs) k L) as AB.
  set (r := ascii_run bs (length bs) k) in *.
  destruct (Z.leb_spec len r) as [G|G]; [discriminate|].
  destruct (Z.eqb_spec (Bi r) 34) as [E34|N34].
  - inversion H; subst. apply (closes_from_ascii (length bs) k); [lia|]. fold r. apply closes_here; [lia|exact E34].
  - destruct (str_token bs r err) as [k2 err2] eqn:ET.
    pose proof (str_token_bounds bs r err) as TB. rewrite ET in TB. cbn [fst] in TB.
    apply (closes_from_ascii (length bs) k); [lia|]. fold r.
    apply (closes_from_token r err k2 err2); [lia| exact N34| exact ET|].
    apply (IH k2 err2 i' err'); [lia| exact H].
Qed.

Definition nonspace (i : Z) : Prop := Bi i <> 32 /\ Bi i <> 9 /\ Bi i <> 10 /\ Bi i <> 13.

Definition out_ok (out : list Z) (idx : Z) : Prop :=
  StronglySorted Z.lt out /\ Forall (fun i => 0 <= i < len /\ i < idx) out /\ Forall nonspace out.

Definition str_ok (out : list Z) (idx : Z) : Prop :=
  forall k i, nth_error out k = Some i -> Bi i = 34 ->
    exists j, closes bs (i + 1) j /\ j < idx /\ (forall i', nth_error out (S k) = Some i' -> j < i').

Lemma out_ok_mono : forall out idx idx', out_ok out idx -> idx <= idx' -> out_ok out idx'.
Proof.
  intros out idx idx' (S & R & N) H. split; [exact S|]. split; [|exact N].
  eapply Forall_impl; [|exact R]. cbv beta. intros; lia.
Qed.

Lemma str_ok_mono : forall out idx idx', str_ok out idx -> idx <= idx' -> str_ok out idx'.
Proof.
  intros out idx idx' H L k i Hn Hq. destruct (H k i Hn Hq) as (j & C & J & NX). exists j. repeat split; try assumption. lia.
Qed.

Lemma StronglySorted_snoc : forall (l : list Z) x, StronglySorted Z.lt l -> Forall (fun y => y < x) l -> StronglySorted Z.lt (l ++ [x]).
Proof.
  induction l as [|a l IH]; intros x S F; cbn.
  - constructor; constructor.
  - inversion S as [|? ? S' FA]; subst. inversion F as [|? ? Fa F']; subst.
    constructor; [apply IH; assumption|].
    apply Forall_app. split; [exact FA| constructor; [exact Fa| constructor]].
Qed.

Lemma out_ok_push : forall out idx i idx', out_ok out idx -> idx <= i < len -> 0 <= i -> i < idx' -> nonspace i ->
  out_ok (out ++ [i]) idx'.
Proof.
  intros out idx i idx' (S & R & N) Hi H0 Hi' NS. split; [|split].
  - apply StronglySorted_snoc; [exact S|]. eapply Forall_impl; [|exact R]. cbv beta. intros; lia.
  - apply Forall_app. split; [eapply Forall_impl; [|exact R]; cbv beta; intros; lia| constructor; [lia| constructor]].
  - apply Forall_app. split; [exact N| constructor; [exact NS| constructor]].
Qed.

Lemma str_ok_push : forall out idx i idx', str_ok out idx -> idx <= i -> i < idx' ->
  (Bi i = 34 -> exists j, closes bs (i + 1) j /\ j < idx') ->
  str_ok (out ++ [i]) idx'.
Proof.
  intros out idx i idx' H Hi Hi' OWN k x Hn Hq.
  destruct (Nat.lt_ge_cases k (length out)) as [L|L].
  - rewrite nth_error_app1 in Hn by exact L.
    destruct (H k x Hn Hq) as (j & C & J & NX). exists j. split; [exact C|]. split; [lia|].
    intros i' Hn'. destruct (Nat.lt_ge_cases (S k) (length out)) as [L2|L2].
    + rewrite nth_error_app1 in Hn' by exact L2. apply NX. exact Hn'.
    + rewrite nth_error_app2 in Hn' by exact L2.
      replace (S k - length out)%nat with 0%nat in Hn' by lia. cbn in Hn'. inversion Hn'; subst. lia.
  - rewrite nth_error_app2 in Hn by exact L.
    destruct (k - length out)%nat as [|d] eqn:D; cbn in Hn; [|destruct d; discriminate].
    inversion Hn; subst x. destruct (OWN Hq) as (j & C & J). exists j. split; [exact C|]. split; [exact J|].
    intros i' Hn'. rewrite nth_error_app2 in Hn' by lia.
    replace (S k - length out)%nat with 1%nat in Hn' by lia. cbn in Hn'. discriminate.
Qed.

Lemma scan_loop_inv : forall f st, 0 <= s_idx st ->
  out_ok (s_out st) (s_idx st) -> (s_unclosed st = false -> str_ok (s_out st) (s_idx st)) ->
  let st' := scan_loop bs f st in
  out_ok (s_out st') (s_idx st') /\ (s_unclosed st' = false -> str_ok (s_out st') (s_idx st')).
Proof.
  induction f as [|f IH]; intros st H0 OO SO; [cbn; split; assumption|].
  cbv zeta. rewrite scan_loop_S.
  destruct (Z.ltb_spec (s_idx st) len) as [L|L]; [|split; assumption].
  cbv zeta.
  pose proof (ws_run_bounds bs (length bs) (s_idx st) L) as WB.
  set (i := ws_run bs (length bs) (s_idx st)) in *.
  destruct (Z.leb_spec len i) as [G|G].
  - cbn [s_out s_idx s_unclosed]. split; [eapply out_ok_mono; [exact OO| lia]|].
    intros U. eapply str_ok_mono; [exact (SO U)| lia].
  - assert (NS : nonspace i).
    { apply t_space_false. apply ws_run_nonspace; try assumption. unfold blen in *. lia. }
    apply IH; unfold scan_token.
    + destruct (Z.eqb_spec (Bi i) 34).
      * destruct (str_loop bs (length bs) (i + 1) (s_err st)) as [[i' err'] u] eqn:ES.
        pose proof (str_loop_bounds bs _ _ _ _ _ _ ES). cbn [s_idx]. lia.
      * destruct (t_op (Bi i)); cbn [s_idx]; [lia|].
        pose proof (prim_run_bounds bs (length bs) i G). lia.
    + destruct (Z.eqb_spec (Bi i) 34).
      * destruct (str_loop bs (length bs) (i + 1) (s_err st)) as [[i' err'] u] eqn:ES.
        pose proof (str_loop_bounds bs _ _ _ _ _ _ ES). cbn [s_idx s_out].
        eapply out_ok_push; [exact OO| lia| lia| lia| exact NS].
      * destruct (t_op (Bi i)); cbn [s_idx s_out].
        -- eapply out_ok_push; [exact OO| lia| lia| lia| exact NS].
        -- pose proof (prim_run_bounds bs (length bs) i G).
           eapply out_ok_push; [exact OO| lia| lia| lia| exact NS].
    + destruct (Z.eqb_spec (Bi i) 34) as [E34|N34].
      * destruct (str_loop bs (length bs) (i + 1) (s_err st)) as [[i' err'] u] eqn:ES.
        pose proof (str_loop_bounds bs _ _ _ _ _ _ ES). cbn [s_idx s_out s_unclosed].
        intros U. apply orb_false_iff in U. destruct U as [U1 U2]. subst u.
        eapply str_ok_push; [exact (SO U1)| lia| lia|].
        intros _. exists i'. split; [|lia]. eapply closes_from_str_loop; [|exact ES]. lia.
      * destruct (t_op (Bi i)); cbn [s_idx s_out s_unclosed]; intros U.
        -- eapply str_ok_push; [exact (SO U)| lia| lia|]. intros Q; contradiction.
        -- pose proof (prim_run_bounds bs (length bs) i G).
           eapply str_ok_push; [exact (SO U)| lia| lia|]. intros Q; contradiction.
Qed.

Theorem stage1_S1OUT : forall idxs, stage1 bs = (0, idxs) -> S1OUT bs idxs.
Proof.
  intros idxs H. unfold stage1 in H. inversion H as [[HC HO]]. clear H.
  destruct (scan_loop_inv (S (length bs)) s1_init) as [OO SO].
  { cbn. lia. }
  { cbn. repeat split; constructor. }
  { intros _ k i Hn. destruct k; discriminate. }
  fold (stage1_st bs) in OO, SO.
  unfold s1_code in HC.
  destruct (length (s_out (stage1_st bs)) =? 0)%nat eqn:EL; [discriminate|].
  destruct (s_unclosed (stage1_st bs)) eqn:EU; [discriminate|].
  specialize (SO eq_refl). destruct OO as (SS & RG & NSP).
  apply Nat.eqb_neq in EL.
  constructor.
  - intros E. rewrite E in EL. apply EL. reflexivity.
  - exact SS.
  - eapply Forall_impl; [|exact RG]. cbv beta. intros; lia.
  - exact NSP.
  - intros k i Hn Hq. destruct (SO k i Hn Hq) as (j & C & J & NX).
    pose proof (closes_bounds _ _ _ C) as CB.
    exists j. split; [apply closes_str_close_len; exact C|]. split; [lia|]. split; [tauto| exact NX].
Qed.

End S1Out.
