(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS.
Open Scope Z_scope.

Module LXWF.

Lemma tsyms_below_mono : forall ts n m, (n <= m)%nat -> tsyms_below ts n = true -> tsyms_below ts m = true.
Proof.
  induction ts as [|[x k] r IH]; cbn -[Nat.ltb]; intros n m Hle H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Nat.ltb_lt in H1. apply andb_true_intro; split; [apply Nat.ltb_lt; lia | eapply IH; eauto].
Qed.
Lemma lin_below_mono : forall l n m, (n <= m)%nat -> lin_below l n = true -> lin_below l m = true.
Proof. intros [c ts]; unfold lin_below; cbn; apply tsyms_below_mono. Qed.
Lemma aval_below_mono : forall v n m, (n <= m)%nat -> aval_below v n = true -> aval_below v m = true.
Proof.
  intros v n m Hle H. destruct v; cbn in *; [reflexivity | eapply lin_below_mono; eauto | |];
  apply andb_prop in H as [H1 H2]; apply andb_true_intro; split; eapply lin_below_mono; eauto.
Qed.

Lemma lconst_below : forall c n, lin_below (lconst c) n = true.
Proof. reflexivity. Qed.
Lemma lvar_below : forall x n, (x < n)%nat -> lin_below (lvar x) n = true.
Proof. intros. unfold lin_below, lvar; cbn -[Nat.ltb]. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma tadd_go_below : forall x k a' rec n,
  (x < n)%nat -> tsyms_below a' n = true ->
  (forall b, tsyms_below b n = true -> tsyms_below (rec b) n = true) ->
  forall b, tsyms_below b n = true -> tsyms_below (tadd_go x k a' rec b) n = true.
Proof.
  intros x k a' rec n Hx Ha Hrec b. induction b as [|[y m] b' IH]; cbn -[Nat.ltb Nat.eqb Z.eqb]; intros Hb.
  - apply andb_true_intro; split; [apply Nat.ltb_lt; exact Hx | exact Ha].
  - apply andb_prop in Hb as [Hy Hb'].
    destruct (Nat.ltb x y).
    + cbn -[Nat.ltb Nat.eqb Z.eqb]. apply andb_true_intro; split; [apply Nat.ltb_lt; exact Hx|].
      apply Hrec. cbn -[Nat.ltb]. rewrite Hy, Hb'. reflexivity.
    + destruct (Nat.eqb x y).
      * destruct (Z.eqb (k + m) 0); [apply Hrec; exact Hb'|].
        cbn -[Nat.ltb Nat.eqb Z.eqb]. apply andb_true_intro; split; [apply Nat.ltb_lt; exact Hx | apply Hrec; exact Hb'].
      * cbn -[Nat.ltb Nat.eqb Z.eqb]. rewrite Hy. cbn. apply IH. exact Hb'.
Qed.

Lemma tadd_below : forall a b n, tsyms_below a n = true -> tsyms_below b n = true -> tsyms_below (tadd a b) n = true.
Proof.
  induction a as [|[x k] a' IH]; intros b n Ha Hb; cbn -[tadd_go Nat.ltb]; [exact Hb|].
  cbn -[Nat.ltb] in Ha. apply andb_prop in Ha as [Hx Ha']. apply Nat.ltb_lt in Hx.
  apply tadd_go_below; auto.
Qed.
Lemma tscale_below : forall k a n, tsyms_below a n = true -> tsyms_below (tscale k a) n = true.
Proof.
  induction a as [|[x m] a' IH]; intros n H; cbn -[Nat.ltb] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn. apply IH. exact H2.
Qed.
Lemma ladd_below : forall a b n, lin_below a n = true -> lin_below b n = true -> lin_below (ladd a b) n = true.
Proof. intros [ca ta] [cb tb] n; unfold lin_below, ladd; cbn; apply tadd_below. Qed.
Lemma lscale_below : forall k a n, lin_below a n = true -> lin_below (lscale k a) n = true.
Proof.
  intros k [c t] n H; unfold lin_below, lscale in *; cbn in *. destruct (Z.eqb k 0); cbn; [reflexivity|].
  apply tscale_below. exact H.
Qed.
Lemma lneg_below : forall a n, lin_below a n = true -> lin_below (lneg a) n = true.
Proof. intros; unfold lneg; apply lscale_below; assumption. Qed.
Lemma lsub_below : forall a b n, lin_below a n = true -> lin_below b n = true -> lin_below (lsub a b) n = true.
Proof. intros; unfold lsub; apply ladd_below; [assumption | apply lneg_below; assumption]. Qed.
Lemma laddc_below : forall a c n, lin_below a n = true -> lin_below (laddc a c) n = true.
Proof. intros [ca ta] c n H; unfold lin_below, laddc in *; cbn in *; exact H. Qed.

Lemma bset_keys : forall b x i y, In y (map fst (bset b x i)) -> y = x \/ In y (map fst b).
Proof.
  induction b as [|[z j] r IH]; cbn; intros x i y H.
  - destruct H as [H|[]]; auto.
  - destruct (Nat.eqb x z) eqn:E; cbn in H.
    + apply Nat.eqb_eq in E; subst. destruct H; auto.
    + destruct H as [H|H]; [auto|]. destruct (IH _ _ _ H); auto.
Qed.

Lemma ctx_below_bounds : forall C n, ctx_below C n = true -> forall y, In y (map fst (cb C)) -> (y < n)%nat.
Proof.
  intros C n H y Hy. unfold ctx_below in H. apply andb_prop in H as [_ H].
  rewrite forallb_forall in H. apply in_map_iff in Hy as ([y' i] & Hyeq & Hin). cbn in Hyeq; subst.
  specialize (H _ Hin). cbn in H. apply Nat.ltb_lt in H. exact H.
Qed.

Lemma set_bound_below : forall C x i n, ctx_below C n = true -> (x < n)%nat -> ctx_below (set_bound C x i) n = true.
Proof.
  intros C x i n H Hx. pose proof (ctx_below_bounds C n H) as HB.
  unfold ctx_below in *. apply andb_prop in H as [HF _]. unfold set_bound; cbn.
  rewrite HF. cbn. rewrite forallb_forall. intros [y j] Hin. cbn. apply Nat.ltb_lt.
  assert (Hy : In y (map fst (bset (cb C) x i))) by (apply in_map_iff; exists (y, j); auto).
  destruct (bset_keys _ _ _ _ Hy); [subst; exact Hx | apply HB; assumption].
Qed.

Lemma refine1_keys : forall b l y, In y (map fst (refine1 b l)) -> In y (lsyms l) \/ In y (map fst b).
Proof.
  intros b [c ts] y H. unfold refine1 in H; cbn in H.
  destruct ts as [|[x k] [|t r]]; try (right; exact H).
  unfold lsyms; cbn.
  destruct (Z.ltb 0 k); [|destruct (Z.ltb k 0)]; try (right; exact H);
    destruct (bset_keys _ _ _ _ H); auto.
Qed.

Lemma lsyms_below : forall l n y, lin_below l n = true -> In y (lsyms l) -> (y < n)%nat.
Proof.
  intros [c ts] n y. unfold lin_below, lsyms; cbn. induction ts as [|[x k] r IH]; cbn -[Nat.ltb]; intros H Hin; [destruct Hin|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [apply Nat.ltb_lt; exact H1 | apply IH; auto].
Qed.

Lemma contra_witness_below : forall fs b l w n,
  forallb (fun f => lin_below f n) fs = true -> lin_below l n = true -> contra_witness fs b l = Some w -> lin_below w n = true.
Proof.
  intros fs b l w n HF Hl H. unfold contra_witness, contra_witnessV in H.
  destruct (find _ fs) as [g|] eqn:E; [|discriminate]. injection H; intros <-.
  apply find_some in E as [Hin _]. rewrite forallb_forall in HF. apply ladd_below; [exact Hl | apply HF; exact Hin].
Qed.
(* [comment removed for export] *)
Definition keys_below (b : bmap) (n : nat) : Prop := forall y, In y (map fst b) -> (y < n)%nat.
Lemma keys_below_forallb : forall b n, keys_below b n -> forallb (fun xb : sym * itv => Nat.ltb (fst xb) n) b = true.
Proof.
  intros b n H. rewrite forallb_forall. intros [y j] Hin. cbn. apply Nat.ltb_lt. apply H. apply in_map_iff. exists (y, j); auto.
Qed.
Lemma refine1_keys_below : forall b l n, keys_below b n -> lin_below l n = true -> keys_below (refine1 b l) n.
Proof.
  intros b l n Hb Hl y Hy. destruct (refine1_keys _ _ _ Hy); [eapply lsyms_below; eauto | apply Hb; assumption].
Qed.
Lemma derive2_below : forall b g x l1 n, lin_below g n = true -> derive2 b g x = Some l1 -> lin_below l1 n = true.
Proof.
  intros b [c ts] x l1 n Hg H. unfold derive2 in H; cbn in H.
  destruct ts as [|[u ku] [|[v kv] [|t r]]]; try discriminate.
  unfold lin_below in Hg; cbn -[Nat.ltb] in Hg. apply andb_prop in Hg as [Hu Hg]. apply andb_prop in Hg as [Hv _].
  destruct (Nat.eqb u x).
  - destruct (kx_max b u ku); [|discriminate]. injection H; intros <-. unfold lin_below; cbn -[Nat.ltb]. rewrite Hv. reflexivity.
  - destruct (Nat.eqb v x); [|discriminate]. destruct (kx_max b v kv); [|discriminate]. injection H; intros <-.
    unfold lin_below; cbn -[Nat.ltb]. rewrite Hu. reflexivity.
Qed.
Lemma propagate2_keys_below : forall fs b x n,
  forallb (fun f => lin_below f n) fs = true -> keys_below b n -> keys_below (propagate2 fs b x) n.
Proof.
  intros fs. induction fs as [|g r IH]; intros b x n HF Hb; cbn; [exact Hb|].
  change (forallb (fun f => lin_below f n) (g :: r)) with (lin_below g n &&& forallb (fun f => lin_below f n) r)%bool in HF.
  apply andb_prop in HF as [Hg Hr]. apply IH; [exact Hr|].
  destruct (derive2 b g x) as [l1|] eqn:E; [|exact Hb]. apply refine1_keys_below; [exact Hb | eapply derive2_below; eauto].
Qed.
Lemma refine2_keys_below : forall b l n, keys_below b n -> lin_below l n = true -> keys_below (refine2 b l) n.
Proof.
  intros b l n Hb Hl. unfold refine2. destruct (lt l) as [|[u ku] [|[v kv] [|t r]]] eqn:El; try exact Hb.
  set (b1 := match derive2 b l v with Some l1 => refine1 b l1 | None => b end).
  assert (Hb1 : keys_below b1 n).
  { subst b1. destruct (derive2 b l v) as [l1|] eqn:E; [|exact Hb]. apply refine1_keys_below; [exact Hb | eapply derive2_below; eauto]. }
  destruct (derive2 b1 l u) as [l2|] eqn:E2; [|exact Hb1]. apply refine1_keys_below; [exact Hb1 | eapply derive2_below; eauto].
Qed.
Lemma lnormg_below : forall l n, lin_below l n = true -> lin_below (lnormg l) n = true.
Proof.
  intros [c ts] n H. unfold lnormg; cbn. destruct (Z.ltb 1 (tgcd ts)); [|exact H].
  unfold lin_below in H |- *; cbn -[Nat.ltb] in H |- *. revert H. generalize (tgcd ts) as g. intros g.
  induction ts as [|[x k] r IH]; cbn -[Nat.ltb]; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite H1, (IH H2). reflexivity.
Qed.
Lemma add_fact_below : forall C l n, ctx_below C n = true -> lin_below l n = true -> ctx_below (add_fact C l) n = true.
Proof.
  intros C l0 n H Hl0. pose proof (ctx_below_bounds C n H) as HB.
  unfold add_fact. pose proof (lnormg_below l0 n Hl0) as Hl. set (l := lnormg l0) in *. clearbody l. destruct (is_const l).
  { destruct (Z.ltb _ 0); [|exact H]. unfold ctx_below in *. apply andb_prop in H as [HF HB'].
    cbn [cfacts cb]. change (forallb (fun f => lin_below f n) (l :: cfacts C)) with (lin_below l n &&& forallb (fun f => lin_below f n) (cfacts C))%bool.
    rewrite Hl, HF, HB'. reflexivity. }
  assert (K1 : keys_below (refine1 (cb C) l) n) by (apply refine1_keys_below; [exact HB | exact Hl]).
  unfold ctx_below in H. apply andb_prop in H as [HF _].
  destruct (single_sym l).
  { unfold ctx_below; cbn [cfacts cb]. rewrite HF, (keys_below_forallb _ _ (propagate2_keys_below _ _ _ _ HF K1)). reflexivity. }
  pose proof (keys_below_forallb _ _ (refine2_keys_below _ _ _ K1 Hl)) as Hb'.
  destruct (contra_witness (cfacts C) (refine2 (refine1 (cb C) l) l) l) as [w|] eqn:E; unfold ctx_below; cbn [cfacts cb].
  - change (forallb (fun f => lin_below f n) (w :: l :: cfacts C)) with (lin_below w n &&& (lin_below l n &&& forallb (fun f => lin_below f n) (cfacts C)))%bool.
    rewrite (contra_witness_below _ _ _ _ _ HF Hl E), Hl, HF, Hb'. reflexivity.
  - change (forallb (fun f => lin_below f n) (l :: cfacts C)) with (lin_below l n &&& forallb (fun f => lin_below f n) (cfacts C))%bool.
    rewrite Hl, HF, Hb'. reflexivity.
Qed.

Lemma norm_step_keys_below : forall b f n, keys_below b n -> lin_below f n = true -> keys_below (norm_step b f) n.
Proof. intros b f n Hb Hf. unfold norm_step. destruct (single_sym f); [apply refine1_keys_below | apply refine2_keys_below]; assumption. Qed.
Lemma rebound_keys_below : forall fs b n,
  forallb (fun f => lin_below f n) fs = true -> keys_below b n -> keys_below (rebound fs b) n.
Proof.
  intros fs. induction fs as [|f r IH]; intros b n HF Hb; cbn; [exact Hb|].
  change (forallb (fun f => lin_below f n) (f :: r)) with (lin_below f n &&& forallb (fun f => lin_below f n) r)%bool in HF.
  apply andb_prop in HF as [Hf Hr]. apply IH; [exact Hr | apply norm_step_keys_below; assumption].
Qed.
Lemma ctx_norm_below : forall C n, ctx_below C n = true -> ctx_below (ctx_norm C) n = true.
Proof.
  intros C n H. pose proof (ctx_below_bounds C n H) as HB. unfold ctx_below in H |- *. apply andb_prop in H as [HF _].
  cbn [cfacts cb ctx_norm]. rewrite HF. rewrite (keys_below_forallb _ _ (rebound_keys_below _ _ _ HF (rebound_keys_below _ _ _ HF HB))). reflexivity.
Qed.

Lemma ctx_below_mono : forall C n m, (n <= m)%nat -> ctx_below C n = true -> ctx_below C m = true.
Proof.
  intros C n m Hle H. unfold ctx_below in *. apply andb_prop in H as [HF HB].
  apply andb_true_intro; split; rewrite forallb_forall in *; intros x Hx.
  - eapply lin_below_mono; eauto.
  - specialize (HB x Hx). apply Nat.ltb_lt in HB. apply Nat.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma wf_ctx_below : forall st, wf_state st = true -> ctx_below (s_ctx st) (s_next st) = true.
Proof. intros st H. unfold wf_state in H. repeat (apply andb_prop in H as [H ?X]). assumption. Qed.

Lemma gc_fact_list_below : forall live fs n,
  forallb (fun f => lin_below f n) fs = true -> forallb (fun f => lin_below f n) (gc_fact_list live fs) = true.
Proof.
  intros live fs n H. apply forallb_forall. intros g Hg. unfold gc_fact_list in Hg.
  apply in_map_iff in Hg as (f & Ef & Hf). subst g.
  destruct (tsyms_any_live live (lt f)); [exact (proj1 (forallb_forall _ _) H f Hf) | reflexivity].
Qed.

Lemma gc_fact_list_length : forall live fs, length (gc_fact_list live fs) = length fs.
Proof. intros. unfold gc_fact_list. apply length_map. Qed.

Lemma gc_facts_ctx_below : forall st n, ctx_below (s_ctx st) n = true -> ctx_below (s_ctx (gc_facts st)) n = true.
Proof.
  intros st n H. unfold gc_facts. destruct (Nat.leb _ _); [exact H|]. cbn [s_ctx set_ctx].
  unfold ctx_below in *. cbn [cfacts cb] in *. apply andb_prop in H as [HF HB].
  rewrite (gc_fact_list_below _ _ _ HF), HB. reflexivity.
Qed.

Lemma gc_facts_wf : forall st, wf_state st = true -> wf_state (gc_facts st) = true.
Proof.
  intros st H. pose proof (gc_facts_ctx_below st (s_next st) (wf_ctx_below st H)) as HC.
  pose proof (wf_ctx_below st H) as HB0.
  unfold gc_facts in *. destruct (Nat.leb _ _); [exact H|].
  unfold wf_state in *. cbn [s_regs s_ctx s_next s_stk s_arrs s_pcache s_pay set_ctx] in *.
  rewrite HC. rewrite HB0 in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma gc_facts_same : forall st,
  s_pc (gc_facts st) = s_pc st /\ s_regs (gc_facts st) = s_regs st /\ s_next (gc_facts st) = s_next st /\
  s_stk (gc_facts st) = s_stk st /\ s_arrs (gc_facts st) = s_arrs st /\ s_abs (gc_facts st) = s_abs st /\
  s_pcache (gc_facts st) = s_pcache st /\ s_resv (gc_facts st) = s_resv st /\ s_depth (gc_facts st) = s_depth st /\
  s_pay (gc_facts st) = s_pay st /\ cb (s_ctx (gc_facts st)) = cb (s_ctx st).
Proof. intros st. unfold gc_facts. destruct (Nat.leb _ _); repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma gc_fact_list_sound : forall rho live fs,
  Forall (fun f => 0 <= evl rho f) fs -> Forall (fun f => 0 <= evl rho f) (gc_fact_list live fs).
Proof.
  intros rho live fs H. apply Forall_forall. intros g Hg. unfold gc_fact_list in Hg.
  apply in_map_iff in Hg as (f & Ef & Hf). subst g.
  destruct (tsyms_any_live live (lt f)); [exact (proj1 (Forall_forall _ _) H f Hf) |].
  unfold tombstone, evl; cbn. lia.
Qed.

Lemma gc_facts_ctx_ok : forall rho st, ctx_ok rho (s_ctx st) -> ctx_ok rho (s_ctx (gc_facts st)).
Proof.
  intros rho st [HF HB]. unfold gc_facts. destruct (Nat.leb _ _); [split; assumption|].
  cbn [s_ctx set_ctx cfacts cb]. split; cbn [cfacts cb]; [apply gc_fact_list_sound; exact HF | exact HB].
Qed.

End LXWF.
