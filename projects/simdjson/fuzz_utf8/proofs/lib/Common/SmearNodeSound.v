(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ExecNodes ExecNodesSound SmearNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import SMR.
Open Scope Z_scope.

Module SMRS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smear_step (v s : Z) : Z := Z.lor v (v / 2 ^ s).
(* [comment removed for export] *)
Definition smear_den (shs : list Z) (v : Z) : Z := fold_left smear_step shs v.
Definition smear6 (x : Z) : Z := smear_den SMEAR_SHIFTS x.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hpos : 0 < Z.lor a b).
  { pose proof (Z.lor_nonneg a b). assert (Z.lor a b <> 0); [|lia]. intros E. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; [exact Hpos|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma smear_step_ok : forall v s a,
  0 <= v < 2 ^ 47 -> 0 <= s -> 0 <= a -> a + s <= 47 ->
  (forall i, a <= i <= 46 -> Z.testbit v i = true) ->
  0 <= smear_step v s < 2 ^ 47 /\ (forall i, Z.max 0 (a - s) <= i <= 46 -> Z.testbit (smear_step v s) i = true).
Proof.
  intros v s a Hv Hs Ha Has Hbits. unfold smear_step.
  assert (Hd : 0 <= v / 2 ^ s < 2 ^ 47).
  { split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
    apply Z.le_lt_trans with v; [|lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- (Z.mul_1_l v) at 1. apply Z.mul_le_mono_nonneg_r; [lia|]. pose proof (Z.pow_pos_nonneg 2 s). lia. }
  split; [apply lor_lt_pow2; lia|].
  intros i Hi. rewrite Z.lor_spec. apply orb_true_iff.
  destruct (Z.le_gt_cases a i) as [Hai|Hai]; [left; apply Hbits; lia|].
  right. rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia. apply Hbits. lia.
Qed.

Lemma smear6_val : forall x, 2 ^ 46 <= x < 2 ^ 47 -> smear6 x = 2 ^ 47 - 1.
Proof.
  intros x Hx.
  assert (B0 : forall i, 46 <= i <= 46 -> Z.testbit x i = true).
  { intros i Hi. replace i with 46 by lia. apply Z.testbit_true; [lia|].
    rewrite ?Z.shiftr_div_pow2 by lia. replace (x / 2 ^ 46) with 1; [reflexivity|].
    apply Z.div_unique with (x - 2 ^ 46); lia. }
  destruct (smear_step_ok x 1 46 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B0) as [R1 B1].
  destruct (smear_step_ok _ 2 45 R1 ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => B1 i ltac:(lia))) as [R2 B2].
  destruct (smear_step_ok _ 4 43 R2 ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => B2 i ltac:(lia))) as [R3 B3].
  destruct (smear_step_ok _ 8 39 R3 ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => B3 i ltac:(lia))) as [R4 B4].
  destruct (smear_step_ok _ 16 31 R4 ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => B4 i ltac:(lia))) as [R5 B5].
  destruct (smear_step_ok _ 32 15 R5 ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => B5 i ltac:(lia))) as [R6 B6].
  change (smear_step (smear_step (smear_step (smear_step (smear_step (smear_step x 1) 2) 4) 8) 16) 32) with (smear6 x) in R6, B6.
  apply Z.bits_inj'. intros n Hn.
  replace (2 ^ 47 - 1) with (Z.ones 47) by reflexivity.
  rewrite Z.testbit_ones by lia.
  destruct (Z.lt_ge_cases n 47) as [Hlt|Hge].
  - rewrite (proj2 (Z.ltb_lt _ _) Hlt), (proj2 (Z.leb_le _ _) Hn). cbn [andb]. apply B6. lia.
  - rewrite (proj2 (Z.ltb_ge _ _) Hge), andb_false_r. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec (smear6 x) 0) as [E0|E0]; [rewrite E0; cbn; lia|].
    apply Z.lt_le_trans with 47; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Den.
  Context {fx : FPState}.
  Variable SEGS : list Segment.

  Lemma smear_level_den : forall E M fk st k, know_ok SEGS E M fk -> 0 <= k < 64 ->
    bv_unsigned (edenot E (smear_level fk st k)) = smear_step (bv_unsigned (edenot E st)) k.
  Proof.
    intros E M fk st k HK Hk. unfold smear_level, smear_step.
    rewrite (mkAluK_denot SEGS E M fk ALU_OR _ _ HK). rewrite u_or64. f_equal.
    rewrite (mkAluK_denot SEGS E M fk ALU_SRL _ _ HK). rewrite u_srl64. cbn [edenot]. rewrite u_lit64. unfold two64.
    rewrite (Z.mod_small k) by lia. rewrite (Z.mod_small k) by lia. reflexivity.
  Qed.

  Lemma rebuild_den_gen : forall E M fk shs x, know_ok SEGS E M fk -> Forall (fun k => 0 <= k < 64) shs ->
    bv_unsigned (edenot E (fold_left (smear_level fk) shs x)) = fold_left smear_step shs (bv_unsigned (edenot E x)).
  Proof.
    intros E M fk shs. induction shs as [|k r IH]; intros x HK Hs; cbn [fold_left]; [reflexivity|].
    apply Forall_cons_iff in Hs as [Hk Hr].
    rewrite (IH _ HK Hr). rewrite (smear_level_den E M fk x k HK Hk). reflexivity.
  Qed.

  Lemma rebuild_den : forall E M fk x, know_ok SEGS E M fk ->
    bv_unsigned (edenot E (rebuild fk x)) = smear6 (bv_unsigned (edenot E x)).
  Proof.
    intros E M fk x HK. unfold rebuild, smear6, smear_den. apply (rebuild_den_gen E M fk SMEAR_SHIFTS x HK).
    unfold SMEAR_SHIFTS. repeat constructor; lia.
  Qed.
End Den.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  Lemma smear_fact_ok : forall E M k e x lo hi, know_ok SEGS E M k ->
    expr_eqb e (rebuild (facts_of k) x) = true -> erange k x = Some (lo, hi) -> 2 ^ 46 <= lo -> hi <= 2 ^ 47 - 1 ->
    kentry_ok SEGS E M (KRange e V47 V47).
  Proof.
    intros E M k e x lo hi HK He Hr Hlo Hhi.
    apply expr_eqb_eq in He. subst e.
    pose proof (erange_sound SEGS E M k x lo hi HK Hr) as Hx.
    pose proof (rebuild_den SEGS E M (facts_of k) x (facts_of_ok SEGS E M k HK)) as Hd.
    assert (Hb : 2 ^ 46 <= bv_unsigned (edenot E x) < 2 ^ 47) by (clear - Hx Hlo Hhi; lia).
    rewrite (smear6_val _ Hb) in Hd.
    cbn [kentry_ok]. unfold V47. rewrite Hd. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem xn_soundF : forall args, node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (SMR.xn args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn in Hn.
    destruct args as [|x rest]; [discriminate|].
    destruct (expr_eqb (reg cs (reg_arg (x :: rest))) (rebuild (facts_of (kn cs)) x)) eqn:He; [|discriminate].
    destruct (erange (kn cs) x) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb (2 ^ 46) lo && Z.leb hi (2 ^ 47 - 1))%bool eqn:Hg; [|discriminate].
    apply andb_prop in Hg as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    injection Hn as <-.
    eapply EXNS.set_kn_sound; [exact HC | | exact Hk].
    constructor; [| exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
    exact (smear_fact_ok E _ (kn cs) _ x lo hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) He Hr H1 H2).
  Qed.

  Theorem xn_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (SMR.xn args).
  Proof. intros args. apply node1_stmtF_stmt. apply xn_soundF. Qed.
End Sound.

End SMRS.
