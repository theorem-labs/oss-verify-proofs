(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg Bridge.
Import ListNotations.
Open Scope sys_scope.

Definition brk_refusable (m : Model) (req : word) : bool :=
  let b := vm_brk (m_vmmaps m) in
  negb (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m))))
  && negb (Z.ltb (bv_unsigned req) (bv_unsigned b))
  && negb (bv_eqb req b)
  && negb (brk_grow_ok m req req).

Lemma scfg_spec_214 : forall i m o,
  bv_unsigned (in_sysno i) = 214%Z -> syscall_spec i m o <-> brk_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma refusal_b_214 : forall i m r,
  bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r E. unfold refusal_b. cbv zeta. rewrite E. reflexivity. Qed.

Lemma alloc_214 : forall i, bv_unsigned (in_sysno i) = 214%Z ->
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof. intros i E. rewrite E. left. reflexivity. Qed.

Lemma brk_outcome_of : forall i m r,
  bv_unsigned (in_sysno i) = 214%Z ->
  brk_r_ok m (in_arg i 0) r = true ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ eff_ret eff = r.
Proof.
  intros i m r E H. eexists _, _, _. split.
  - apply (proj2 (scfg_spec_214 i m _ E)). unfold brk_spec.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta.
    eapply bind_ok_nil; [apply (choose_ok _ r); exact H|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - reflexivity.
Qed.

Lemma brk_outcome_inv : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 214%Z ->
  syscall_spec i m (Ok eff m' evs) -> brk_r_ok m (in_arg i 0) (eff_ret eff) = true.
Proof.
  intros i m eff m' evs E Hs. apply (proj1 (scfg_spec_214 _ _ _ E)) in Hs. unfold brk_spec in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs.
  apply choose_bind_inv in Hs as (r & Hr & Hs). apply modify_bind_inv in Hs.
  apply pure_inv in Hs as (-> & _ & _). exact Hr.
Qed.

Lemma brk_refusable_false_ex : forall m req,
  brk_refusable m req = false ->
  exists r, brk_r_ok m req r = true /\ brk_refusal_b m req r = false.
Proof.
  intros m req Hr. set (b := vm_brk (m_vmmaps m)) in *.
  unfold brk_refusable in Hr. unfold brk_r_ok, brk_refusal_b. cbv beta zeta in Hr |- *. fold b in Hr |- *.
  pose proof (proj2 (bv_eqb_eq req req) eq_refl) as Rq.
  pose proof (proj2 (bv_eqb_eq b b) eq_refl) as Rb.
  destruct (w_is0 req) eqn:W; cbn [orb negb andb] in Hr |- *.
  { exists b. split; [exact Rb|reflexivity]. }
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m)))) eqn:Mb;
    cbn [orb negb andb] in Hr |- *.
  { exists b. split; [exact Rb|reflexivity]. }
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned b)) eqn:L; cbn [negb andb] in Hr |- *.
  { exists req. rewrite Rq. cbn [orb]. split; [reflexivity|].
    destruct (bv_eqb req b); reflexivity. }
  destruct (bv_eqb req b) eqn:Eq; cbn [negb andb] in Hr |- *.
  { exists b. rewrite Rb, orb_true_r. cbn [andb]. split; [|reflexivity].
    unfold brk_grow_ok. cbv beta zeta. fold b. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. }
  apply negb_false_iff in Hr. exists req. rewrite Rq, Hr. cbn [orb andb].
  split; [reflexivity|exact Eq].
Qed.

Lemma brk_refusable_true_all : forall m req,
  brk_refusable m req = true ->
  forall r, brk_r_ok m req r = true -> brk_refusal_b m req r = true.
Proof.
  intros m req Hr r Hok. set (b := vm_brk (m_vmmaps m)) in *.
  unfold brk_refusable in Hr. unfold brk_r_ok in Hok. unfold brk_refusal_b.
  cbv beta zeta in Hr, Hok |- *. fold b in Hr, Hok |- *.
  apply andb_true_iff in Hr as [Hr Hgr]. apply andb_true_iff in Hr as [Hr Hne].
  apply andb_true_iff in Hr as [Hq Hl].
  apply negb_true_iff in Hq. apply negb_true_iff in Hl.
  apply negb_true_iff in Hne. apply negb_true_iff in Hgr.
  rewrite Hq, Hl in Hok. apply orb_false_iff in Hq as [W Mb].
  rewrite W, Mb, Hne. cbn [negb andb].
  apply andb_true_iff in Hok as [Hrb Hgo].
  apply orb_true_iff in Hrb as [Hrq|Hrb].
  - apply bv_eqb_eq in Hrq. rewrite Hrq in Hgo. rewrite Hgo in Hgr. discriminate Hgr.
  - exact Hrb.
Qed.

Lemma brk_refusable_iff_all : forall m req,
  brk_refusable m req = true <->
  (forall r, brk_r_ok m req r = true -> brk_refusal_b m req r = true).
Proof.
  intros m req. split; [apply brk_refusable_true_all|].
  intros H. destruct (brk_refusable m req) eqn:Hr; [reflexivity|].
  destruct (brk_refusable_false_ex m req Hr) as (r & Hok & Hnr).
  rewrite (H r Hok) in Hnr. discriminate Hnr.
Qed.

Lemma brk_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 214%Z ->
  brk_refusable m (in_arg i 0) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hr.
  destruct (brk_refusable_false_ex m (in_arg i 0) Hr) as (r & Hok & Hnr).
  destruct (brk_outcome_of i m r E Hok) as (eff & m' & evs & Hs & Hret).
  exists eff, m', evs. split; [exact Hs|]. rewrite refusal_b_214 by exact E. rewrite Hret. exact Hnr.
Qed.

Lemma brk_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 214%Z ->
  brk_refusable m (in_arg i 0) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hr eff m' evs Hs. rewrite refusal_b_214 by exact E.
  exact (brk_refusable_true_all m _ Hr _ (brk_outcome_inv i m eff m' evs E Hs)).
Qed.

Lemma brk_nonspur_refusable : forall i m eff,
  bv_unsigned (in_sysno i) = 214%Z ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true -> brk_refusable m (in_arg i 0) = true)).
Proof.
  intros i m eff E. apply (nonspur_cases _ i m eff (alloc_214 i E)).
  - apply brk_refusable_false_grant, E.
  - apply brk_refusable_true_forced, E.
Qed.

Lemma brk_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 214%Z ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (brk_refusal_b m (in_arg i 0) (eff_ret eff) = true ->
    forall r, brk_r_ok m (in_arg i 0) r = true -> brk_refusal_b m (in_arg i 0) r = true)).
Proof.
  intros i m eff E. rewrite (brk_nonspur_refusable i m eff E), (refusal_b_214 i m _ E).
  rewrite brk_refusable_iff_all. reflexivity.
Qed.

Lemma brk_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> brk_refusable m (in_arg i 0) = true).
Proof. intros i m eff E. apply nonspur_refusal_iff, brk_nonspur_refusable, E. Qed.

Lemma brk_grow_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 214%Z ->
  brk_grow_ok m (in_arg i 0) (in_arg i 0) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hg. apply (nonspur_of_grant i m eff (alloc_214 i E)).
  apply brk_refusable_false_grant; [exact E|].
  unfold brk_refusable. rewrite Hg. cbn [negb]. apply andb_false_r.
Qed.

Lemma brk_grow_refusal_spurious : forall i m eff,
  bv_unsigned (in_sysno i) = 214%Z ->
  w_is0 (in_arg i 0) = false ->
  (bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned (in_arg i 0))%Z ->
  (bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned (in_arg i 0))%Z ->
  brk_grow_ok m (in_arg i 0) (in_arg i 0) = true ->
  eff_ret eff = vm_brk (m_vmmaps m) ->
  spurious_refusal_cfg fcfg i m eff.
Proof.
  intros i m eff E W Hmin Hlt Hg Hret.
  split; [exact (fcfg_family_off i (alloc_214 i E))|]. split.
  - rewrite refusal_b_214 by exact E. rewrite Hret. unfold brk_refusal_b. cbv beta zeta.
    rewrite W, (proj2 (Z.ltb_ge _ _) Hmin).
    destruct (bv_eqb (in_arg i 0) (vm_brk (m_vmmaps m))) eqn:Eq.
    + apply bv_eqb_eq in Eq. rewrite Eq in Hlt. lia.
    + rewrite (proj2 (bv_eqb_eq (vm_brk (m_vmmaps m)) _) eq_refl). reflexivity.
  - apply brk_refusable_false_grant; [exact E|].
    unfold brk_refusable. rewrite Hg. cbn [negb]. apply andb_false_r.
Qed.
