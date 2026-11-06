(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Import ListNotations.

Lemma nonalloc_no : forall (x8 : bv 64) K, bv_unsigned x8 = K ->
  existsb (Z.eqb K) alloc_mark_sysnos = false -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros x8 K E Hb Hin. rewrite E in Hin.
  assert (Ht : existsb (Z.eqb K) alloc_mark_sysnos = true).
  { apply existsb_exists. exists K. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Section S.
Variable segs : list Segment.

Lemma step_nonspur_svc : forall ms m x8 K, ms_svc_pending ms = Some x8 -> bv_unsigned x8 = K ->
  existsb (Z.eqb K) alloc_mark_sysnos = false -> step_nonspur segs (mkCfg ms m).
Proof.
  intros ms m x8 K Hp E Hb. apply (step_nonspur_nonalloc segs ms m x8 Hp).
  exact (nonalloc_no x8 K E Hb).
Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs fcfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. apply (sstep_cfg_sub segs) in H. inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_one : forall c e c',
  sstep_cfg segs fcfg c e (SNext c') -> star_cfg segs fcfg c e c'.
Proof.
  intros c e c' H. rewrite <- (app_nil_r e).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs fcfg c1 t1 c2 -> star_cfg segs fcfg c2 t2 c3 -> star_cfg segs fcfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H. revert t2 c3.
  induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; intros t2 c4 H2; [exact H2|].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | apply IH; exact H2].
Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs fcfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh H. inversion H; subst; [split; reflexivity|].
  exfalso. apply Hh. eapply sstep_cfg_halted_none; eassumption.
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs fcfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

Lemma inv_no_reaches_error_cfg : forall (P : config -> Prop) c0,
  (forall c e c', P c -> sstep_cfg segs fcfg c e (SNext c') -> P c') ->
  (forall c e, P c -> ~ sstep_cfg segs fcfg c e SError) ->
  P c0 -> ~ reaches_error_cfg segs fcfg c0.
Proof.
  intros P c0 Hstep Herr H0 (tr & c & evs & Hstar & Hss).
  assert (Hc : P c).
  { clear Hss. revert H0. induction Hstar as [c | c1 e c2 tr c3 Hs Hst IH]; intros H1; [exact H1|].
    apply IH. eapply Hstep; eassumption. }
  exact (Herr c evs Hc Hss).
Qed.

End S.
