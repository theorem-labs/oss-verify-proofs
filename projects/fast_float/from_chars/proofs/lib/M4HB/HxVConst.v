(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChEnt FxChEntM FxChSubst FxChMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition vc_sig (v : positive) (c : Z) : tree lin := tset v (lconst c) TEmpty.
Definition vconst_post (S : sst) (M : smodel) (v : positive) : option sst :=
  let '(lo, hi) := irange (s_facts S) (lvar v) in
  let σ := vc_sig v lo in
  if (Z.eqb lo hi && Z.leb 0 lo && Z.ltb lo two64 && Pos.ltb v (s_next S) && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool
  then Some (ssubst σ (s_next S) S) else None.

Lemma svar_vc_same : forall v c, svar (vc_sig v c) v = lconst c.
Proof. intros. unfold svar, vc_sig. rewrite tget_tset_same. reflexivity. Qed.
Lemma svar_vc_other : forall v c x, x <> v -> svar (vc_sig v c) x = lvar x.
Proof. intros v c x Hx. unfold svar, vc_sig. rewrite tget_tset_other by congruence. rewrite tget_empty. reflexivity. Qed.

Section VC.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_vconst : forall S M v S' E ms model, vconst_post S M v = Some S' ->
  DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M v S' E ms model Hp Hd. unfold vconst_post in Hp.
  destruct (irange (s_facts S) (lvar v)) as [lo hi] eqn:Hir.
  set (σ := vc_sig v lo) in *.
  destruct (Z.eqb lo hi && Z.leb 0 lo && Z.ltb lo two64 && Pos.ltb v (s_next S) && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool eqn:Hb; [|discriminate].
  injection Hp as <-.
  apply andb_prop in Hb as [Hb Hmk]. apply andb_prop in Hb as [Hb Hsm]. apply andb_prop in Hb as [Hb Hv]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [Heq Hle].
  apply Z.eqb_eq in Heq. apply Z.leb_le in Hle. apply Z.ltb_lt in Hlt. apply Pos.ltb_lt in Hv. apply sm_eqb_eq in Hsm.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) (lvar v) HF) as Rv. rewrite Hir, lden_lvar in Rv. cbn [fst snd] in Rv.
  assert (Hu : bv_unsigned (E v) = lo) by lia.
  assert (Hag : agree (s_next S) E (ecomp E σ)).
  { intros x Hx. unfold ecomp. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_vc_same, lden_lconst. apply bv_eq. rewrite Hu, u_Z_to_bv. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. symmetry. apply Z.mod_small. lia.
    - unfold σ. rewrite svar_vc_other by exact Hne. rewrite lden_lvar. reflexivity. }
  assert (Hsig : sig_wf σ (s_next S) (s_next S)).
  { intros x Hx. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_vc_same. reflexivity.
    - unfold σ. rewrite svar_vc_other by exact Hne. apply lwf_lvar. exact Hx. }
  pose proof (den_agree segs LIMIT model0 mem0 E (ecomp E σ) S M ms model Hd Hag) as Hd2.
  pose proof (den_subst segs LIMIT model0 mem0 E σ S M (s_next S) ms model Hsig Hmk Hd2) as Hd3. rewrite Hsm in Hd3. exact Hd3.
Qed.
End VC.
(* [comment removed for export] *)
