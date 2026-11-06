(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import CatSim MmapSim ShapeAlg DivergeSim SpinAlg.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma excused_by_sibling : forall ms model x8 cR cG,
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  sstep segs (mkCfg ms model) [] (SNext cG) ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms cG) 0) = false ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms cR) 0) = true ->
  ~ fo_step segs (mkCfg ms model) [] cR.
Proof.
  intros ms model x8 cR cG Hsvc Hoff HstG HnG HrR.
  inversion HstG; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | Hx : ms_svc_pending ms = Some ?x0, Hsp : syscall_spec _ _ (Ok ?eff ?m1 _) |- _ =>
        assert (Ex : x0 = x8) by congruence; subst x0;
        apply (refusal_not_fo_step segs ms model x8 eff m1 [] cR Hsvc Hoff Hsp); [|exact HrR]
    end.
    cbn [cfg_ms] in HnG. rewrite ms_gpr0_advance_apply_effect in HnG. exact HnG.
  - (* [comment removed for export] *)
    match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H; destruct H as [_ H]; discriminate H end.
  - (* [comment removed for export] *)
    match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H; destruct H as [_ H]; discriminate H end.
Qed.

(* [comment removed for export] *)
Lemma srz_alt2_sp : forall ms model x8 (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) (IA + IB) (fun _ => []) nx ->
  (forall i, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inl i))) 0) = true) ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inr b0))) 0) = false ->
  (forall i, srealizes0 segs (nx (inl i)) A) ->
  (forall i, srealizes segs (nx (inr i)) B) ->
  srealizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 IA IB nx A B a0 b0 Hsvc Hoff Hnode HrA HnB HA HB.
  assert (HA0 : A []) by (eapply srealizes0_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  pose proof (proj1 Hnode (inr b0)) as HstG. cbn in HstG.
  apply (srz_conseq segs (mkCfg ms model)
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node_sp segs (mkCfg ms model) (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode).
    intros [i|i]; [right | left; apply HB].
    split; [apply HA|].
    exact (excused_by_sibling ms model x8 (nx (inl i)) (nx (inr b0)) Hsvc Hoff HstG HnB (HrA i)).
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Lemma srz_node_sp_sys : forall ms model x8 (I : Type) (nx : I -> config) (T : I -> TSet)
                            (live : I -> bool) (g0 : I),
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
  live g0 = true ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx g0)) 0) = false ->
  (forall i, live i = true -> srealizes segs (nx i) (T i)) ->
  (forall i, live i = false ->
     srealizes0 segs (nx i) (T i) /\ refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = true) ->
  srealizes segs (mkCfg ms model) (t_alt (fun i => t_emit [] (T i))).
Proof.
  intros ms model x8 I nx T live g0 Hsvc Hoff Hnode Hg0 Hng HL HD.
  pose proof (proj1 Hnode g0) as HstG. cbn in HstG.
  apply (srz_node_sp segs (mkCfg ms model) I (fun _ => []) nx T g0 Hnode).
  intros i. destruct (live i) eqn:Hi.
  - left. exact (HL i Hi).
  - right. destruct (HD i Hi) as [H0 Hr]. split; [exact H0|].
    exact (excused_by_sibling ms model x8 (nx i) (nx g0) Hsvc Hoff HstG Hng Hr).
Qed.

(* [comment removed for export] *)
Lemma ms_gpr0_advance_set_gpr0 : forall ms v,
  ms_gpr (advance_past_svc (set_gpr0 ms v)) 0 = v.
Proof.
  intros ms v. rewrite <- (apply_effect_no_write ms v). rewrite ms_gpr0_advance_apply_effect. reflexivity.
Qed.

End WithSegs.
