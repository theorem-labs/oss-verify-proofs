(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CatSim ShapeAlg SpinAlg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition cfg0 : SpuriousCfg := alloc_only_cfg false.
Lemma cfg0_literal : cfg0 = mkSpuriousCfg false true true true true true. Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition crz (c : config) (T : ShapeAlg.TSet) : Prop := realizes_cfg cfg0 segs c T.

Lemma crz_conseq : forall c T T', crz c T -> ShapeAlg.t_eq T T' -> crz c T'.
Proof. intros c T T' H Heq. exact (rzc_conseq cfg0 segs c T T' H Heq). Qed.

Lemma crz_halt : forall c, m_halted (cfg_model c) <> None -> crz c ShapeAlg.t_nil.
Proof. intros c H. exact (rzc_halt cfg0 segs c H). Qed.

Lemma crz_nonempty : forall c T, crz c T -> T [].
Proof. intros c T H. exact (realizes_cfg_nonempty cfg0 segs c T H). Qed.

(* [comment removed for export] *)
Definition fam_on (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> sysno_family_off cfg0 (bv_unsigned x8) = false.

Lemma fam_on_no_svc : forall c, ms_svc_pending (cfg_ms c) = None -> fam_on c.
Proof. intros c H x8 Hx. rewrite H in Hx. discriminate. Qed.

Lemma fam_on_sysno : forall c x8, ms_svc_pending (cfg_ms c) = Some x8 ->
  bv_unsigned x8 <> 214%Z -> bv_unsigned x8 <> 216%Z -> bv_unsigned x8 <> 222%Z -> bv_unsigned x8 <> 226%Z -> fam_on c.
Proof.
  intros c x8 H H1 H2 H3 H4 y Hy. rewrite H in Hy. injection Hy as <-.
  apply sysno_family_off_alloc_only_false; assumption.
Qed.

Lemma node_on : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  ShapeAlg.node_ok segs c I evs nx -> fam_on c -> node_ok_cfg cfg0 segs c I evs nx.
Proof.
  intros [ms model] I evs nx Hn Hon.
  apply (node_ok_cfg_of_plain_on cfg0 segs ms model I evs nx); [|exact Hn].
  intros x8 Hsvc. rewrite injected_family_off_sysno. exact (Hon x8 Hsvc).
Qed.

Lemma node_det : forall c (evs : unit -> list event) (nx : unit -> config),
  ShapeAlg.node_ok segs c unit evs nx -> node_ok_cfg cfg0 segs c unit evs nx.
Proof. intros [ms model] evs nx Hn. exact (node_ok_cfg_of_plain_det cfg0 segs ms model evs nx Hn). Qed.

Lemma crz_node_on : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> ShapeAlg.TSet) (i0 : I),
  ShapeAlg.node_ok segs c I evs nx -> fam_on c ->
  (forall i, crz (nx i) (T i)) ->
  crz c (ShapeAlg.t_alt (fun i => ShapeAlg.t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hn Hon Hk.
  exact (rzc_node cfg0 segs c I evs nx T i0 (node_on c I evs nx Hn Hon) Hk).
Qed.

Lemma crz_silent1 : forall c c' T,
  ShapeAlg.node_ok segs c unit (fun _ => []) (fun _ => c') -> crz c' T -> crz c T.
Proof. intros c c' T Hn Hc. exact (rzc_silent1 cfg0 segs c c' T (node_det c _ _ Hn) Hc). Qed.

Lemma crz_emit1 : forall c c' e T,
  ShapeAlg.node_ok segs c unit (fun _ => e) (fun _ => c') -> crz c' T -> crz c (ShapeAlg.t_emit e T).
Proof. intros c c' e T Hn Hc. exact (rzc_emit1 cfg0 segs c c' e T (node_det c _ _ Hn) Hc). Qed.

Lemma crz_cases_on : forall c (I : Type) (nx : I -> config) (T : I -> ShapeAlg.TSet) (i0 : I),
  ShapeAlg.node_ok segs c I (fun _ => []) nx -> fam_on c ->
  (forall i, crz (nx i) (T i)) -> crz c (ShapeAlg.t_alt T).
Proof. intros c I nx T i0 Hn Hon Hk. exact (rzc_cases cfg0 segs c I nx T i0 (node_on c I _ nx Hn Hon) Hk). Qed.

Lemma crz_alt2_on : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : ShapeAlg.TSet) (a0 : IA) (b0 : IB),
  ShapeAlg.node_ok segs c (IA + IB) (fun _ => []) nx -> fam_on c ->
  (forall i, crz (nx (inl i)) A) -> (forall i, crz (nx (inr i)) B) ->
  crz c (ShapeAlg.t_alt2 A B).
Proof. intros c IA IB nx A B a0 b0 Hn Hon HA HB. exact (rzc_alt2 cfg0 segs c IA IB nx A B a0 b0 (node_on c _ _ nx Hn Hon) HA HB). Qed.

Lemma crz_exit : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  crz (mkCfg ms model) (ShapeAlg.t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros ms model x8 Hh Hsvc Hx. exact (rzc_exit cfg0 segs ms model x8 Hh Hsvc Hx). Qed.


(* [comment removed for export] *)
Lemma crz_cases_nonref : forall ms model x8 (I : Type) (nx : I -> config) (T : I -> ShapeAlg.TSet) (i0 : I),
  ms_svc_pending ms = Some x8 ->
  ShapeAlg.node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
  (forall i, m_halted (cfg_model (nx i)) = None -> refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = false) ->
  (forall i, crz (nx i) (T i)) -> crz (mkCfg ms model) (ShapeAlg.t_alt T).
Proof.
  intros ms model x8 I nx T i0 Hsvc Hn Hnr Hk.
  apply (rzc_cases cfg0 segs (mkCfg ms model) I nx T i0); [|exact Hk].
  exact (node_ok_cfg_of_plain_nonrefusal cfg0 segs ms model x8 I _ nx Hsvc Hnr Hn).
Qed.

(* [comment removed for export] *)
Lemma crz_alt2_fo : forall ms model x8 (IA IB : Type) (nx : IA + IB -> config) (B : ShapeAlg.TSet) (b0 : IB),
  ms_svc_pending ms = Some x8 -> sysno_family_off cfg0 (bv_unsigned x8) = true ->
  ShapeAlg.node_ok segs (mkCfg ms model) (IA + IB) (fun _ => []) nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall a, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inl a))) 0) = true) ->
  (forall b, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inr b))) 0) = false) ->
  (forall b, crz (nx (inr b)) B) -> crz (mkCfg ms model) B.
Proof.
  intros ms model x8 IA IB nx B b0 Hsvc Hoff Hn Hh Hr Hg Hk.
  apply (rzc_cases_same cfg0 segs (mkCfg ms model) IB (fun b => nx (inr b)) B b0); [|exact Hk].
  refine (node_ok_cfg_of_plain_sum_r cfg0 segs ms model x8 IA IB (fun _ => []) nx b0 Hsvc _ Hn Hh Hr Hg).
  rewrite injected_family_off_sysno. exact Hoff.
Qed.

(* [comment removed for export] *)
Lemma crz_cases_filter : forall ms model x8 (I J : Type) (nx : I -> config) (sel : J -> I) (T : J -> ShapeAlg.TSet) (j0 : J),
  ms_svc_pending ms = Some x8 -> sysno_family_off cfg0 (bv_unsigned x8) = true ->
  ShapeAlg.node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall j, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (sel j))) 0) = false) ->
  (forall i, (exists j, i = sel j) \/ refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = true) ->
  (forall j, crz (nx (sel j)) (T j)) -> crz (mkCfg ms model) (ShapeAlg.t_alt T).
Proof.
  intros ms model x8 I J nx sel T j0 Hsvc Hoff Hn Hh Hg Hr Hk.
  apply (rzc_cases cfg0 segs (mkCfg ms model) J (fun j => nx (sel j)) T j0); [|exact Hk].
  refine (node_ok_cfg_of_plain_filter cfg0 segs ms model x8 I J (fun _ => []) nx sel j0 Hsvc _ Hn Hh Hg Hr).
  rewrite injected_family_off_sysno. exact Hoff.
Qed.


(* [comment removed for export] *)
Lemma crz_cases_forced : forall ms model x8 (I : Type) (nx : I -> config) (T : I -> ShapeAlg.TSet) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  ShapeAlg.node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall i, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = true) ->
  (forall i, crz (nx i) (T i)) -> crz (mkCfg ms model) (ShapeAlg.t_alt T).
Proof.
  intros ms model x8 I nx T i0 Hh Hsvc Hn Hh' Hr Hk.
  apply (rzc_cases cfg0 segs (mkCfg ms model) I nx T i0); [|exact Hk].
  exact (node_ok_cfg_of_plain_forced cfg0 segs ms model x8 I _ nx Hh Hsvc Hn Hh' Hr).
Qed.

End WithSegs.
