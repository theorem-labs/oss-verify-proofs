(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState RegsEquiv RegsEquivCfg RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import GlueCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithCfg.
Variable cfg : SpuriousCfg.

Lemma init_config_eqv_ms0 : forall segs pc ph lim en inp,
  cfg_eqv (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
          (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)).
Proof.
  intros. destruct (init_config_ms0 segs pc ph lim en inp) as [-> Heqv].
  split; [exact Heqv | reflexivity].
Qed.

Lemma behaves_spec_cfg_of_ms0 : forall segs pc ph lim T,
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     behaves_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T inp)) ->
  realizes_spec_cfg cfg segs pc ph lim T.
Proof.
  intros segs pc ph lim T H en inp HE HI.
  apply (behaves_cfg_eqv segs cfg _ _ (T inp) (cfg_eqv_sym _ _ (init_config_eqv_ms0 segs pc ph lim en inp))).
  apply H; assumption.
Qed.

Lemma realizes_spec_cfg_of_ms0 : forall segs pc ph lim T,
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T inp)) ->
  realizes_spec_cfg cfg segs pc ph lim T.
Proof.
  intros segs pc ph lim T H. apply behaves_spec_cfg_of_ms0.
  intros en inp HE HI. apply realizes_cfg_behaves. apply H; assumption.
Qed.

(* [comment removed for export] *)
Lemma run_scfg_fields_ms0 : forall segs pc ph lim en inp,
  let b := run_scfg cfg (mkImage segs pc ph) lim en inp in
  let c0 := mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp) in
  (forall tr, bh_traces b tr <-> obs_trace_cfg segs cfg c0 tr)
  /\ (bh_errors b <-> reaches_error_cfg segs cfg c0).
Proof.
  intros segs pc ph lim en inp. rewrite run_scfg_eq. cbv zeta. cbn [bh_traces bh_errors].
  pose proof (init_config_eqv_ms0 segs pc ph lim en inp) as H1.
  rewrite (proj1 (init_config_ms0 segs pc ph lim en inp)) in H1.
  pose proof (cfg_eqv_sym _ _ H1) as H2.
  split; [intros tr|]; split; intros H.
  - exact (obs_trace_scfg_eqv segs cfg _ _ tr H1 H).
  - exact (obs_trace_scfg_eqv segs cfg _ _ tr H2 H).
  - exact (reaches_error_scfg_eqv segs cfg _ _ H1 H).
  - exact (reaches_error_scfg_eqv segs cfg _ _ H2 H).
Qed.

End WithCfg.
