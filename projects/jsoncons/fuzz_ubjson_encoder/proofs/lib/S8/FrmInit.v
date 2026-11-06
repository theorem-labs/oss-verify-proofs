(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim FPSteps ShapeAlg SpinAlg FrmKeep FrmKeepC FrmKeepEa0.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma init_fz : forall segs pc ph sp brk0 mb rnd lim inp,
  frm_zero (ms_fcsr (cfg_ms (init_config segs pc ph sp brk0 mb rnd lim inp))).
Proof. intros. reflexivity. Qed.

Lemma top_of_guarded {bmK : BMode} : forall segs scfg pc ph sp brk0 mb rnd lim inp T,
  frm_safe segs ->
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T.
Proof. intros segs scfg pc ph sp brk0 mb rnd lim inp T FS H. apply (srealizes0_of segs scfg _ T); [split; [exact FS| apply init_fz]| exact H]. Qed.

Lemma frm_safe_Ma0 : frm_safe Asan.M.loaded_segments.
Proof. split; [exact FRMA0.no_wx| intros a w H; exact (FRMC.safe_of_coarse w (FRMA0.fetch_safe a w H))]. Qed.
