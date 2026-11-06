(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require FrmKeepNa0. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FrmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FrmKeepC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047.FrmKeepNs0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.FrmKeepNa0.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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

(* [comment removed for export] *)
Lemma frm_safe_Ms0 : frm_safe Plain.M.loaded_segments.
Proof. split; [exact FRMS0.no_wx| intros a w H; exact (FRMC.safe_of_coarse w (FRMS0.fetch_safe a w H))]. Qed.
Lemma frm_safe_Ma0 : frm_safe Asan.M.loaded_segments.
Proof. split; [exact FRMA0.no_wx| exact FRMA0.fetch_safe]. Qed.
