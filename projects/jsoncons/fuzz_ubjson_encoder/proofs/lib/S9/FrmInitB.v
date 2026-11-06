(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim FPSteps ShapeAlg SpinAlg FrmKeep FrmKeepC FrmKeepCEb0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Export FrmInit.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma frm_safe_Mb0 : frm_safe AsanUbsan.M.loaded_segments.
Proof. split; [exact FRMCB0.no_wx| exact FRMCB0.fetch_safe]. Qed.
