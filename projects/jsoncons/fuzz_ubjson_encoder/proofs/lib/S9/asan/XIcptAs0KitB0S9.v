(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound SegRun SegPlan XIcptAB0S9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2.
Open Scope Z_scope.
Module XIAS0.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition fill_spec : Prop := XIA.icpt_fill_spec RSEGS XIA.AS0_MSET XIA.AS0_CELLS.
Definition copy_spec : Prop := XIA.icpt_copy_spec RSEGS XIA.AS0_MCPY XIA.AS0_CELLS.
Definition tls_spec : Prop := XIA.icpt_tls_spec RSEGS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Definition xstep : list SGP.region -> nat -> sym_state -> option sym_state :=
  XIA.xstep RSEGS XIA.AS0_MSET XIA.AS0_MCPY XIA.AS0_CELLS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Theorem xstep_ok : fill_spec -> copy_spec -> tls_spec -> forall nx0 BR F M0, SGP.XSTEP_ok RSEGS nx0 BR xstep F M0.
Proof. intros HF HC HT. exact (XIA.xstep_ok RSEGS _ _ _ _ _ _ _ _ _ HF HC HT). Qed.
End XIAS0.
