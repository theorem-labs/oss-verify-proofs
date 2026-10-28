(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b.
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
