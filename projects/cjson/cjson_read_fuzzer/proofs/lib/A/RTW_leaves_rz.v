(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma k8_cases : forall k, 0 <= k <= 7 -> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7.
Proof. intros. lia. Qed.

Theorem rzsize2log_proof : rzsize2log_spec.
Proof.
  unfold rzsize2log_spec. intros until lo. intros MI HK A0 ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_RZSIZE2LOG. subst a0. leaf_prep.
  carve_frame 16%nat ST.
  destruct (k8_cases k HK) as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn.
  all: lstep; lstep. (* [comment removed for export] *)
  all: lstep; lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; if_lia. (* [comment removed for export] *)
  all: lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; if_lia. (* [comment removed for export] *)
  all: lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; if_lia. (* [comment removed for export] *)
  all: lstep; lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; fl. (* [comment removed for export] *)
  all: lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; if_lia. (* [comment removed for export] *)
  all: lstep; lstep; fl. (* [comment removed for export] *)
  all: lstep; if_lia. (* [comment removed for export] *)
  all: lstep; lstep; lstep; lstep. (* [comment removed for export] *)
  all: release_frame FR ST (bv_unsigned sp).
  all: finish; reflexivity.
Qed.


End CeilWrap.
