(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BI_shadow BI_lowshadow BYajlRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma callbacks_oshadow : forall m, low_shadow_ok m -> oshadow m 0xa9b40 88.
Proof.
  intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 88) with (low_shadow_bytes 0x8000d368 11) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.
Lemma noop_allocs_oshadow : forall m, low_shadow_ok m -> oshadow m 0xa9bc0 32.
Proof.
  intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 32) with (low_shadow_bytes 0x8000d378 4) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.
Lemma buf_alloc_error_oshadow : forall m, low_shadow_ok m -> oshadow m 0xa9c00 32.
Proof.
  intros m H. unfold oshadow, block_shadow. split; [reflexivity|]. split; [lia|].
  replace (blk_shadow 32) with (low_shadow_bytes 0x8000d380 4) by (vm_compute; reflexivity).
  apply low_shadow_u8arr; [exact H| lia | cbn; lia].
Qed.
End RC__1.
