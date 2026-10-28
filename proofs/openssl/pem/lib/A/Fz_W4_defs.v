(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Export Fz_W4_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_EVP_DecodeInit : Z := 0x31f3e8.
Definition e_EVP_DecodeUpdate : Z := 0x31f498.
Definition e_evp_decodeblock_int : Z := 0x31f8bc.
Definition e_EVP_DecodeFinal : Z := 0x320034.

(* [comment removed for export] *)
Notation B64A_TABLE := (0xa41a0)%Z (only parsing).
Definition b64A_table : list byte :=
  Eval vm_compute in (match image_bytes asegs 0xa41a0 128 with Some bs => bs | None => [] end).

Lemma b64A_table_len : length b64A_table = 128%nat.
Proof. reflexivity. Qed.

Lemma b64A_table_at : forall m, mem_inv asegs m -> bytes_at asegs m B64A_TABLE b64A_table.
Proof.
  intros m HI.
  assert (RO : ro_cells asegs m B64A_TABLE [CB 128 b64A_table])
    by (apply (ro_cells_image asegs m B64A_TABLE b64A_table HI); [vm_compute; reflexivity | lia | cbn; lia]).
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma b64A_table_nth : forall c, 0 <= c < 128 -> exists v, nth_error b64A_table (Z.to_nat c) = Some v.
Proof.
  intros c Hc. destruct (nth_error b64A_table (Z.to_nat c)) as [v|] eqn:E; [exists v; reflexivity|].
  apply nth_error_None in E. rewrite b64A_table_len in E. lia.
Qed.

(* [comment removed for export] *)
Lemma ectxA_data : forall m C num ed ln fl, length ed = 80%nat ->
  ro_cells asegs m C (ectx_cells num ed ln fl) -> bytes_at asegs m (C + 4) ed.
Proof.
  intros m C num ed ln fl L [_ B]. unfold ectx_cells in B. cbn [cells_bytes cbytes] in B.
  apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
  replace (Z.of_nat (length (le4 num))) with 4 in B by reflexivity. exact B.
Qed.
