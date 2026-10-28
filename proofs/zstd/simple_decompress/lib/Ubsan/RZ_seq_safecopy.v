(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memmove RZ_seq_iface seqD_kit_sc_base seqD_kit_sc_lo seqD_kit_sc_hi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

Theorem zd_safecopy_proof : zd_safecopy_stmt.
Proof.
  unfold zd_safecopy_stmt, PZD_SAFECOPY. intros until R1.
  intros REG B0L B1H OPB LEN0 OPL OW0 OWH RDM R0L R1H IPR OVC STK LOS SPR OFFB OFFR MI -> -> -> -> ->.
  unfold off_stack in OFFB, OFFR. pose proof STK as (LO0 & _ & _).
  assert (OVC2 : sc_ovc OV IP OP LEN B0 B1 R0 R1).
    - (* [comment removed for export] *)
    exact OVC.
    - (* [comment removed for export] *)
    eapply sc_main; try eassumption.
    intros. subst. eapply sc_460 with (IP := IP) (OV := OV); eassumption.
Qed.
