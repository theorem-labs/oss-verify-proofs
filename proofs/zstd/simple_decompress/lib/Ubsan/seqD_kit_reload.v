(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface huf41_kit_reload.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].


Definition PZD_RELOADI : Z := 0x1df40.

Theorem seqd_reload_proof : huf_reload_stmt_at PZD_RELOADI.
Proof.
  unfold huf_reload_stmt_at, PZD_RELOADI.
  intros until sqb. intros MI HBD BDA SQB SL R1 R2 R3 R4 DJ RB RP1 RP2.
  unfold bitd_cells in HBD.
  assert (MU : munch [(BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (QR : exists q r d, bc = 8 * q + r /\ p = S + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
    by (exists (bc / 8), (bc mod 8), (p - S); clear - RB RP1 RP2; lia).
  destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
  assert (ED : (8 * q + r) / 8 = q) by (symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia).
  assert (EM : (8 * q + r) mod 8 = r) by (symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia).
  kx_autoLx (@nil Z) 60%nat
    [KZRange BD 4096 (2^47 - 40); KZRange S 4096 (2^47); KZRange (S + n) 4096 (2^47); KZRange n 16 (2^47);
     KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47);
     KZRange (n - d) 8 (2^47); KZAlign BD 8; KZWr BD 40; KZDisj BD 40 S n]
    [(S, n)].
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dfe0) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: kx_mem.
  all: zstep.
  all: kx_abs.
  all: (apply evt_done; unfold huf_reload_post, bitd_cells; repeat (lazymatch goal with |- ex _ => eexists end);
        split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
        rewrite ED, EM; replace (S + d - q) with (S + (-1 * q + d)) by lia;
        match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end).
Qed.
