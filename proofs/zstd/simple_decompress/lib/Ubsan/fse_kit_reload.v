(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface huf41_kit_reload.
Import ListNotations. Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PFSE_RELOAD : Z := 0x2c2f8.

Definition fse_reload_stmt : Prop := huf_reload_stmt_at PFSE_RELOAD.

Theorem fse_reload_proof : fse_reload_stmt.
Proof.
  unfold fse_reload_stmt, huf_reload_stmt_at, PFSE_RELOAD. intros until sqb.
  intros MI BDC A1 SRCB SRCL R1 R2 R3 R4 DJ BCR P1 P2.
  unfold bitd_cells in BDC.
  assert (MU : munch [(BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (QR : exists q r d, bc = 8 * q + r /\ p = S + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
    by (exists (bc / 8), (bc mod 8), (p - S); clear - BCR P1 P2; Z.div_mod_to_equations; lia).
  destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
  assert (EDIV : (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r) by (clear - Q1 Q2; split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]).
  destruct EDIV as (ED & EM).
  kx_auto [] 150%nat
    [KZRange BD 4096 (2^47 - 40); KZRange S 4096 (2^47); KZRange (S + n) 4096 (2^47); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
     KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZAlign BD 8; KZWr BD 40; KZDisj BD 40 S n]
    [(S, n)].
  all: lazymatch goal with |- context [Z_to_bv 64 0x2c398] => kx_trap_fast | _ => idtac end.
  all: kx_mem.
  all: zstep.
  all: kx_abs.
  all: (apply evt_done; unfold huf_reload_post, bitd_cells; repeat (lazymatch goal with |- ex _ => eexists end);
        split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|];
        rewrite ED, EM; replace (S + d - q) with (S + (-1 * q + d)) by lia; exact BDC).
Qed.
