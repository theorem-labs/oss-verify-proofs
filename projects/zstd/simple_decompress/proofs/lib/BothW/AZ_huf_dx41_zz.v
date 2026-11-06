(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_huf_iface3 AZ_hufkit AZ_libc_iface AZ_libc
     AZ_huf_dx41 AZ_huf_dx41_e AZ_huf_dx41_z AZ_huf_dx41_ffv.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Theorem x41_fast_okA : zd_memcpyZ_stmtA -> x41_fast_stmtA.
Proof.
  intros XMC RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX NB DH.
  unfold AZ_huf_dx41_e.x41_fast_stmt.
  intros mm l1 l2 l3 b0 b1 b2 b3 junk4 junk3 junk2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w0 w1 w2 w3 w4 w8 w12
    SV STK MU0 WM0 MI OUT DTB SRCB FR AR BJ4 BJ3 BJ2 HL1 HL2 HL3 HLN HQ3 TL11 HS0 HS1 HS2 HS3.
  eapply (AZ_huf_dx41_ffv.x41_fast RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DH NB TL11 XMC);
    eassumption.
Qed.

(* [comment removed for export] *)
Theorem huf_4x1_proofC : huf_4x1_stmtA.
Proof. exact (huf_4x1_proofA (x41_fast_okA zd_memcpyZ_proofA)). Qed.

End CANSEC1.
