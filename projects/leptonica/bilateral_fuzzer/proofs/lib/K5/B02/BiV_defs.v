(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Arr FP FpBound FpReal FpSiteB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout RT_iface.
Import ListNotations.
Open Scope Z_scope.

Definition kel_vals (m : mem) (sx : Z) (rows : list Z) (f : Z -> Z -> Z) : Prop :=
  forall kk r qq, nth_error rows (Z.to_nat kk) = Some r -> 0 <= kk -> 0 <= qq < sx ->
    rw_cells asegs m (r + 4 * qq) [C4 (Z_to_bv 64 (f kk qq))] /\ FB fmt_single 1 (f kk qq).

Definition kfr_vals (m : mem) (kf : Z) (kfs : list Z) : Prop :=
  u32arr asegs m kf (map (Z_to_bv 64) kfs) /\ length kfs = 256%nat /\ Forall kfr_le1 kfs.
