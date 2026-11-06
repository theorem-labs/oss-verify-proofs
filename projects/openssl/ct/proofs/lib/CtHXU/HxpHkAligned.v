(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
From OSSVerify.Proofs.openssl.ct.lib.ApHX Require Import HkAligned.
From OSSVerify.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition hkp_posix_memalign : acd -> sstate -> option (acd * sstate) :=
  hk_at PC_POSIX_MEMALIGN (hk_posix_memalign_v T_ERRNO ERRNO_INT TPV 1%uint63).
