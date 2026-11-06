(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section ACeilS0. Context {ACEIL__ : ACeil}.
Definition DI_S0 : dimg := DIMG s0segs 0x2462c 0x320e8 0x32098 0x33178 0x335b0.
End ACeilS0.
