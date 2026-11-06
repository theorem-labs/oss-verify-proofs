(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzZScan.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AzHexZero.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma both_bss_scan2 : zscanN AsanUbsan_seg_bytes_003 63 2817408%N 2802304%N = true.
Proof. apply AzHexZero.zscanN_of_zero. vm_compute. reflexivity. Qed.
