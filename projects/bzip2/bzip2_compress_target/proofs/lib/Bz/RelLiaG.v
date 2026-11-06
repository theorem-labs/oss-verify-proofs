(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import RelLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require TrivLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac lia_rg :=
  first [ TrivLia.lia_triv
        | rel_prune; zify_noeuclid; xlia zchecker
        | Zify.zify; xlia zchecker
        | aceil_evars; Zify.zify; xlia zchecker
        | bz_ceil; Zify.zify; xlia zchecker ].
