(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export BzParams.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker
        | aceil_evars; bzp_evars; Zify.zify; xlia zchecker
        | bz_ceil; bz_params_occ; Zify.zify; xlia zchecker ].
Ltac nia ::= first [ Zify.zify; xnia zchecker | bz_ceil; bz_params_occ; Zify.zify; xnia zchecker ].

Section SelfTest. Context {BZP : BzParams} {AC : ACeil}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End SelfTest.
