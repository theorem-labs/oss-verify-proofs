(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import FLia RelLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require TrivLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac ceil_drop_redundant :=
  lazymatch goal with
  | _ : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z |- _ =>
      repeat match goal with
             | H : (0x7fff7f800000 <= alloc_ceiling)%Z |- _ => clear H
             | H : (alloc_ceiling <= 0x7fffff800000)%Z |- _ => clear H
             end
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac lia_rf_tiers :=
  first [ RelLia.lia_r12
        | Zify.zify; xlia zchecker
        | progress aceil_evars; Zify.zify; xlia zchecker
        | progress (bz_ceil; ceil_drop_redundant); Zify.zify; xlia zchecker ].
Ltac lia_rf :=
  first [ TrivLia.lia_triv
        | solve [ NatLitLia.natlit_pre_goal_strict; lia_rf_tiers ]
        | lia_rf_tiers ].
