(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require TrivLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia_t12 :=
  zify_prune; intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate;
  first [ Zify.zify_post_hook; Z.euclidean_division_equations_cleanup; xlia zchecker
        | progress (Z.divide_to_equations'; first [ progress (repeat zify_dm_step; repeat zify_qr_step); cbv beta | idtac ]);
          Z.euclidean_division_equations_cleanup; Zify.zify_post_hook; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
