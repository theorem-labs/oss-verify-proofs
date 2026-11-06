(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia_cr :=
  first [ CmpLiaC.closed_arith
        | RelLia.rel_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | CmpLiaC.lia_c ].

Goal forall (f : Z -> Z) (a b c : Z), (0 <= f a < 10 -> 0 <= f b < 10 -> c <= f a -> c < 10)%Z. Proof. intros. lia_cr. Qed.
Goal (0 <= 13 < 50)%Z. Proof. lia_cr. Qed.
