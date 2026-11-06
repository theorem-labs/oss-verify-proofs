(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia_acp_tiers :=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker
        | progress aceil_evars; Zify.zify; xlia zchecker
        | progress bz_ceil; Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac lia_acp :=
  first [ solve [ NatLitLia.natlit_pre_goal_strict; lia_acp_tiers ]
        | lia_acp_tiers ].

(* [comment removed for export] *)
Ltac tauto_fast :=
  first [ solve [ repeat match goal with
                         | |- _ /\ _ => split
                         | |- True => exact I
                         | |- _ = _ => reflexivity
                         end ]
        | tauto ].

(* [comment removed for export] *)
Section SelfTestP. Context {AC : ACeil} {RW : RunW}.
Local Ltac lia ::= lia_acp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End SelfTestP.
