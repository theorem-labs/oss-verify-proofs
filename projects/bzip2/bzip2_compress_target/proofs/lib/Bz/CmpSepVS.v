(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzSepTac CmpSepV.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac tslia_vs_leaf := first [ BzSepTac.tlia1 | BzSepTac.sep_tac | BzSepTac.tlia2 ].
Ltac tslia_vs :=
  lazymatch goal with
  | |- True => exact I
  | |- (_ <= _ \/ _ <= _) /\ _ => first [ split; [ CmpSepV.sv_conj_with ltac:(tslia_vs_leaf) | tslia_vs ] | BzSepTac.tslia_sep ]
  | |- (_ <= _ \/ _ <= _) => first [ CmpSepV.sv_conj_with ltac:(tslia_vs_leaf) | BzSepTac.tslia_sep ]
  | |- _ => BzSepTac.tslia_sep
  end.
