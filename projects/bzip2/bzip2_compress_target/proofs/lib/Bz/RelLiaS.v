(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLinT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac RelLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tlia_bzd_r := first [ solve [ SepLinT.sl_tslia ltac:(idtac; Zify.zify; xlia zchecker) ]
                         | rel_prune; Zify.zify; xlia zchecker
                         | Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Ltac tlia1_r := first [ solve [ SepLinT.sl_tslia ltac:(idtac; Zify.zify; xlia zchecker) ] | rel_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
