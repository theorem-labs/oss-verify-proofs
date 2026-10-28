(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLinT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import RelLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac tlia_rr := first [ solve [ SepLinT.sl_tslia ltac:(idtac; Zify.zify; xlia zchecker) ]
                      | rel_prune; Zify.zify; xlia zchecker
                      | Zify.zify; xlia zchecker
                      | RangeFast.rc_prune_lia
                      | sf_unhide;
                        first [ zify_prune_neg; Zify.zify; xlia zchecker
                              | zify_prune_plain; Zify.zify; xlia zchecker
                              | lia ] ].
