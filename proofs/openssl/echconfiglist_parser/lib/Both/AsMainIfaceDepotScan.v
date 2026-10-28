(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsPlanImagesHexZ.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainIface.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma tab_zero_scan : AsanHexTree.zpt AsanUbsan_seg_bytes_003 (Z.to_N (7915480 - 0x5ea000)) (Z.to_N 0x400000).
Proof. exact asan_tab_zero. Qed.
