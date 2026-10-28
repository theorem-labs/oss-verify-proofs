(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface F_time AsIfaceMemalign.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section F.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Definition ainst_facts : Prop := atime_stmt H /\ memalign_stmt H APOSIX_MEMALIGN_STUB APC0_POSIX_MEMALIGN.
  Lemma ainst_time : ainst_facts -> atime_stmt H.
  Proof. intros X. exact (proj1 X). Qed.
  Lemma ainst_mal : ainst_facts -> memalign_stmt H APOSIX_MEMALIGN_STUB APC0_POSIX_MEMALIGN.
  Proof. intros X. exact (proj2 X). Qed.
  (* [comment removed for export] *)
  Lemma ainst_mal_lit : ainst_facts -> memalign_stmt H 0x1bf180 0x1bfb98.
  Proof. intros X. exact (proj2 X). Qed.
End F.
