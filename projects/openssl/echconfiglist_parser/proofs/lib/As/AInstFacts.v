(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsIface F_time AsIfaceMemalign.
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
  Lemma ainst_mal_lit : ainst_facts -> memalign_stmt H 0x1c4258 0x1c4c70.
  Proof. intros X. exact (proj2 X). Qed.
End F.
