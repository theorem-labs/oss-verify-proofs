(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_m2s R_fs_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition FSB_ok2 (FSB : Z) : Prop :=
  (FSB + kFakeStackSize <= 0x7fff7000 \/ kHighShadowEnd < FSB) /\ 0xbfd000 <= FSB /\
  FSB + kFakeStackSize <= 2 ^ 47 /\ (FSB mod 4096 = 0).

Lemma FSB_ok_ok2 : forall FSB, FSB_ok FSB -> FSB_ok2 FSB.
Proof. intros FSB (H1 & H2 & H3). unfold FSB_ok2, kHighShadowEnd in *. repeat split; try lia. Qed.

(* [comment removed for export] *)
Lemma fsb_in_mem : forall FSB p, FSB_ok2 FSB -> FSB <= p < FSB + kFakeStackSize -> addr_in_mem p.
Proof. intros FSB p (H1 & H0 & H2 & H3) Hp. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd, kFakeStackSize in *. lia. Qed.

(* [comment removed for export] *)
Definition FSB_okL (FSB : Z) : Prop :=
  FSB + kFakeStackSize <= 0x7fff7000 /\ 0xbfd000 <= FSB /\ (FSB mod 4096 = 0).
