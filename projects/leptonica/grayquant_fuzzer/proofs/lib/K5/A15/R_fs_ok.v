(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import R_m2s R_fs_defs.
Open Scope Z_scope.

Definition FSB_ok2 (FSB : Z) : Prop :=
  (FSB + kFakeStackSize <= 0x7fff7000 \/ kHighShadowEnd < FSB) /\ 0x644000 <= FSB /\
  FSB + kFakeStackSize <= 2 ^ 47 /\ (FSB mod 4096 = 0).

Lemma FSB_ok_ok2 : forall FSB, FSB_ok FSB -> FSB_ok2 FSB.
Proof. intros FSB (H1 & H2 & H3). unfold FSB_ok2, kHighShadowEnd in *. repeat split; try lia. Qed.

(* [comment removed for export] *)
Lemma fsb_in_mem : forall FSB p, FSB_ok2 FSB -> FSB <= p < FSB + kFakeStackSize -> addr_in_mem p.
Proof. intros FSB p (H1 & H0 & H2 & H3) Hp. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd, kFakeStackSize in *. lia. Qed.

(* [comment removed for export] *)
Definition FSB_okL (FSB : Z) : Prop :=
  FSB + kFakeStackSize <= 0x7fff7000 /\ 0x644000 <= FSB /\ (FSB mod 4096 = 0).
