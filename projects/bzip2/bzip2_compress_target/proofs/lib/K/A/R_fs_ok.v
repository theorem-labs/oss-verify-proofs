(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_m2s R_fs_defs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition FSB_ok2 (FSB : Z) : Prop :=
  (FSB + kFakeStackSize <= 0x7fff7000 \/ kHighShadowEnd < FSB) /\ 0x62b000 <= FSB /\
  FSB + kFakeStackSize <= 2 ^ 47 /\ (FSB mod 4096 = 0).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fsb_in_mem : forall FSB p, FSB_ok2 FSB -> FSB <= p < FSB + kFakeStackSize -> addr_in_mem p.
Proof. intros FSB p (H1 & H0 & H2 & H3) Hp. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd, kFakeStackSize in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_m2s R_fs_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition FSB_ok2 (FSB : Z) : Prop :=
  (FSB + kFakeStackSize <= 0x7fff7000 \/ kHighShadowEnd < FSB) /\ 0x61e000 <= FSB /\
  FSB + kFakeStackSize <= 2 ^ 47 /\ (FSB mod 4096 = 0).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fsb_in_mem : forall FSB p, FSB_ok2 FSB -> FSB <= p < FSB + kFakeStackSize -> addr_in_mem p.
Proof. intros FSB p (H1 & H0 & H2 & H3) Hp. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd, kFakeStackSize in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
