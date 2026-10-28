(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Mem ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffImage R_intalloc.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma seg_rw_byte_win : forall z, 0x52e000 <= z < 0xbc6000 -> seg_rw_byte asegs z = true.
Proof. exact hi_seg_rw_byte_win. Qed.   (* [comment removed for export] *)

Lemma seg_rw_go_win : forall f a, 0x52e000 <= a -> a + Z.of_nat f <= 0xbc6000 -> seg_rw_go asegs a f = true.
Proof.
  induction f as [|f IH]; intros a H1 H2; cbn [seg_rw_go]; [reflexivity|].
  rewrite (seg_rw_byte_win a ltac:(lia)), (IH (a + 1) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_ok_win : forall a n, 0x52e000 <= a -> 0 <= n -> a + n <= 0xbc6000 -> seg_rw_ok asegs a n = true.
Proof.
  intros a n H1 H2 H3. unfold seg_rw_ok. rewrite (seg_rw_go_win (Z.to_nat n) a H1 ltac:(rewrite Z2Nat.id by lia; lia)).
  rewrite (proj2 (Z.leb_le 0 a) ltac:(lia)), (proj2 (Z.leb_le 0 n) H2), (proj2 (Z.leb_le (a + n) (2 ^ 64)) ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seg_rw_IAP1 : seg_rw_ok asegs (IAP + 8) 0x40000 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP2 : seg_rw_ok asegs (IAP + 0x40040) 0xd80 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP3 : seg_rw_ok asegs (IAP + 0x40dc0) 0x40248 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
