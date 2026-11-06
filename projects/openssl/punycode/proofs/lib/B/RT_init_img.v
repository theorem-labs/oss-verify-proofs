(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Mem ImageA.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import HandoffImage R_intalloc.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma seg_rw_byte_win : forall z, 0x56b000 <= z < 0xbfd000 -> seg_rw_byte bsegs z = true.
Proof. exact hi_seg_rw_byte_win. Qed.   (* [comment removed for export] *)

Lemma seg_rw_go_win : forall f a, 0x56b000 <= a -> a + Z.of_nat f <= 0xbfd000 -> seg_rw_go bsegs a f = true.
Proof.
  induction f as [|f IH]; intros a H1 H2; cbn [seg_rw_go]; [reflexivity|].
  rewrite (seg_rw_byte_win a ltac:(lia)), (IH (a + 1) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_ok_win : forall a n, 0x56b000 <= a -> 0 <= n -> a + n <= 0xbfd000 -> seg_rw_ok bsegs a n = true.
Proof.
  intros a n H1 H2 H3. unfold seg_rw_ok. rewrite (seg_rw_go_win (Z.to_nat n) a H1 ltac:(rewrite Z2Nat.id by lia; lia)).
  rewrite (proj2 (Z.leb_le 0 a) ltac:(lia)), (proj2 (Z.leb_le 0 n) H2), (proj2 (Z.leb_le (a + n) (2 ^ 64)) ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seg_rw_IAP1 : seg_rw_ok bsegs (IAP + 8) 0x40000 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP2 : seg_rw_ok bsegs (IAP + 0x40040) 0xd80 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP3 : seg_rw_ok bsegs (IAP + 0x40dc0) 0x40248 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
