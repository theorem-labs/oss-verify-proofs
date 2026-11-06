(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma find_segment_above : forall z, B_IMG_END <= z -> find_segment BSEGS z 1 = None.
Proof.
  intros z Hz. unfold B_IMG_END in Hz.
  unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments.
  cbn [find_segment].
  unfold AsanUbsan_segment_000, AsanUbsan_segment_001,
         AsanUbsan_segment_002, AsanUbsan_segment_003.
  cbn [seg_base seg_size].
  repeat match goal with
  | |- context [Z.leb ?a ?b && Z.leb ?c ?d] =>
      let E := fresh "E" in
      assert (E : Z.leb a b && Z.leb c d = false) by (apply andb_false_iff; right; apply Z.leb_gt; lia);
      rewrite E; clear E
  end.
  reflexivity.
Qed.

Lemma wr_ok_rd_ok : forall M a n, wr_ok BSEGS M a n -> B_IMG_END <= a -> a + n < 2 ^ 64 -> rd_ok M a n.
Proof.
  intros M a n Hw Ha Hn i Hi.
  pose proof (Hw (a + i) 1%nat ltac:(lia) ltac:(lia)) as Hs.
  cbn [store_ok] in Hs. unfold wview in Hs.
  destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:E; [discriminate|].
  unfold B_IMG_END in Ha.
  rewrite Wu in Hs by lia. rewrite find_segment_above in Hs by (unfold B_IMG_END; lia). discriminate.
Qed.
