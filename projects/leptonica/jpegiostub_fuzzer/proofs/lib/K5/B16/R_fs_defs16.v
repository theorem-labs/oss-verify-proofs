(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import R_fs_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma NF_1 : NF 1 = 8192. Proof. reflexivity. Qed.
Lemma NF_6 : NF 6 = 256. Proof. reflexivity. Qed.
Lemma flags_off_1 : flags_off 1 = 0x4000. Proof. reflexivity. Qed.
Lemma flags_off_6 : flags_off 6 = 0x7e00. Proof. reflexivity. Qed.
Lemma fsz_1 : fsz 1 = 128. Proof. reflexivity. Qed.
Lemma fsz_6 : fsz 6 = 4096. Proof. reflexivity. Qed.

Lemma frame_addr_range16 : forall FSB c p, (c = 0 \/ c = 1 \/ c = 6) -> 0 <= p < NF c ->
  FSB + 0x9000 <= frame_addr FSB c p /\ frame_addr FSB c p + fsz c <= FSB + kFakeStackSize.
Proof.
  intros FSB c p Hc Hp. unfold frame_addr, kFakeStackSize.
  destruct Hc as [ -> | [ -> | -> ] ]; rewrite ?NF_0, ?NF_1, ?NF_6 in Hp; rewrite ?fsz_0, ?fsz_1, ?fsz_6; lia.
Qed.

Lemma fl_base_range16 : forall FSB c p, (c = 0 \/ c = 1 \/ c = 6) -> 0 <= p < NF c ->
  FSB + 0x1000 <= fl_base FSB c + p /\ fl_base FSB c + p + 1 <= FSB + 0x9000.
Proof.
  intros FSB c p Hc Hp. unfold fl_base.
  destruct Hc as [ -> | [ -> | -> ] ]; rewrite ?NF_0, ?NF_1, ?NF_6 in Hp; rewrite ?flags_off_0, ?flags_off_1, ?flags_off_6; lia.
Qed.
