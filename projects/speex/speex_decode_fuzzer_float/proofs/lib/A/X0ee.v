(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cy X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X03n X0hf.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Asan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2 X0lj.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0um X180.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require AsanUbsan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require X0lk.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0um OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180.
Import OSSVerify.speex.speex_decode_fuzzer_float.images.AsanUbsan.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0k2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lk.
Open Scope Z_scope.

Lemma seg_rw_byte_win : forall z, 0xf7000 <= z < 0x65b000 -> seg_rw_byte bsegs z = true.
Proof.
intros z Hz. assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; lia).
pose proof (asan_rw_window (fun _ => None) (wa z) ltac:(rewrite Hu; lia)) as W.
unfold wview in W. change ASEGS with bsegs in W. rewrite Hu in W. cbv beta iota in W. unfold seg_rw_byte.
destruct (find_segment bsegs z 1) as [s|] eqn:F; [|exfalso; apply W; reflexivity].
destruct (seg_writable s) eqn:Ew; [|exfalso; apply W; reflexivity].
destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) eqn:Eb; [|exfalso; apply W; reflexivity].
assert (Er : seg_readable s = true).
{ apply find_segment_some_spec in F as (Hin & _). change bsegs with ASEGS in Hin. rewrite asan_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_readable seg_writable seg_perms string_has Ascii.eqb AsanUbsan_segment_000 AsanUbsan_segment_001
AsanUbsan_segment_002 AsanUbsan_segment_003] in Ew |- *; first [reflexivity | discriminate]. }
rewrite Er. reflexivity.
Qed.

Lemma seg_rw_go_win : forall f a, 0xf7000 <= a -> a + Z.of_nat f <= 0x65b000 -> seg_rw_go bsegs a f = true.
Proof.
induction f as [|f IH]; intros a H1 H2; cbn [seg_rw_go]; [reflexivity|].
rewrite (seg_rw_byte_win a ltac:(lia)), (IH (a + 1) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_ok_win : forall a n, 0xf7000 <= a -> 0 <= n -> a + n <= 0x65b000 -> seg_rw_ok bsegs a n = true.
Proof.
intros a n H1 H2 H3. unfold seg_rw_ok. rewrite (seg_rw_go_win (Z.to_nat n) a H1 ltac:(rewrite Z2Nat.id by lia; lia)).
rewrite (proj2 (Z.leb_le 0 a) ltac:(lia)), (proj2 (Z.leb_le 0 n) H2), (proj2 (Z.leb_le (a + n) (2 ^ 64)) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_IAP1 : seg_rw_ok bsegs (IAP + 8) 0x40000 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP2 : seg_rw_ok bsegs (IAP + 0x40040) 0xd80 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP3 : seg_rw_ok bsegs (IAP + 0x40dc0) 0x40248 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
End B_TWIN.

Open Scope Z_scope.

Lemma seg_rw_byte_win : forall z, 0xef000 <= z < 0x652000 -> seg_rw_byte asegs z = true.
Proof.
intros z Hz. assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; lia).
pose proof (asan_rw_window (fun _ => None) (wa z) ltac:(rewrite Hu; lia)) as W.
unfold wview in W. change ASEGS with asegs in W. rewrite Hu in W. cbv beta iota in W. unfold seg_rw_byte.
destruct (find_segment asegs z 1) as [s|] eqn:F; [|exfalso; apply W; reflexivity].
destruct (seg_writable s) eqn:Ew; [|exfalso; apply W; reflexivity].
destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) eqn:Eb; [|exfalso; apply W; reflexivity].
assert (Er : seg_readable s = true).
{ apply find_segment_some_spec in F as (Hin & _). change asegs with ASEGS in Hin. rewrite asan_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_readable seg_writable seg_perms string_has Ascii.eqb Asan_segment_000 Asan_segment_001
Asan_segment_002 Asan_segment_003] in Ew |- *; first [reflexivity | discriminate]. }
rewrite Er. reflexivity.
Qed.

Lemma seg_rw_go_win : forall f a, 0xef000 <= a -> a + Z.of_nat f <= 0x652000 -> seg_rw_go asegs a f = true.
Proof.
induction f as [|f IH]; intros a H1 H2; cbn [seg_rw_go]; [reflexivity|].
rewrite (seg_rw_byte_win a ltac:(lia)), (IH (a + 1) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_ok_win : forall a n, 0xef000 <= a -> 0 <= n -> a + n <= 0x652000 -> seg_rw_ok asegs a n = true.
Proof.
intros a n H1 H2 H3. unfold seg_rw_ok. rewrite (seg_rw_go_win (Z.to_nat n) a H1 ltac:(rewrite Z2Nat.id by lia; lia)).
rewrite (proj2 (Z.leb_le 0 a) ltac:(lia)), (proj2 (Z.leb_le 0 n) H2), (proj2 (Z.leb_le (a + n) (2 ^ 64)) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_IAP1 : seg_rw_ok asegs (IAP + 8) 0x40000 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP2 : seg_rw_ok asegs (IAP + 0x40040) 0xd80 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
Lemma seg_rw_IAP3 : seg_rw_ok asegs (IAP + 0x40dc0) 0x40248 = true.
Proof. apply seg_rw_ok_win; unfold IAP; lia. Qed.
