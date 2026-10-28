(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Mem ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import HandoffImage R_intalloc.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Asan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct AsanPlanImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma seg_rw_byte_win : forall z, 0x164000 <= z < 0x6ca000 -> seg_rw_byte asegs z = true.
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

Lemma seg_rw_go_win : forall f a, 0x164000 <= a -> a + Z.of_nat f <= 0x6ca000 -> seg_rw_go asegs a f = true.
Proof.
  induction f as [|f IH]; intros a H1 H2; cbn [seg_rw_go]; [reflexivity|].
  rewrite (seg_rw_byte_win a ltac:(lia)), (IH (a + 1) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma seg_rw_ok_win : forall a n, 0x164000 <= a -> 0 <= n -> a + n <= 0x6ca000 -> seg_rw_ok asegs a n = true.
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
