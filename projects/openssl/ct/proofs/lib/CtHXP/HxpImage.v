(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Mem Image.
From OSSVerify.openssl.ct.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation ctpsegs := ImageCt.ctpsegs.

Definition seg0 := Plain_segment_000.
Definition seg1 := Plain_segment_001.
Definition seg2 := Plain_segment_002.
Definition seg3 := Plain_segment_003.

Lemma psegs_eq : ctpsegs = [seg0; seg1; seg2; seg3].
Proof. reflexivity. Qed.

Local Ltac seg_consts :=
  replace (Z.of_N (seg_base Plain_segment_000)) with 65536%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Plain_segment_000)) with 839680%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Plain_segment_001)) with 905216%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Plain_segment_001)) with 1703936%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Plain_segment_002)) with 2609152%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Plain_segment_002)) with 380928%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Plain_segment_003)) with 2990080%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Plain_segment_003)) with 217088%Z by (vm_compute; reflexivity).

(* [comment removed for export] *)
Lemma find_seg : forall a n, 1 <= n ->
  find_segment ctpsegs a n =
    if (65536 <=? a) && (a + n <=? 905216) then Some seg0
    else if (905216 <=? a) && (a + n <=? 2609152) then Some seg1
    else if (2609152 <=? a) && (a + n <=? 2990080) then Some seg2
    else if (2990080 <=? a) && (a + n <=? 3207168) then Some seg3
    else None.
Proof.
  intros a n Hn. unfold ctpsegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments.
  cbn [find_segment]. seg_consts. reflexivity.
Qed.

Lemma seg0_ro : seg_writable seg0 = false. Proof. vm_compute. reflexivity. Qed.
Lemma seg0_rd : seg_readable seg0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg2_wr : seg_writable seg2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg2_rd : seg_readable seg2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg3_wr : seg_writable seg3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg3_rd : seg_readable seg3 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ro_addr_seg0 : forall a, 65536 <= a < 905216 -> ro_addr ctpsegs (wa a) = true.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 905216)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  rewrite seg0_ro. reflexivity.
Qed.

(* [comment removed for export] *)
Definition chunk_of (sg : Segment) : PrimString.string := match seg_bytes sg with [c] => c | _ => PrimString.make 0%uint63 0%uint63 end.
Lemma seg0_chunk : seg_bytes seg0 = [chunk_of seg0]. Proof. reflexivity. Qed.
Lemma seg2_chunk : seg_bytes seg2 = [chunk_of seg2]. Proof. reflexivity. Qed.
Lemma seg3_chunk : seg_bytes seg3 = [chunk_of seg3]. Proof. reflexivity. Qed.

Lemma find_seg0_in : forall a, 65536 <= a < 905216 -> find_segment ctpsegs a 1 = Some seg0.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 905216)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma find_seg2_in : forall a, 2609152 <= a < 2990080 -> find_segment ctpsegs a 1 = Some seg2.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 905216)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((905216 <=? a) && (a + 1 <=? 2609152)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((2609152 <=? a) && (a + 1 <=? 2990080)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma find_seg3_in : forall a, 2990080 <= a < 3207168 -> find_segment ctpsegs a 1 = Some seg3.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 905216)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((905216 <=? a) && (a + 1 <=? 2609152)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((2609152 <=? a) && (a + 1 <=? 2990080)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((2990080 <=? a) && (a + 1 <=? 3207168)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ro_none (m : word -> option byte) (a : Z) : mem_inv ctpsegs m -> 65536 <= a < 905216 -> m (wa a) = None.
Proof.
  intros MI Ha. destruct (m (wa a)) as [b|] eqn:E; [|reflexivity]. pose proof (mem_inv_ro ctpsegs m _ _ MI E) as H.
  rewrite (ro_addr_seg0 a Ha) in H. discriminate.
Qed.
