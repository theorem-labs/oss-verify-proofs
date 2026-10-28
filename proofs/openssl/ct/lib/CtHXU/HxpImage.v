(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Image.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation ctusegs := ImageCt.ctusegs.

Definition seg0 := Ubsan_segment_000.
Definition seg1 := Ubsan_segment_001.
Definition seg2 := Ubsan_segment_002.
Definition seg3 := Ubsan_segment_003.

Lemma psegs_eq : ctusegs = [seg0; seg1; seg2; seg3].
Proof. reflexivity. Qed.

Local Ltac seg_consts :=
  replace (Z.of_N (seg_base Ubsan_segment_000)) with 65536%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Ubsan_segment_000)) with 856064%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Ubsan_segment_001)) with 921600%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Ubsan_segment_001)) with 1970176%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Ubsan_segment_002)) with 2891776%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Ubsan_segment_002)) with 380928%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base Ubsan_segment_003)) with 3272704%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size Ubsan_segment_003)) with 221184%Z by (vm_compute; reflexivity).

(* [comment removed for export] *)
Lemma find_seg : forall a n, 1 <= n ->
  find_segment ctusegs a n =
    if (65536 <=? a) && (a + n <=? 921600) then Some seg0
    else if (921600 <=? a) && (a + n <=? 2891776) then Some seg1
    else if (2891776 <=? a) && (a + n <=? 3272704) then Some seg2
    else if (3272704 <=? a) && (a + n <=? 3493888) then Some seg3
    else None.
Proof.
  intros a n Hn. unfold ctusegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments.
  cbn [find_segment]. seg_consts. reflexivity.
Qed.

Lemma seg0_ro : seg_writable seg0 = false. Proof. vm_compute. reflexivity. Qed.
Lemma seg0_rd : seg_readable seg0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg2_wr : seg_writable seg2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg2_rd : seg_readable seg2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg3_wr : seg_writable seg3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg3_rd : seg_readable seg3 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ro_addr_seg0 : forall a, 65536 <= a < 921600 -> ro_addr ctusegs (wa a) = true.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 921600)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  rewrite seg0_ro. reflexivity.
Qed.

(* [comment removed for export] *)
Definition chunk_of (sg : Segment) : PrimString.string := match seg_bytes sg with [c] => c | _ => PrimString.make 0%uint63 0%uint63 end.
Lemma seg0_chunk : seg_bytes seg0 = [chunk_of seg0]. Proof. reflexivity. Qed.
Lemma seg2_chunk : seg_bytes seg2 = [chunk_of seg2]. Proof. reflexivity. Qed.
Lemma seg3_chunk : seg_bytes seg3 = [chunk_of seg3]. Proof. reflexivity. Qed.

Lemma find_seg0_in : forall a, 65536 <= a < 921600 -> find_segment ctusegs a 1 = Some seg0.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 921600)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma find_seg2_in : forall a, 2891776 <= a < 3272704 -> find_segment ctusegs a 1 = Some seg2.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 921600)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((921600 <=? a) && (a + 1 <=? 2891776)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((2891776 <=? a) && (a + 1 <=? 3272704)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma find_seg3_in : forall a, 3272704 <= a < 3493888 -> find_segment ctusegs a 1 = Some seg3.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 921600)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((921600 <=? a) && (a + 1 <=? 2891776)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((2891776 <=? a) && (a + 1 <=? 3272704)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((3272704 <=? a) && (a + 1 <=? 3493888)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ro_none (m : word -> option byte) (a : Z) : mem_inv ctusegs m -> 65536 <= a < 921600 -> m (wa a) = None.
Proof.
  intros MI Ha. destruct (m (wa a)) as [b|] eqn:E; [|reflexivity]. pose proof (mem_inv_ro ctusegs m _ _ MI E) as H.
  rewrite (ro_addr_seg0 a Ha) in H. discriminate.
Qed.
