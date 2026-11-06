(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexZero. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanHexScan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexZero.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition RW_LO : Z := 0xa5000.

Lemma seg2_scan : scanN AsanUbsan_seg_bytes_002 64 0 0x2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma seg3_scan : scanN AsanUbsan_seg_bytes_003 64 0 0x55d000 = true.
Proof. (* [comment removed for export] *)
  apply (scanN_prefix_zwin AsanUbsan_seg_bytes_003 20480 0x55d000 (Uint63.of_Z 40960) (Uint63.of_Z 11206656)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma seg2_len : (0x2000 <= Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2))%N.
Proof. vm_compute. discriminate. Qed.
Lemma seg3_len : (0x55d000 <= Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2))%N.
Proof. vm_compute. discriminate. Qed.

Lemma seg2_w : seg_writable AsanUbsan_segment_002 = true. Proof. reflexivity. Qed.
Lemma seg3_w : seg_writable AsanUbsan_segment_003 = true. Proof. reflexivity. Qed.

Lemma rw_window_img : forall m (x : word), RW_LO <= bv_unsigned x < IMG_HI -> wview SEGS m x <> None.
Proof.
  intros m x Hx. unfold RW_LO, IMG_HI in Hx. unfold wview. destruct (m x) as [b|]; [discriminate|].
  unfold SEGS, IMGM.loaded_segments, AsanUbsan_loaded_segments.
  cbn [find_segment seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001].
  replace ((Z.of_N 65536 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 65536 + Z.of_N 139264))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((Z.of_N 204800 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 204800 + Z.of_N 471040))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  destruct (Z.lt_ge_cases (bv_unsigned x) 0xa7000) as [Hlo|Hhi].
  - cbn [find_segment seg_base seg_size AsanUbsan_segment_002].
    replace ((Z.of_N 675840 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 675840 + Z.of_N 8192))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite seg2_w. cbn [seg_bytes seg_base].
    apply (segment_byte_at_some1 _ 0x2000%N); [exact seg2_scan | exact seg2_len | cbn [seg_base AsanUbsan_segment_002]; rewrite Z2N.id by lia; lia].
  - cbn [find_segment seg_base seg_size AsanUbsan_segment_002].
    replace ((Z.of_N 675840 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 675840 + Z.of_N 8192))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    cbn [find_segment seg_base seg_size AsanUbsan_segment_003].
    replace ((Z.of_N 684032 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 684032 + Z.of_N 5623808))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite seg3_w. cbn [seg_bytes seg_base].
    apply (segment_byte_at_some1 _ 0x55d000%N); [exact seg3_scan | exact seg3_len | cbn [seg_base AsanUbsan_segment_003]; rewrite Z2N.id by lia; lia].
Qed.
