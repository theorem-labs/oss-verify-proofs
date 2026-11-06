(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: it computes the lowest and the highest
   address the loaded segments of the ASan image cover and compares them with lib/Reusable/YImgTop.v's IMG_LO
   and IMG_TOP (the latter is also Reusable/PcapImgEnd.v's pcap_img_end). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YImgTop.
Local Open Scope Z_scope.

(* The highest address any loaded segment of the ASan image covers. *)
Definition pcap_img_last_end : Z :=
  fold_left (fun m s => Z.max m (Z.of_N (seg_base s) + Z.of_N (seg_size s))) Asan.M.loaded_segments 0.

(* The lowest address any loaded segment of the ASan image covers. *)
Definition pcap_img_first_base : Z :=
  fold_left (fun m s => Z.min m (Z.of_N (seg_base s))) Asan.M.loaded_segments (2 ^ 64).

Theorem pcap_img_top_is_image_end : YImgTop.IMG_TOP = 4096 * ((pcap_img_last_end + 4095) / 4096).
Proof. vm_compute. reflexivity. Qed.

Theorem pcap_img_top_past_image : pcap_img_last_end <= YImgTop.IMG_TOP < pcap_img_last_end + 4096.
Proof. vm_compute. split; [discriminate | reflexivity]. Qed.

Theorem pcap_img_lo_is_image_base : YImgTop.IMG_LO = pcap_img_first_base.
Proof. vm_compute. reflexivity. Qed.

Theorem pcap_img_end_is_img_top : pcap_img_end = YImgTop.IMG_TOP.
Proof. reflexivity. Qed.
