(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: it computes the end of the ASan image's last
   loaded segment out of the image the build loads and compares it with lib/Reusable/PcapImgEnd.v's constant. *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- the asan-ubsan twin of lib/A/PcapImgEndCheck.v (a Theorem Labs lane), the same check
   over the asan-ubsan image (last PT_LOAD end 0x5f6070, page-rounded 0x5f7000, the same constant as asan). *)
(* Modified by Theorem Labs, 2026-10: lib/A/PcapImgEndCheck.v's two guards on lib/Reusable/YImgTop.v, over the
   asan-ubsan image: pcap_img_lo_is_image_base (IMG_LO = 0x10000, the lowest PT_LOAD p_vaddr of this image: 0x10000,
   0x2ffc0, 0x99160, 0x9b3f0) and pcap_img_end_is_img_top. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.libreac.fuzz_pcap.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YImgTop.
Local Open Scope Z_scope.

(* The highest address any loaded segment of the asan-ubsan image covers. *)
Definition pcap_img_last_end : Z :=
  fold_left (fun m s => Z.max m (Z.of_N (seg_base s) + Z.of_N (seg_size s))) AsanUbsan.M.loaded_segments 0.

(* The lowest address any loaded segment of the asan-ubsan image covers. *)
Definition pcap_img_first_base : Z :=
  fold_left (fun m s => Z.min m (Z.of_N (seg_base s))) AsanUbsan.M.loaded_segments (2 ^ 64).

Theorem pcap_img_end_is_image_end : pcap_img_end = 4096 * ((pcap_img_last_end + 4095) / 4096).
Proof. vm_compute. reflexivity. Qed.

Theorem pcap_img_end_past_image : pcap_img_last_end <= pcap_img_end < pcap_img_last_end + 4096.
Proof. vm_compute. split; [discriminate | reflexivity]. Qed.

Theorem pcap_img_lo_is_image_base : YImgTop.IMG_LO = pcap_img_first_base.
Proof. vm_compute. reflexivity. Qed.

Theorem pcap_img_end_is_img_top : pcap_img_end = YImgTop.IMG_TOP.
Proof. reflexivity. Qed.
