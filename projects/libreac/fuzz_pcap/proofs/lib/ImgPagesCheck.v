(* SPDX-License-Identifier: MIT *)
(* OSSV-267: lib/ImgPages.v names each build's page bounds from the sections of Symbols.v.  This file checks them
   against the image each build loads: the loaded segments are exactly [ro_lo, text_lo), [text_lo, relro_lo),
   [relro_lo, rw_lo) and [rw_lo, top), in that order.  A relink that lays an image out otherwise (another segment, a
   gap, a section that no longer opens or closes its segment) fails here, rather than give a proof a wrong bound. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.libreac.fuzz_pcap.images Require Plain Ubsan Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require ImgPages.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_pages segs : list (Z * Z) :=
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.

Theorem plain_pages :
  seg_pages OSSVerify.libreac.fuzz_pcap.images.Plain.M.loaded_segments =
  [(ImgPages.Plain.ro_lo, ImgPages.Plain.text_lo); (ImgPages.Plain.text_lo, ImgPages.Plain.relro_lo);
   (ImgPages.Plain.relro_lo, ImgPages.Plain.rw_lo); (ImgPages.Plain.rw_lo, ImgPages.Plain.top)].
Proof. vm_compute. reflexivity. Qed.

Theorem ubsan_pages :
  seg_pages OSSVerify.libreac.fuzz_pcap.images.Ubsan.M.loaded_segments =
  [(ImgPages.Ubsan.ro_lo, ImgPages.Ubsan.text_lo); (ImgPages.Ubsan.text_lo, ImgPages.Ubsan.relro_lo);
   (ImgPages.Ubsan.relro_lo, ImgPages.Ubsan.rw_lo); (ImgPages.Ubsan.rw_lo, ImgPages.Ubsan.top)].
Proof. vm_compute. reflexivity. Qed.

Theorem asan_pages :
  seg_pages OSSVerify.libreac.fuzz_pcap.images.Asan.M.loaded_segments =
  [(ImgPages.Asan.ro_lo, ImgPages.Asan.text_lo); (ImgPages.Asan.text_lo, ImgPages.Asan.relro_lo);
   (ImgPages.Asan.relro_lo, ImgPages.Asan.rw_lo); (ImgPages.Asan.rw_lo, ImgPages.Asan.top)].
Proof. vm_compute. reflexivity. Qed.

Theorem asan_ubsan_pages :
  seg_pages OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.loaded_segments =
  [(ImgPages.AsanUbsan.ro_lo, ImgPages.AsanUbsan.text_lo); (ImgPages.AsanUbsan.text_lo, ImgPages.AsanUbsan.relro_lo);
   (ImgPages.AsanUbsan.relro_lo, ImgPages.AsanUbsan.rw_lo); (ImgPages.AsanUbsan.rw_lo, ImgPages.AsanUbsan.top)].
Proof. vm_compute. reflexivity. Qed.
