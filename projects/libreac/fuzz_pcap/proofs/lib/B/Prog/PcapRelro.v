(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: libreac/fuzz_pcap (libreac v1.9.0, ASan build): the read-only window RLO / RHI that
   pcap's ASan statements pass (obligation row 5; the donor passes 0x9da38 / 0x9eca8, cgif_file_fuzzer lib/A/AD2o.v:45-47,
   AB1w.v:11-14, ACeg.v:42-44 in_ro_tfa).
   The donor's rule, measured on both donor images (cgif_file_fuzzer.asan sha256 7093581aab040cfd: .data.rel.ro
   0x9da38.., .got ..0x9eca8; .asan-ubsan 1c29845fe6058de6: 0x9dca8 .. 0x9ef18): RLO = the start of .data.rel.ro (the
   RELRO segment past .init_array / .fini_array / .preinit_array), RHI = the end of .got (the RELRO segment before
   .relro_padding). The same rule on pcap's ORIGINAL v1.9.0 pins:
     fuzz_pcap.asan       (sha256 b7a91d9b1fb0017d): .data.rel.ro 0x992d0 .. 0x997d0, .got 0x997d0 .. 0x9a528
                          (PT_GNU_RELRO 0x99298 .. 0x9b000)  -> RLO = 0x992d0, RHI = 0x9a528
     fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a): .data.rel.ro 0x99198 .. 0x99698, .got 0x99698 .. 0x9a3f0
                          (PT_GNU_RELRO 0x99160 .. 0x9b000)  -> RLO = 0x99198, RHI = 0x9a3f0 (lib/B's owner states it)
   pcap_relro_in_image checks, by computation over the image module the build loads, that the window lies inside one
   loaded segment. *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapRelro.v for fuzz_pcap.asan-ubsan (v1.9.0, pin sha256
   9e66f771f22af67a, the image the build loads as AsanUbsan): the same rule gives RLO = 0x99198 (start of .data.rel.ro)
   and RHI = 0x9a3f0 (end of .got), re-measured from the pin's section headers (.data.rel.ro 0x99198 .. 0x99698, .got
   0x99698 .. 0x9a3f0, inside the PT_LOAD 0x99160 .. 0x9b000); pcap_relro_in_image checks them against AsanUbsan. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
Import ListNotations.
Open Scope Z_scope.

Definition PCAP_RLO : Z := Eval compute in Symbols.AsanUbsan.Sec.s_data_rel_ro.
Definition PCAP_RHI : Z := Eval compute in (Symbols.AsanUbsan.Sec.s_got + Symbols.AsanUbsan.Sec.Size.s_got)%Z.

Definition relro_in_seg (lo hi : Z) (s : Segment) : bool :=
  (Z.of_N (seg_base s) <=? lo) && (lo <? hi) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)).

Lemma pcap_relro_in_image_b : existsb (relro_in_seg PCAP_RLO PCAP_RHI) AsanUbsan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pcap_relro_in_image :
  exists s, In s AsanUbsan.M.loaded_segments /\
    Z.of_N (seg_base s) <= PCAP_RLO /\ PCAP_RLO < PCAP_RHI /\ PCAP_RHI <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  destruct (proj1 (existsb_exists _ _) pcap_relro_in_image_b) as (s & Hin & H).
  unfold relro_in_seg in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  exists s. split; [exact Hin|].
  split; [apply Z.leb_le; exact H1|]. split; [apply Z.ltb_lt; exact H2|]. apply Z.leb_le; exact H3.
Qed.
