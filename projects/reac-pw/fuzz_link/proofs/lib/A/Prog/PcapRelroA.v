(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan IMAGE's half of lib/A/Prog/PcapRelro.v, split out so that PcapRelro.v
   names no image and a lib/B file may Require it for PCAP_RLO / PCAP_RHI (a Theorem Labs lane's closure audit; the twin
   test flagged PcapRelro.v:28,32's `Asan.M.loaded_segments`). pcap_relro_in_image checks, by vm_compute over the
   image module the build loads, that the read-only window [PCAP_RLO, PCAP_RHI) lies inside one loaded segment of
   the original v1.9.0 ASan pin (fuzz_pcap.asan sha256 b7a91d9b1fb0017d: .data.rel.ro 0x992d0 .. 0x997d0,
   .got 0x997d0 .. 0x9a528). *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
Import ListNotations.
Open Scope Z_scope.

Lemma pcap_relro_in_image_b : existsb (relro_in_seg PCAP_RLO PCAP_RHI) Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pcap_relro_in_image :
  exists s, In s Asan.M.loaded_segments /\
    Z.of_N (seg_base s) <= PCAP_RLO /\ PCAP_RLO < PCAP_RHI /\ PCAP_RHI <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  destruct (proj1 (existsb_exists _ _) pcap_relro_in_image_b) as (s & Hin & H).
  unfold relro_in_seg in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  exists s. split; [exact Hin|].
  split; [apply Z.leb_le; exact H1|]. split; [apply Z.ltb_lt; exact H2|]. apply Z.leb_le; exact H3.
Qed.
