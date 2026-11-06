(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: two frame laws of lib/A/AE3i.v's read-only-image
   fact ro_img, in the form the A entry instance (lib/A/Prog/PcapEntryInst.v, at ROI := AE3i.ro_img and
   ro_chunk_addr := PcapGHarness.ro_chunk_addr) takes them; no function walk.
   - pcap_roimg_kept (the instance's ROIMG_KEPT): ro_img is kept when the bytes of AE3i.v's img_ro_chunks
     (PcapGHarness.ro_chunk_addr) read the same through mbyte. The proof is cgif c8557374ad2e lib/A/AE3i.v:72-81
     ro_img_kept (lib/A/AE3i.v:107-116 here), with its premise over the window [IMG_RO_LO, IMG_RO_HI) and mrestrict
     replaced by the premise over the chunk bytes and mbyte: the per-chunk step rewrites mbyte at c_off c + i, which is
     a chunk byte, instead of the restricted memory at the word Z_to_bv 64 (c_off c + i). The same statement is
     a working branch fec3976e6ce lib/A/Prog/PcapSourceOpenK.v:95 ro_img_chunks_kept, which does not build
     there (that tree has no AB1v.v / AE3i.v / PcapGHarness.v, so tfibsegs, ro_img and ro_chunk_addr are unbound); in
     this tree the file states it as a Hypothesis instead (PcapSourceOpenK.v:110, ROIMG_KEPT).
   - pcap_roimg_low (the instance's ROIMG_LOW, PcapFuzzFopenG.roimg_low tfibsegs ro_img unfolded): ro_img depends only
     on the bytes below alloc_ceiling. The proof is the donor kit's lib/Reusable/YI04.v region_ok_transport (cgif
     lib/YI04.v) at E' := E on img_ro_region, whose window [IMG_RO_LO, IMG_RO_HI) = [0x10000, 0x2ef70) lies below
     alloc_ceiling (>= CEIL_MIN, lib/Reusable/YM05.v), whose chunks are all CImg (AE3i.img_ro_chunks_inside) and which
     has no writable part. The donor has no roimg_low; only this composition is new text.
   Both are stated at segs := tfibsegs (lib/A/AB1v.v, = Asan.M.loaded_segments); the instance states them at
   pa_segs PI_pcap, which reduces to the same segments. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AE3i PcapGHarness.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
(* ROIMG_KEPT: donor cgif lib/A/AE3i.v:72-81 ro_img_kept, over the chunk bytes and mbyte. *)
Lemma pcap_roimg_kept : forall m m' : word -> option byte,
(forall a, ro_chunk_addr a -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> ro_img m -> ro_img m'.
Proof.
intros m m' Heq Hro E. pose proof (Hro E) as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [exact Hcb|].
revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l.
rewrite (Heq (YP09.c_off c + i)) by (unfold ro_chunk_addr; apply Exists_exists; exists c; split; [exact Hc | lia]).
intros Hmb. exact Hmb.
Qed.
(* ROIMG_LOW (PcapFuzzFopenG.roimg_low tfibsegs ro_img, unfolded): YI04.region_ok_transport on img_ro_region. *)
Lemma pcap_roimg_low : forall m m' : word -> option byte,
(forall a, 0 <= a < alloc_ceiling -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> ro_img m -> ro_img m'.
Proof.
intros m m' Heq Hro E. pose proof alloc_ceiling_value as [[CR _] _].
apply (region_ok_transport tfibsegs E E m m' img_ro_region (Hro E) eq_refl).
- intros c Hc. pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (_ & _ & n & Hv). rewrite Hv. exact I.
- intros a Ha. cbn [img_ro_region YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. unfold IMG_RO_LO, IMG_RO_HI in Ha.
  apply Heq. lia.
- intros a Ha _. cbn [img_ro_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
- vm_compute. reflexivity.
Qed.
End d.
