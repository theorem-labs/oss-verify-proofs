(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PcapRoBridges.v (a working branch
   ce45cce9434), new file for libreac/fuzz_pcap: the frame law of lib/Reusable/YE3i.v's read-only-image fact ro_img
   that lib/B/Prog/PcapFuzzFopen.v takes as its hypothesis ROIMG_LOW (a working branch c2236e094d0,
   :151, at roimg := YE3i.ro_img); no function walk. Module paths lib.A AB1v / AE3i -> lib.Reusable YB1v / YE3i.
   - pcap_roimg_low (ROIMG_LOW, `roimg_low SEGS roimg` at SEGS := tfibsegs, roimg := ro_img, unfolded): ro_img
     depends only on the bytes below alloc_ceiling. The proof is lib/A/PcapRoBridges.v's: the donor kit's
     lib/Reusable/YI04.v region_ok_transport (cgif lib/YI04.v) at E' := E on img_ro_region, whose window
     [IMG_RO_LO, IMG_RO_HI) = [0x10000, 0x2efc0) (the read-only PT_LOAD of fuzz_pcap.asan-ubsan) lies below
     alloc_ceiling (>= CEIL_MIN, lib/Reusable/YM05.v), whose chunks are all CImg (YE3i.img_ro_chunks_inside) and which
     has no writable part.
   - lib/A's pcap_roimg_kept (the A entry instance's ROIMG_KEPT, over lib/A/PcapGHarness.v's ro_chunk_addr) has no
     twin here: no lib/B file takes ROIMG_KEPT (lib/B on a working branch c2236e094d0,
     a working branch 55b41c87e3c and a working branch a1e18bc20b7, 2026-10-29; the B open
     walk lib/B/Prog/PcapSourceOpen.v takes its own keep law ROK instead).
   The lemma is stated at segs := tfibsegs (lib/Reusable/YB1v.v, = AsanUbsan.M.loaded_segments); the lib/B top states
   it at pa_segs of its PAImg instance, which reduces to the same segments. The Check at the end of the section has
   the kernel compare the lemma's type with ROIMG_LOW's. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YE3i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
(* ROIMG_LOW (lib/B/Prog/PcapFuzzFopen.v roimg_low tfibsegs ro_img, unfolded): YI04.region_ok_transport on
   img_ro_region. *)
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
(* The type of the hypothesis ROIMG_LOW of lib/B/Prog/PcapFuzzFopen.v:151 (a working branch c2236e094d0),
   `roimg_low SEGS roimg`, at SEGS := tfibsegs and roimg := ro_img. roimg_low is that file's Definition at :75-77, its
   body copied here word for word as the function below (that file is not in this tree, so it cannot be Required).
   The kernel checks that pcap_roimg_low has this type. *)
Check (pcap_roimg_low : (fun (segs : list Segment) (roimg : (word -> option byte) -> Prop) =>
forall m m' : word -> option byte,
(forall a, 0 <= a < alloc_ceiling -> mbyte segs m' a = mbyte segs m a) -> roimg m -> roimg m') tfibsegs ro_img).
End d.
