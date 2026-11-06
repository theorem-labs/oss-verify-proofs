(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the PALib / PALibF / frame-flag subset of cgif c8557374ad2e lib/A/ACed.v
   (tfibX_PALib0 :77-87, tfibX_PALibF0 :105-114, tfibX_FFL :133-144), stated for libreac/fuzz_pcap's ASan build at
   B := PcapB (lib/A/AD2l.v) and the listing's image instance PI := PcapEntryTop.PI_pcap, each in the form of
   lib/A/Prog/PcapEntryInst.v's hypothesis (TL, TLF, FFL). Adapted:
   - PALib and PALibF are pcap's records (lib/A/Prog/PcapPaLib.v, lib/A/Prog/PcapFrame.v), which name fuzz_pcap.asan's
     objects (PcapAddr.v): the shadow-base GOT slot is object 1 and its cell object 15, the side-stack flag's GOT slot
     object 0 and its cell object 16. PALib has two fields more than the donor's (pal_got_uar, pal_uar_cell), proved
     by reflexivity as the donor's pal_got_shadow / pal_cell are; PALibF holds stack-malloc classes 0 and 1 (the
     donor's 1 and 2) and has no got_uar / uar_img fields (pcap derives them from PALib: PcapFrame.v palf_got_uar,
     palf_uar_img), so the donor's proof of those two fields has no counterpart here.
   - The donor's tfibX_env / tfibX_LAWS are lib/A/PcapBFacts.v PcapB_env / PcapB_LAWS, stated at tfibsegs
     (lib/A/AB1v.v); tfib_img_cover is lib/A/ACeh.v's, as in the donor (ACed.v:15 imports ACeh).
   - The donor's TFIB_IMG_LO / TFIB_IMG_END literals are ACeh's 0x10000 / pcap_img_end = YImgTop.IMG_TOP, and off_img
     is stated with YImgTop.IMG_LO / IMG_TOP (lib/Reusable/YCbq.v:792), so the proofs open those names for lia.
   - Each statement names its RunCeil, listing and image instance explicitly (the @ form PcapEntryInst.v uses). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v ACeh.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require AD2l PcapBFacts.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSyms PcapList PcapPa PcapPaLib PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntryTop.
Import ListNotations.
Local Open Scope Z_scope.

Section b. Context {rc : YM05.RunCeil}.

(* donor ACed.v:77-87 tfibX_PALib0, at PcapB and PI_pcap: PcapEntryInst.v's TL. *)
Lemma PcapB_PALib : @PALib rc pcap_listing (@PcapEntryTop.PI_pcap rc) AD2l.PcapB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact PcapBFacts.PcapB_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.

(* donor ACed.v:105-114 tfibX_PALibF0, at PcapB and PI_pcap: PcapEntryInst.v's TLF. *)
Lemma PcapB_PALibF : @PALibF rc pcap_listing (@PcapEntryTop.PI_pcap rc) AD2l.PcapB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. repeat split; first [ discriminate | left; discriminate | right; discriminate ].
Qed.

(* donor ACed.v:133-144 tfibX_FFL, at PcapB and pa_segs PI_pcap: PcapEntryInst.v's FFL. *)
Lemma PcapB_FFL : @frame_flag_lawP rc (@pa_segs rc pcap_listing (@PcapEntryTop.PI_pcap rc)) AD2l.PcapB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ PcapBFacts.PcapB_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ PcapBFacts.PcapB_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil].
  unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

End b.
