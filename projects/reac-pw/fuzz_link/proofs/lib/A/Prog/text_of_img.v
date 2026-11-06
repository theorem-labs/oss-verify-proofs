(* text_of on image A at the image's asyms record PcapB (lib/A/AD2l.v) and the trivial meter (lib/Reusable/YCbp.v
   ameter_triv), every Section hypothesis of lib/A/Prog/text_of.v discharged: the allocator laws by
   lib/Reusable/YG0q.v AR_laws_ok, PALib by LinkPaLibInst.v PcapB_palib, the meter's laws by YCbp.v ameter_triv_laws,
   PcapSyms by AD2l.PcapB_syms, memchr by lib/A/Rt/RtClosed.v link_memchrM_closed and LinkWalkMemchr.v link_mc_ro,
   the wild malloc rule by lib/A/Rt/LinkMallocDepotWA.v PcapB_AMALLOC4_DW, checked_memcpy by lib/A/AE2q.v
   asan_memcpy_realizes.
   - text_of_aproof_img: what stays is the image instance (PI with LinkVals and pa_segs = tfibsegs);
   - text_of_aproof_pcapb: at link's instance (LinkImgInst.v PI_link), in the shape the slot's closing applies.

   This file is kept apart from text_of.v because LinkMallocDepotWA.v's closure is long to build.

   Proves text_of (kind: function proof, at the image's asyms). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0n YC20 YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkAddr LinkPa
  LinkPaLib LinkWalk LinkPaLibInst PcapRelro LinkImgInst LinkWalkMemchr link_amem text_of_c text_ofDefs text_of.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE2q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtClosed LinkMallocDepotWA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Open Scope Z_scope.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Hypothesis LV : LinkVals.
Hypothesis HSEGS : pa_segs = tfibsegs.

Theorem text_of_aproof_img : forall CTX rlo rhi, text_of_acontract SK pa_segs rlo rhi PcapB ameter_triv CTX.
Proof.
intros CTX.
assert (LAWS : AR_laws pa_segs PcapB) by (rewrite HSEGS; exact (YG0q.AR_laws_ok tfibsegs PcapB)).
apply (text_of_aproof SK PcapB ameter_triv CTX LAWS (PcapB_palib LV HSEGS) LV ameter_triv_laws PcapB_syms).
- rewrite (lv_sigma LV). cbn [link_sigma]. rewrite HSEGS. exact (RtClosed.link_memchrM_closed PcapB PcapB_syms).
- rewrite HSEGS. exact (link_mc_ro PcapB PcapB_syms).
- rewrite HSEGS. exact (LinkMallocDepotWA.PcapB_AMALLOC4_DW (SK := SK)).
- rewrite (lv_sigma LV). cbn [link_sigma]. rewrite HSEGS.
  exact (AE2q.asan_memcpy_realizes PcapB (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms).
- exact HSEGS.
Qed.
End inst.

Section link. Context {rc : YM05.RunCeil}.
Theorem text_of_aproof_pcapb : forall (fy : YK11.FPState) CTX,
  @text_of_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB ameter_triv CTX.
Proof.
intros fy CTX.
pose proof (@text_of_aproof_img fy rc link_asink_head PI_link pi_link_vals pi_link_segs CTX PCAP_RLO PCAP_RHI) as H.
rewrite pi_link_segs in H. exact H.
Qed.
End link.

Print Assumptions text_of_aproof_img.
Print Assumptions text_of_aproof_pcapb.
