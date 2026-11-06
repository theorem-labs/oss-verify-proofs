(* text_buf on image A at the image's asyms record PcapB (lib/A/AD2l.v) and the trivial meter (lib/Reusable/YCbp.v
   ameter_triv), every Section hypothesis of lib/A/Prog/text_buf.v discharged: the allocator laws by
   lib/Reusable/YG0q.v AR_laws_ok, PALib by LinkPaLibInst.v PcapB_palib, the meter's laws by YCbp.v
   ameter_triv_laws, the malloc rule by lib/A/Rt/LinkMallocDepotA.v PcapB_AMALLOC4_D, checked_memset by lib/A/AE2r.v
   asan_memset_realizes (its statement asks no amem_range of the destination; the walk's hypothesis does, and is
   implied). What stays is the image instance itself: PI with the value table link's (LinkVals) and the segments the
   image's (pa_segs = tfibsegs); at link's instance (LinkImgInst.v PI_link) both are pi_link_vals / pi_link_segs.

   This file is kept apart from text_buf.v because LinkMallocDepotA.v's closure is long to build.

   Proves text_buf (kind: function proof, at the image's asyms). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkAddr LinkPa
  LinkPaLib LinkWalk LinkPaLibInst text_buf_c text_buf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AD2l AE2r.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkMallocDepotA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Open Scope Z_scope.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Hypothesis LV : LinkVals.
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.

Theorem text_buf_aproof_pcapb : forall CTX rlo rhi,
  text_buf_acontract SK pa_segs rlo rhi AD2l.PcapB ameter_triv CTX.
Proof.
intros CTX.
assert (LAWS : AR_laws pa_segs AD2l.PcapB) by (rewrite HSEGS; exact (YG0q.AR_laws_ok AB1v.tfibsegs AD2l.PcapB)).
apply (text_buf_aproof SK AD2l.PcapB ameter_triv CTX LAWS (PcapB_palib LV HSEGS) LV ameter_triv_laws).
- rewrite HSEGS. exact (LinkMallocDepotA.PcapB_AMALLOC4_D (SK := SK)).
- rewrite (lv_sigma LV). cbn [link_sigma]. rewrite HSEGS.
  intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
  eapply (AE2r.asan_memset_realizes AD2l.PcapB (YG0q.AR_laws_ok AB1v.tfibsegs AD2l.PcapB) AD2l.PcapB_syms);
    eassumption.
Qed.
End inst.

Print Assumptions text_buf_aproof.
Print Assumptions text_buf_aproof_pcapb.
