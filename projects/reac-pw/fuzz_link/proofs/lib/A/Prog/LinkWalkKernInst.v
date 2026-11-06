(* reac-pw/fuzz_link, image A: seventeen walks (listed below) at the image's asyms record PcapB (lib/A/AD2l.v), every
   Section hypothesis discharged: the allocator laws by lib/Reusable/YG0q.v AR_laws_ok, PALib by
   LinkPaLibInst.v PcapB_palib, the image's asyms record by AD2l.v PcapB_syms, ERRF by LinkWalkErrnoInst.v
   link_errno_not_static, and the callees by their closed contracts (each walk's _img corollary names them; for
   fuzz_recv, which has none: lib/A/Rt/RtErrnoLocClosed.v link_errno_location_closed, lib/A/AE2q.v
   asan_memcpy_realizes, lib/A/AE2r.v asan_memset_realizes). What stays is the image instance itself: its program
   tables (PI, with the value table link's: LinkVals, and the segments the image's: pa_segs = tfibsegs); at link's
   instance (LinkImgInst.v PI_link) both premises are pi_link_vals / pi_link_segs.

   Proves fuzz_socket, fuzz_send, fuzz_recv, fuzz_if_nametoindex, index_of, check_socket, check_refused,
   check_verdict, check_write, check_mark, check_bounds, check_read, check_requests, check_marks, talk, model_write, model_read (kind: function
   proof, at the image's asyms). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkAddr LinkPa
  LinkPaLib LinkWalk LinkWalkErrnoInst LinkPaLibInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  fuzz_socket_c fuzz_send_c fuzz_recv_c fuzz_if_nametoindex_c index_of_c check_socket_c check_refused_c
  check_verdict_c check_write_c check_mark_c check_bounds_c check_read_c check_requests_c check_marks_c talk_c model_write_c model_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require
  fuzz_socket fuzz_send_img fuzz_recv fuzz_if_nametoindex_img index_of check_socket check_refused check_verdict
  check_write check_mark check_bounds check_read check_requests check_marks talk model_write model_read.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AD2l AE2q AE2r.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtErrnoLocClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Open Scope Z_scope.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Hypothesis LV : LinkVals.
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.

#[local] Notation B := AD2l.PcapB.
Let TL : PALib B := PcapB_palib LV HSEGS.
Let TS : AF0m.PcapSyms B := AD2l.PcapB_syms.
Let LAWS : AR_laws pa_segs B.
Proof. rewrite HSEGS. exact (YG0q.AR_laws_ok AB1v.tfibsegs B). Qed.

Theorem fuzz_socket_aproof_pcapb : forall rlo rhi, fuzz_socket_acontract SK pa_segs rlo rhi B.
Proof. exact (fuzz_socket.fuzz_socket_aproof_img SK B TL LV TS HSEGS). Qed.
Theorem fuzz_send_aproof_pcapb : forall rlo rhi, fuzz_send_acontract SK pa_segs rlo rhi B.
Proof. exact (fuzz_send_img.fuzz_send_aproof_img SK B LAWS TL LV TS HSEGS). Qed.
Theorem fuzz_recv_aproof_pcapb : forall rlo rhi, fuzz_recv_acontract SK pa_segs rlo rhi B.
Proof.
apply (fuzz_recv.fuzz_recv_aproof SK B LAWS TL LV (link_errno_not_static B TS));
  rewrite (lv_sigma LV); cbn [link_sigma]; rewrite HSEGS.
- exact (RtErrnoLocClosed.link_errno_location_closed B).
- exact (AE2q.asan_memcpy_realizes B (YG0q.AR_laws_ok AB1v.tfibsegs B) TS).
- (* the frame's statement asks no amem_range of the destination: drop that premise *)
  intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
  eapply (AE2r.asan_memset_realizes B (YG0q.AR_laws_ok AB1v.tfibsegs B) TS); eassumption.
Qed.
Theorem fuzz_if_nametoindex_aproof_pcapb : forall rlo rhi, fuzz_if_nametoindex_acontract SK pa_segs rlo rhi B.
Proof. exact (fuzz_if_nametoindex_img.fuzz_if_nametoindex_aproof_img SK B TL LV TS HSEGS). Qed.
Theorem index_of_aproof_pcapb : forall rlo rhi, index_of_acontract SK pa_segs rlo rhi B.
Proof. exact (index_of.index_of_aproof_img SK B TL LV TS HSEGS). Qed.
Theorem check_socket_aproof_pcapb : forall rlo rhi, check_socket_acontract SK pa_segs rlo rhi B.
Proof. exact (check_socket.check_socket_aproof_img SK B LV HSEGS). Qed.
Theorem check_refused_aproof_pcapb : forall rlo rhi, check_refused_acontract SK pa_segs rlo rhi B.
Proof. exact (check_refused.check_refused_aproof_img SK B LV HSEGS). Qed.
Theorem check_verdict_aproof_pcapb : forall rlo rhi, check_verdict_acontract SK pa_segs rlo rhi B.
Proof. exact (check_verdict.check_verdict_aproof_img SK B LV HSEGS). Qed.
Theorem check_write_aproof_pcapb : forall rlo rhi, check_write_acontract SK pa_segs rlo rhi B.
Proof. exact (check_write.check_write_aproof_img SK B LV HSEGS). Qed.
Theorem check_mark_aproof_pcapb : forall rlo rhi, check_mark_acontract SK pa_segs rlo rhi B.
Proof. exact (check_mark.check_mark_aproof_img SK B LV HSEGS). Qed.
Theorem check_bounds_aproof_pcapb : forall rlo rhi, check_bounds_acontract SK pa_segs rlo rhi B.
Proof. exact (check_bounds.check_bounds_aproof_img SK B TL LV TS HSEGS). Qed.
Theorem check_read_aproof_pcapb : forall rlo rhi, check_read_acontract SK pa_segs rlo rhi B.
Proof. exact (check_read.check_read_aproof_img SK B LV TS HSEGS). Qed.
Theorem check_requests_aproof_pcapb : forall rlo rhi, check_requests_acontract SK pa_segs rlo rhi B.
Proof. exact (check_requests.check_requests_aproof_img SK B TL LV TS HSEGS). Qed.
Theorem check_marks_aproof_pcapb : forall rlo rhi, check_marks_acontract SK pa_segs rlo rhi B.
Proof. exact (check_marks.check_marks_aproof_img SK B TL LV TS HSEGS). Qed.
Theorem talk_aproof_pcapb : forall rlo rhi, talk_acontract SK pa_segs rlo rhi B.
Proof.
apply (talk.talk_aproof SK B LAWS TL LV).
rewrite (lv_sigma LV). cbn [link_sigma]. rewrite HSEGS.
exact (AE2q.asan_memcpy_realizes B (YG0q.AR_laws_ok AB1v.tfibsegs B) TS).
Qed.
Theorem model_write_aproof_pcapb : forall rlo rhi, model_write_acontract SK pa_segs rlo rhi B.
Proof. exact (model_write.model_write_aproof_img SK B LAWS TL LV TS HSEGS index_of_aproof_pcapb talk_aproof_pcapb). Qed.
Theorem model_read_aproof_pcapb : forall rlo rhi, model_read_acontract SK pa_segs rlo rhi B.
Proof. exact (model_read.model_read_aproof_img SK B LAWS TL LV TS HSEGS index_of_aproof_pcapb talk_aproof_pcapb). Qed.
End inst.

Print Assumptions fuzz_socket_aproof_pcapb.
Print Assumptions fuzz_send_aproof_pcapb.
Print Assumptions fuzz_recv_aproof_pcapb.
Print Assumptions fuzz_if_nametoindex_aproof_pcapb.
Print Assumptions index_of_aproof_pcapb.
Print Assumptions check_socket_aproof_pcapb.
Print Assumptions check_refused_aproof_pcapb.
Print Assumptions check_verdict_aproof_pcapb.
Print Assumptions check_write_aproof_pcapb.
Print Assumptions check_mark_aproof_pcapb.
Print Assumptions check_bounds_aproof_pcapb.
Print Assumptions check_read_aproof_pcapb.
Print Assumptions check_requests_aproof_pcapb.
Print Assumptions check_marks_aproof_pcapb.
Print Assumptions model_write_aproof_pcapb.
Print Assumptions model_read_aproof_pcapb.
Print Assumptions talk_aproof_pcapb.
