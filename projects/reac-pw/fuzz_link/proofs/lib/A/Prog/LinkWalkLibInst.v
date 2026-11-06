(* reac-pw/fuzz_link, image A: the five library walks at link's image-A instance, every Section hypothesis
   discharged: copy_attr, nl_talk, reac_link_alias_read, reac_link_alias_write and reac_served_unmark_all at
   B := AD2l.PcapB, SK := AMemFile.link_asink_head, PI := LinkImgInst.v PI_link (so pa_segs = tfibsegs), for the
   slot's closing (lib/A/Prog/LLVMFuzzerTestOneInputClose.v). The form is that of
   lib/A/Prog/mark_quietlyInst.v; this file holds only the chain below reac_served_unmark_all, so it Requires no
   printf / fmemopen / allocator walk file.

   The chain closed here: reac_served_unmark_all's walk (reac_served_unmark_all.v) takes reac_link_alias_read,
   reac_link_alias_write, wrapper_bcmp, frame_alloc_3, meta_fill_f5 and checked_memset; the two alias walks take
   fuzz_if_nametoindex (LinkWalkKernInst.v), nl_talk, frame_alloc_1 / frame_alloc_3, meta_fill_f5, wrapper_strlen,
   checked_memset and checked_memcpy; nl_talk's walk takes fuzz_close (fuzz_close.v), fuzz_socket, fuzz_send,
   fuzz_recv (LinkWalkKernInst.v), copy_attr, ___errno_location, meta_fill_00 / f8 and the class-9 side stack;
   copy_attr's walk takes wrapper_strnlen and checked_memcpy. Each runtime realization is its owner's closed lemma
   at tfibsegs / PcapB (the `i_rt` list below); the image instance is LinkImgInst.v's pi_link_vals / pi_link_segs;
   AR's laws are YG0q.AR_laws_ok; PALib is LinkPaLibInst.v PcapB_palib; PcapSyms is AD2l.PcapB_syms.

   Proves no function (kind: instance of the walks of copy_attr, nl_talk, reac_link_alias_read,
   reac_link_alias_write and reac_served_unmark_all). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0o YI16 YM05 YG00 YG0f YG0n YG0d YCbq YG01 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef StackFreeDef AsStackSz.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PaTable PaSym PaRun LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0s AE2q AE2r AE2s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtClosed RtErrnoLocClosed SetShadow StackSideInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkImgInst LinkPaLibInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
fuzz_close_c fuzz_socket_c fuzz_send_c fuzz_recv_c fuzz_if_nametoindex_c copy_attr_c nl_talk_c
reac_link_alias_read_c reac_link_alias_write_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require
fuzz_close LinkWalkKernInst copy_attr nl_talk reac_link_alias_read reac_link_alias_write reac_served_unmark_all.
Import ListNotations.
Open Scope Z_scope.

Section inst. Context {rc : YM05.RunCeil}.
#[local] Notation PIl := (@PI_link rc).
#[local] Notation SEGSl := (@pa_segs rc link_listing PIl).
#[local] Notation SK := link_asink_head.
#[local] Notation LAWS0 := (YG0q.AR_laws_ok tfibsegs PcapB).

(* checked_memset (0x53214) in YG0d.v's aintrin_realizes premise order: lib/A/AE2r.v asan_memset_realizes, whose
   statement takes the same premises with amem_range moved after the two shadow premises *)
Lemma l_amset : forall fy : YK11.FPState,
  aintrin_realizes (fx := fy) SEGSl PcapB OSet (@pa_sigma rc link_listing PIl LS___asan_memset).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___asan_memset) with 0x53214 by (vm_compute; reflexivity).
  intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
  eapply (AE2r.asan_memset_realizes (fx := fy) PcapB LAWS0 PcapB_syms); eassumption.
Qed.

(* frame_alloc_3's entry is the class-3 row of the frame's code table (AF0l.v Tfib_code) *)
Lemma l_hsm3 : pc_stack_malloc (as_code PcapB) 3 = @pa_sigma rc link_listing PIl LS___asan_stack_malloc_3.
Proof. vm_compute. reflexivity. Qed.

(* one hypothesis of a walk at the instance, by its owner's closed lemma; a hypothesis stated at every FP state is
   introduced first *)
Ltac i_rt :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ exact LAWS0
  | exact pi_link_vals
  | exact PcapB_syms
  | exact pi_link_segs
  | exact (PcapB_palib pi_link_vals pi_link_segs)
  | exact l_hsm3
  | exact (l_amset _)
  | exact (AF0s.stack_malloc1_contract PcapB LAWS0 PcapB_syms)
  | exact (StackSideInst.link_stack_malloc_3 PcapB PcapB_syms)
  | exact (StackSideInst.link_stack_malloc_9 PcapB PcapB_syms)
  | exact (StackSideInst.link_stack_free_9 PcapB PcapB_syms)
  | exact (SetShadow.link_set_shadow_f5 PcapB LAWS0 PcapB_syms)
  | exact (SetShadow.link_set_shadow_f8 PcapB LAWS0 PcapB_syms)
  | exact (SetShadow.link_set_shadow_00 PcapB LAWS0 PcapB_syms)
  | exact (AE2s.bcmp_icpt_contract PcapB LAWS0 PcapB_syms)
  | exact (AE2q.asan_memcpy_realizes PcapB LAWS0 PcapB_syms)
  | exact (RtClosed.cmd_strlen_closed PcapB PcapB_syms)
  | exact (RtClosed.link_strnlenM_closed PcapB PcapB_syms)
  | exact (RtErrnoLocClosed.link_errno_location_closed PcapB) ].

(* ---- the leaves: fuzz_close (the pilot walk), the kernel calls (the kernel-call walk), copy_attr ---- *)
Lemma l_fclose : forall fy : YK11.FPState,
  fuzz_close_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@fuzz_close.fuzz_close_aproof_pcap fy rc SK PIl PcapB); i_rt. Qed.
Lemma l_fso : forall fy : YK11.FPState,
  fuzz_socket_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_socket_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma l_fse : forall fy : YK11.FPState,
  fuzz_send_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_send_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma l_recv : forall fy : YK11.FPState,
  fuzz_recv_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_recv_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma l_fifn : forall fy : YK11.FPState,
  fuzz_if_nametoindex_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_if_nametoindex_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma l_ca : forall fy : YK11.FPState,
  copy_attr_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@copy_attr.copy_attr_aproof fy rc SK PIl PcapB); i_rt. Qed.

Ltac i_own :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ i_rt
  | exact (l_fclose _) | exact (l_fso _) | exact (l_fse _) | exact (l_recv _) | exact (l_fifn _)
  | exact (l_ca _) ].

(* ---- nl_talk and the two alias walks ---- *)
Lemma l_nlt : forall fy : YK11.FPState,
  nl_talk_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@nl_talk.nl_talk_aproof fy rc SK PIl PcapB); i_own. Qed.
Lemma l_hrd : forall fy : YK11.FPState,
  reac_link_alias_read_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. apply (@reac_link_alias_read.reac_link_alias_read_aproof fy rc SK PIl PcapB);
    first [i_own | exact (l_nlt _)].
Qed.
Lemma l_hwr : forall fy : YK11.FPState,
  reac_link_alias_write_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. apply (@reac_link_alias_write.reac_link_alias_write_aproof fy rc SK PIl PcapB);
    first [i_own | exact (l_nlt _)].
Qed.

(* ---- reac_served_unmark_all ---- *)
Lemma l_um : forall fy : YK11.FPState,
  reac_served_unmark_all_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. apply (@reac_served_unmark_all.reac_served_unmark_all_aproof fy rc SK PIl PcapB);
    first [i_own | exact (l_hrd _) | exact (l_hwr _)].
Qed.

(* ---- THE FIVE INSTANCES, at link's segments ---- *)
Theorem copy_attr_aproof_pcapb : forall fy : YK11.FPState,
  @copy_attr_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (l_ca fy). Qed.
Theorem nl_talk_aproof_pcapb : forall fy : YK11.FPState,
  @nl_talk_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (l_nlt fy). Qed.
Theorem reac_link_alias_read_aproof_pcapb : forall fy : YK11.FPState,
  @reac_link_alias_read_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (l_hrd fy). Qed.
Theorem reac_link_alias_write_aproof_pcapb : forall fy : YK11.FPState,
  @reac_link_alias_write_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (l_hwr fy). Qed.
Theorem reac_served_unmark_all_aproof_pcapb : forall fy : YK11.FPState,
  @reac_served_unmark_all_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (l_um fy). Qed.

End inst.

About reac_link_alias_write_aproof_pcapb.
About reac_served_unmark_all_aproof_pcapb.
Print Assumptions copy_attr_aproof_pcapb.
Print Assumptions nl_talk_aproof_pcapb.
Print Assumptions reac_link_alias_read_aproof_pcapb.
Print Assumptions reac_link_alias_write_aproof_pcapb.
Print Assumptions reac_served_unmark_all_aproof_pcapb.
