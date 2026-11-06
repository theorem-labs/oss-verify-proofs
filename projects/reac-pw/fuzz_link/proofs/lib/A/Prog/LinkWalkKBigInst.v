(* attr_text (fuzz_link.asan 0x86b18), nl_error (0x86e4c) and kernel (0x83d30) at link's image-A instance, every
   Section hypothesis discharged: the walks lib/A/Prog/attr_text.v `attr_text_aproof`, lib/A/Prog/nl_error.v
   `nl_error_aproof` and lib/A/Prog/kernel.v `kernel_aproof` at B := AD2l.PcapB, SK := AMemFile.link_asink_head,
   PI := LinkImgInst.v PI_link (so pa_segs = tfibsegs), at the relro window PCAP_RLO / PCAP_RHI, in the shape of
   lib/A/Prog/mark_quietlyInst.v, for the slot's closing. kernel's own-callee hypotheses (attr_text, nl_error) are
   discharged by the two instances above it.

   Discharges: AR's laws YG0q.AR_laws_ok; LinkVals and pa_segs = tfibsegs LinkImgInst.v pi_link_vals /
   pi_link_segs; PALib LinkPaLibInst.v PcapB_palib; PcapSyms AD2l.PcapB_syms; kernel's image record
   kernel_img_tfib.v kernel_img_pcapB; wrapper_strlen (0x43044) lib/A/Rt/RtClosed.v cmd_strlen_closed;
   checked_memcpy (0x52d78) lib/A/AE2q.v asan_memcpy_realizes; checked_memset (0x53214) lib/A/AE2r.v
   asan_memset_realizes (premise order adapted by `ik_amset`); frame_alloc_1 (0x3da88) lib/A/AF0s.v
   stack_malloc1_contract; frame_alloc_8 (0x3df90) / frame_release_8 (0x3e10c) lib/A/Rt/StackSideInst.v
   link_stack_malloc_8 / link_stack_free_8; meta_fill_00 (0x55e74) / meta_fill_f8 (0x55f94) lib/A/Rt/SetShadow.v
   link_set_shadow_00 / link_set_shadow_f8.

   Proves no function (kind: instance of the attr_text, nl_error and kernel walks). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YI16 YM05 YG00 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PaTable PaSym PaRun LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0s AE2q AE2r.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtClosed StackSideInst SetShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkImgInst LinkPaLibInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import attr_text_c nl_error_c kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require attr_text nl_error kernel kernel_img_tfib.
Import ListNotations.
Open Scope Z_scope.

Section inst. Context {rc : YM05.RunCeil}.
#[local] Notation PIl := (@PI_link rc).
#[local] Notation SEGSl := (@pa_segs rc link_listing PIl).
#[local] Notation SK := link_asink_head.
#[local] Notation LAWS0 := (YG0q.AR_laws_ok tfibsegs PcapB).

(* checked_memset (0x53214) in YG0d.v's aintrin_realizes premise order: lib/A/AE2r.v asan_memset_realizes takes the
   same premises with amem_range after the two shadow premises *)
Lemma ik_amset : forall fy : YK11.FPState,
  aintrin_realizes (fx := fy) SEGSl PcapB OSet (@pa_sigma rc link_listing PIl LS___asan_memset).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___asan_memset) with 0x53214 by (vm_compute; reflexivity).
  intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
  eapply (AE2r.asan_memset_realizes (fx := fy) PcapB LAWS0 PcapB_syms); eassumption.
Qed.

(* one Section hypothesis of a walk at the instance, by its owner's closed lemma *)
Ltac ik_rt :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ exact LAWS0
  | exact pi_link_vals
  | exact PcapB_syms
  | exact pi_link_segs
  | exact (PcapB_palib pi_link_vals pi_link_segs)
  | exact (ik_amset _)
  | exact (AE2q.asan_memcpy_realizes PcapB LAWS0 PcapB_syms)
  | exact (AF0s.stack_malloc1_contract PcapB LAWS0 PcapB_syms)
  | exact (RtClosed.cmd_strlen_closed PcapB PcapB_syms) ].

Lemma ik_attr_text : forall fy : YK11.FPState,
  attr_text_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@attr_text.attr_text_aproof fy rc SK PIl PcapB); ik_rt. Qed.

Lemma ik_nl_error : forall fy : YK11.FPState,
  nl_error_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@nl_error.nl_error_aproof fy rc SK PIl PcapB); ik_rt. Qed.

(* ---- THE TWO INSTANCES, at link's segments ---- *)
Theorem attr_text_aproof_pcapb : forall fy : YK11.FPState,
  @attr_text_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (ik_attr_text fy). Qed.

Theorem nl_error_aproof_pcapb : forall fy : YK11.FPState,
  @nl_error_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (ik_nl_error fy). Qed.

(* one Section hypothesis of kernel's walk at the instance: the runtime callees, kernel's image record, and its two
   own callees by the instances above *)
Ltac ik_kn :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ ik_rt
  | exact kernel_img_tfib.kernel_img_pcapB
  | exact (StackSideInst.link_stack_malloc_8 PcapB PcapB_syms)
  | exact (StackSideInst.link_stack_free_8 PcapB PcapB_syms)
  | exact (SetShadow.link_set_shadow_00 PcapB LAWS0 PcapB_syms)
  | exact (SetShadow.link_set_shadow_f8 PcapB LAWS0 PcapB_syms)
  | exact (ik_attr_text _)
  | exact (ik_nl_error _) ].

Lemma ik_kernel : forall fy : YK11.FPState,
  kernel_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@kernel.kernel_aproof fy rc SK PIl PcapB); ik_kn. Qed.

Theorem kernel_aproof_pcapb : forall fy : YK11.FPState,
  @kernel_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (ik_kernel fy). Qed.

End inst.

About attr_text_aproof_pcapb.
About nl_error_aproof_pcapb.
About kernel_aproof_pcapb.
Print Assumptions attr_text_aproof_pcapb.
Print Assumptions nl_error_aproof_pcapb.
Print Assumptions kernel_aproof_pcapb.
