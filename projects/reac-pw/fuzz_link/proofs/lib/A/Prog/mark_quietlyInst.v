(* mark_quietly (fuzz_link.asan 0x883d4) at link's image-A instance, every Section hypothesis discharged: the two
   arms of lib/A/Prog/mark_quietly_c.v at B := AD2l.PcapB, SK := AMemFile.link_asink_head, PI := LinkImgInst.v
   PI_link (so pa_segs = tfibsegs), MT := YCbp.ameter_triv, for the slot's closing
   (lib/A/Prog/LLVMFuzzerTestOneInputClose.v), so that it does not re-assemble the mark chain.

   The chain closed here: mark_quietly's two walks (mark_quietlyAgain.v, mark_quietlyOpen.v) take fmemopen,
   rewind, reac_served_say_to and reac_served_mark; reac_served_mark's walk (reac_served_mark.v) takes
   frame_alloc_3, meta_fill_f5, wrapper_bcmp, wrapper_fprintf and five own callees: reac_link_alias_read /
   reac_link_alias_write, reac_served_decide (model_decide.v), remember and
   reac_code_emit; the two alias walks take fuzz_if_nametoindex (LinkWalkKernInst.v) and nl_talk, whose walk
   (nl_talk.v) takes fuzz_close, fuzz_socket, fuzz_send, fuzz_recv, copy_attr and the class-9 side stack. Every
   runtime realization is its owner's closed lemma at tfibsegs / PcapB (named at each `i_*` lemma below); the
   image instance is LinkImgInst.v's pi_link_vals / pi_link_segs; AR's laws are YG0q.AR_laws_ok; PALib is
   LinkPaLibInst.v PcapB_palib; PcapSyms is AD2l.PcapB_syms.

   The opening arm is stated for EVERY allocator-trace context list CTX (mark_quietly_aproof_open holds for all
   MO and CTX), so the slot applies it at its LF_CTX_link (LLVMFuzzerTestOneInputInst.v) without this file
   Requiring the slot's top; its LedPost is the text of LLVMFuzzerTestOneInputMqCall.v `mq_ledpost PcapB`
   (the wild count of the depot does not grow), which that definition unfolds to.

   Proves no function (kind: instance of mark_quietly's walks). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0o YI16 YM05 YC5d YCbp YG00 YG0f YG0n YG0d YCbq YG01 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef StackFreeDef AsStackSz.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PaTable PaSym PaRun LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2l AMemFile AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0s StackMalloc0 AE2q AE2r AE2s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtString LinkMfDefs LinkVfDefs LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkFoSpec LinkFoInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require
RtClosed RtStrcmpClosed RtErrnoLocClosed SetShadow StackSideInst LinkVfTop LinkSnp LinkRwAll LinkFoOk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkImgInst LinkPaLibInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
fuzz_close_c fuzz_socket_c fuzz_send_c fuzz_recv_c fuzz_if_nametoindex_c copy_attr_c nl_talk_c
reac_link_alias_read_c reac_link_alias_write_c model_decide_c reac_served_say_to_c
remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require
fuzz_close LinkWalkKernInst copy_attr nl_talk reac_link_alias_read reac_link_alias_write model_decide
reac_served_say_to remember reac_code_emit reac_served_mark mark_quietlyOrel mark_quietlyAgain mark_quietlyOpen.
Import ListNotations.
Open Scope Z_scope.

Section inst. Context {rc : YM05.RunCeil}.
#[local] Notation PIl := (@PI_link rc).
#[local] Notation SEGSl := (@pa_segs rc link_listing PIl).
#[local] Notation SK := link_asink_head.
#[local] Notation LAWS0 := (YG0q.AR_laws_ok tfibsegs PcapB).

(* checked_memset (0x53214) in YG0d.v's aintrin_realizes premise order: lib/A/AE2r.v asan_memset_realizes, whose
   statement takes the same premises with amem_range moved after the two shadow premises *)
Lemma i_amset : forall fy : YK11.FPState,
  aintrin_realizes (fx := fy) SEGSl PcapB OSet (@pa_sigma rc link_listing PIl LS___asan_memset).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___asan_memset) with 0x53214 by (vm_compute; reflexivity).
  intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
  eapply (AE2r.asan_memset_realizes (fx := fy) PcapB LAWS0 PcapB_syms); eassumption.
Qed.

(* frame_alloc_3's entry is the class-3 row of the frame's code table (AF0l.v Tfib_code) *)
Lemma i_hsm3 : pc_stack_malloc (as_code PcapB) 3 = @pa_sigma rc link_listing PIl LS___asan_stack_malloc_3.
Proof. vm_compute. reflexivity. Qed.

(* one hypothesis of a walk at the instance, by its owner's closed lemma; a hypothesis stated at every FP state
   is introduced first *)
Ltac i_rt :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ exact LAWS0
  | exact pi_link_vals
  | exact PcapB_syms
  | exact pi_link_segs
  | exact (PcapB_palib pi_link_vals pi_link_segs)
  | exact i_hsm3
  | exact (i_amset _)
  | exact (StackMalloc0.stack_malloc0_contract PcapB LAWS0 PcapB_syms)
  | exact (AF0s.stack_malloc1_contract PcapB LAWS0 PcapB_syms)
  | exact (StackSideInst.link_stack_malloc_3 PcapB PcapB_syms)
  | exact (StackSideInst.link_stack_malloc_9 PcapB PcapB_syms)
  | exact (StackSideInst.link_stack_free_9 PcapB PcapB_syms)
  | exact (SetShadow.link_set_shadow_f5 PcapB LAWS0 PcapB_syms)
  | exact (SetShadow.link_set_shadow_f8 PcapB LAWS0 PcapB_syms)
  | exact (SetShadow.link_set_shadow_00 PcapB LAWS0 PcapB_syms)
  | exact (AE2s.bcmp_icpt_contract PcapB LAWS0 PcapB_syms)
  | exact (AE2q.asan_memcpy_realizes PcapB LAWS0 PcapB_syms)
  | exact (LinkVfTop.link_fprintf_mf_rel PCAP_RLO PCAP_RHI)
  | exact (LinkVfTop.link_vfprintf_mf_rel PCAP_RLO PCAP_RHI)
  | exact (RtStrcmpClosed.link_strcmp_closed PcapB PcapB_syms)
  | exact (RtClosed.cmd_strncmp_closed PcapB PcapB_syms)
  | exact (RtClosed.cmd_strlen_closed PcapB PcapB_syms)
  | exact (RtClosed.link_strnlenM_closed PcapB PcapB_syms)
  | exact (RtErrnoLocClosed.link_errno_location_closed PcapB)
  | exact LinkSnp.link_snprintf
  | exact LinkRwAll.link_arewind_ok
  | exact (LinkFoOk.afmemopen_w_ok_pcapb link_afmemopen_ctx)
  | exact link_amf_head_law
  | exact mark_quietlyOrel.mqo_univ0_pcapb
  | exact mark_quietlyOrel.mqo_univ1_pcapb
  | exact (fun (_ : astate) (_ : Z) => I)
  | exact (fun (_ _ : astate) (_ : Z) => I) ].

(* ---- the leaves of the chain ---- *)
Lemma i_fclose : forall fy : YK11.FPState,
  fuzz_close_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@fuzz_close.fuzz_close_aproof_pcap fy rc SK PIl PcapB); i_rt. Qed.
Lemma i_fso : forall fy : YK11.FPState,
  fuzz_socket_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_socket_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma i_fse : forall fy : YK11.FPState,
  fuzz_send_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_send_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma i_recv : forall fy : YK11.FPState,
  fuzz_recv_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_recv_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma i_fifn : forall fy : YK11.FPState,
  fuzz_if_nametoindex_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@LinkWalkKernInst.fuzz_if_nametoindex_aproof_pcapb fy rc SK PIl); i_rt. Qed.
Lemma i_ca : forall fy : YK11.FPState,
  copy_attr_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@copy_attr.copy_attr_aproof fy rc SK PIl PcapB); i_rt. Qed.
Lemma i_rst : forall fy : YK11.FPState,
  reac_served_say_to_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@reac_served_say_to.reac_served_say_to_aproof_pcap fy rc SK PIl PcapB); i_rt. Qed.
Lemma i_hdc : forall fy : YK11.FPState,
  reac_served_decide_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@model_decide.reac_served_decide_aproof fy rc SK PIl PcapB); i_rt. Qed.

(* ---- nl_talk and the two alias walks ---- *)
Ltac i_own :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ i_rt
  | exact (i_fclose _) | exact (i_fso _) | exact (i_fse _) | exact (i_recv _) | exact (i_fifn _)
  | exact (i_ca _) | exact (i_rst _) | exact (i_hdc _) ].

Lemma i_nlt : forall fy : YK11.FPState,
  nl_talk_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@nl_talk.nl_talk_aproof fy rc SK PIl PcapB); i_own. Qed.
Lemma i_hrd : forall fy : YK11.FPState,
  reac_link_alias_read_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. apply (@reac_link_alias_read.reac_link_alias_read_aproof fy rc SK PIl PcapB);
    first [i_own | exact (i_nlt _)].
Qed.
Lemma i_hwr : forall fy : YK11.FPState,
  reac_link_alias_write_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. apply (@reac_link_alias_write.reac_link_alias_write_aproof fy rc SK PIl PcapB);
    first [i_own | exact (i_nlt _)].
Qed.

(* ---- this slice's walks ---- *)
Lemma i_hrm : forall fy : YK11.FPState,
  remember_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@remember.remember_aproof fy rc SK PIl PcapB); i_rt. Qed.
Lemma i_hem : forall fy : YK11.FPState,
  reac_code_emit_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@reac_code_emit.reac_code_emit_aproof fy rc SK PIl PcapB); i_rt. Qed.

Ltac i_mark :=
  repeat match goal with |- forall _ : YK11.FPState, _ => intro end;
  first
  [ i_own
  | exact (i_nlt _) | exact (i_hrd _) | exact (i_hwr _) | exact (i_hrm _) | exact (i_hem _) ].

Lemma i_rsm : forall fy : YK11.FPState,
  reac_served_mark_acontract (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. apply (@reac_served_mark.reac_served_mark_aproof fy rc SK PIl PcapB); i_mark. Qed.

(* ---- mark_quietly's two arms, at the image's program tables ---- *)
Lemma i_mq_again : forall fy : YK11.FPState,
  mark_quietly_acontract_again (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. apply (@mark_quietlyAgain.mark_quietly_aproof_again fy rc SK PIl PcapB);
    first [i_mark | exact (i_rsm _)].
Qed.

Lemma i_mq_open : forall (fy : YK11.FPState) (CTX : list (list Z)),
  mark_quietly_acontract_open (fx := fy) SK SEGSl PCAP_RLO PCAP_RHI PcapB ameter_triv
    (mo_malloc ameter_triv AMF_BLOCK) CTX (fun _ => True)
    (fun Sc S2 => (length (wild_part (as_universe PcapB) (st_depot S2))
                   <= length (wild_part (as_universe PcapB) (st_depot Sc)))%nat).
Proof.
  intros fy CTX. apply (@mark_quietlyOpen.mark_quietly_aproof_open fy rc SK PIl PcapB);
    first [i_mark | exact (i_rst _) | exact (i_rsm _)].
Qed.

(* ---- THE TWO INSTANCES, at link's segments ---- *)
Theorem mark_quietly_aproof_again_pcapb : forall fy : YK11.FPState,
  @mark_quietly_acontract_again fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (i_mq_again fy). Qed.

Theorem mark_quietly_aproof_open_pcapb : forall (fy : YK11.FPState) (CTX : list (list Z)),
  @mark_quietly_acontract_open fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB ameter_triv
    (mo_malloc ameter_triv AMF_BLOCK) CTX (fun _ => True)
    (fun Sc S2 => (length (wild_part (as_universe PcapB) (st_depot S2))
                   <= length (wild_part (as_universe PcapB) (st_depot Sc)))%nat).
Proof. intros fy CTX. exact (i_mq_open fy CTX). Qed.

(* reac_served_mark at the instance too, for any other caller of the chain *)
Theorem reac_served_mark_aproof_pcapb : forall fy : YK11.FPState,
  @reac_served_mark_acontract fy rc link_asink_head tfibsegs PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (i_rsm fy). Qed.

End inst.

About mark_quietly_aproof_again_pcapb.
About mark_quietly_aproof_open_pcapb.
Print Assumptions mark_quietly_aproof_again_pcapb.
Print Assumptions mark_quietly_aproof_open_pcapb.
Print Assumptions reac_served_mark_aproof_pcapb.
