(* The closing of LLVMFuzzerTestOneInput's image-A walk: every Section hypothesis of the top
   (lib/A/Prog/LLVMFuzzerTestOneInput.v Section b) that is not a phase lemma, discharged at link's instance:
   the image PI_link (LinkImgInst.v), the asyms PcapB (AD2l.v), the sink head link_asink_head, the memory FILE
   link_amf, the driver's meter ameter_triv (LLVMFuzzerTestOneInputInst.v).

   Every hypothesis of the top is discharged here, among them text_of's contract TXO_C (close_txo_c, by
   text_of_img.v's text_of_aproof_pcapb) and the decide pair's realizations RSD_C / MDC_C (close_rsd / close_mdc,
   over the strncmp / strcmp wrappers' closed proofs).

   Proves no function (kind: instance of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK0o YI16 YM05 YC5d YCbp YG00 YG0f YG0n YG0d YCbq YG01 YGwildCount YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym PaRun LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2l AMemFile AMemFileSink ACej ACejSites.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA text_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkSnpDef LinkSnp SetShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepotA StackSideInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE2r PcapBFacts DecodeCalloc DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE2s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkBcmp model_read_c model_write_c LinkWalkKernLink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_write_c reac_served_unmark_all_c kernel_c
  LinkWalkLibInst LinkWalkKBigInst text_of_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_buf_c text_buf_img reac_link_alias_read_c
  check_bounds_c check_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepotCalloc LinkMallocDepotCallocA RtClosed RtStrcmpClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c model_decide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import check_socket_c check_socket check_refused_c check_refused
  check_write_c check_write index_of_c index_of check_marks_c LinkWalkKernInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietly_c mark_quietlyInst LLVMFuzzerTestOneInputMqCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs LinkImgInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkPaLibInst check_verdict_c check_verdict.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import check_mark_c check_mark check_requests_c check_requests.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputTxo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section inst. Context {rc : YM05.RunCeil}.
#[local] Notation PIl := (@PI_link rc).
#[local] Notation SEGSl := (@pa_segs rc link_listing PIl).

Lemma close_laws : AR_laws SEGSl PcapB.
Proof. exact (AR_laws_ok tfibsegs PcapB). Qed.
Lemma close_tb : PcapSyms PcapB.
Proof. exact PcapB_syms. Qed.
Lemma close_hsegs : SEGSl = tfibsegs.
Proof. exact pi_link_segs. Qed.
Lemma close_lv : LinkVals (PI := PIl).
Proof. exact pi_link_vals. Qed.
Lemma close_tl : PALib (PI := PIl) PcapB.
Proof. exact (PcapB_palib pi_link_vals pi_link_segs). Qed.

(* snprintf, at every FP state *)
Lemma close_snp : forall fy : YK11.FPState,
  @asnprintf_link_realizes fy rc SEGSl PcapB PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
Proof. intros fy. exact (@link_snprintf fy rc). Qed.

(* meta_fill_f5, at the address link's symbol table gives it *)
Lemma close_ass : forall fy : YK11.FPState,
  aset_shadow_realizes (fx := fy) SEGSl PcapB (@pa_sigma rc link_listing PIl LS___asan_set_shadow_f5) 0xf5.
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___asan_set_shadow_f5) with SSF5_ENTRY by (vm_compute; reflexivity).
  exact (@link_set_shadow_f5 fy rc PcapB (AR_laws_ok tfibsegs PcapB) PcapB_syms).
Qed.

(* the driver's meter *)
Lemma close_mt_ok : forall S m, mo_ok ameter_triv S m.
Proof. intros S m. exact I. Qed.
Lemma close_mt_le : forall S S' m, mo_le ameter_triv S S' m.
Proof. intros S S' m. exact I. Qed.

(* text_of's malloc trace: the fixed universe row [pc_malloc_ra0; 0x87ff0] *)
Lemma close_txo_tr : text_of_traces PcapB.
Proof. unfold text_of_traces. apply memZL_In. vm_compute. reflexivity. Qed.

(* the seven free sites' traces, with and without this call's frame record on the chain *)
Lemma close_trace_free : lf_trace_free PcapB.
Proof.
  intros ra b Hin. unfold lf_unwind, lf_ctx_tail.
  replace (pc_free_ra0 (as_code PcapB)) with 0x5420c by (vm_compute; reflexivity).
  replace (if b then [RA_LLVMF] else []) with (if b then [0x820c8] else []) by (destruct b; reflexivity).
  apply llvmf_site_in.
  cbn [LF_FREE_RAS In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; subst ra; lia.
Qed.

(* the free rules with the depot clause, at every FP state *)
Lemma close_afree : forall fy : YK11.FPState, afree04_rule_w (fx := fy) link_asink_head SEGSl PcapB ameter_triv.
Proof. intros fy. exact (@PcapB_AFREE4_D fy rc link_asink_head). Qed.
Lemma close_afree_null : forall fy : YK11.FPState,
  afree_null04_rule_w (fx := fy) link_asink_head SEGSl PcapB ameter_triv.
Proof. intros fy. exact (@PcapB_AFREE_NULL4_D fy rc link_asink_head). Qed.

(* check_verdict (its walk) *)
Lemma close_cv : forall fy : YK11.FPState,
  check_verdict_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (@check_verdict_aproof_img fy rc link_asink_head PIl PcapB pi_link_vals pi_link_segs _ _). Qed.

(* the texts table's strings and NULs are read-only image bytes (W3's span; lf_txo_ro) *)
Lemma close_txo_ro : forall i, (i < 11)%nat ->
  text_of_ro SEGSl PCAP_RLO PCAP_RHI PcapB (fst (nth i KP_TEXTS (0, [])))
    (Z.of_nat (length (snd (nth i KP_TEXTS (0, [])))) + 1).
Proof. exact (@lf_txo_ro rc PIl PcapB pi_link_segs PcapB_syms). Qed.

(* the two calloc sites' traces, with and without this call's frame record on the chain *)
Lemma close_trace_calloc : lf_trace_calloc PcapB 0x545a0.
Proof.
  intros ra b Hin. unfold lf_unwind, lf_ctx_tail.
  replace (if b then [RA_LLVMF] else []) with (if b then [0x820c8] else []) by (destruct b; reflexivity).
  apply llvmf_site_in.
  cbn [LF_CALLOC_RAS In] in Hin.
  destruct Hin as [H|[H|[]]]; subst ra; lia.
Qed.

(* check_mark and check_requests (their walks) *)
Lemma close_cm : forall fy : YK11.FPState,
  check_mark_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (@check_mark_aproof_img fy rc link_asink_head PIl PcapB pi_link_vals pi_link_segs _ _). Qed.
Lemma close_cr : forall fy : YK11.FPState,
  check_requests_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy.
  exact (@check_requests_aproof_img fy rc link_asink_head PIl PcapB (PcapB_palib pi_link_vals pi_link_segs)
           pi_link_vals PcapB_syms pi_link_segs _ _).
Qed.

(* frame_alloc_4 (the class-4 side frame) and checked_memset, at the image *)
Lemma close_asm4 : forall fy : YK11.FPState, astack_malloc_realizes (fx := fy) SEGSl PcapB 4.
Proof. intros fy. exact (link_stack_malloc_4 (fx := fy) PcapB PcapB_syms). Qed.
Definition close_cms (fy : YK11.FPState) :=
  asan_memset_realizes (fx := fy) PcapB (AR_laws_ok tfibsegs PcapB) PcapB_syms.

(* the calloc rule with its depot clause at the calloc wrapper's address and its return address
   inside the allocator *)
Lemma close_calloc : forall fy : YK11.FPState,
  acalloc04_rule_w (fx := fy) link_asink_head SEGSl PcapB ameter_triv
    (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_calloc) 0x545a0 8856 2192.
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_calloc) with DEC_A_wrap_calloc
    by (vm_compute; reflexivity).
  exact (link_acalloc04_d PcapB PcapB_syms PcapB_lib (fun t => eq_refl) (fx := fy) (rc := rc) (SK := link_asink_head)).
Qed.

(* reac_served_decide and model_decide (model_decide.v), over the strncmp and strcmp wrappers' closed realizations *)
Lemma close_strncmp : forall fy : YK11.FPState, RtString.astrncmp_realizes (fx := fy) SEGSl PcapB
  (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_strncmp).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_strncmp) with 0x43050 by (vm_compute; reflexivity).
  exact (cmd_strncmp_closed (fx := fy) PcapB PcapB_syms).
Qed.
Lemma close_strcmp : forall fy : YK11.FPState, RtString.astrcmp_realizes (fx := fy) SEGSl PcapB
  (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_strcmp).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_strcmp) with 0x4304c by (vm_compute; reflexivity).
  exact (link_strcmp_closed (fx := fy) PcapB PcapB_syms).
Qed.
Lemma close_rsd : forall fy : YK11.FPState,
  reac_served_decide_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. exact (reac_served_decide_aproof (fx := fy) link_asink_head PcapB close_laws close_tl close_lv
    (close_strncmp fy) (close_strcmp fy)).
Qed.
Lemma close_mdc : forall fy : YK11.FPState,
  model_decide_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. exact (model_decide_aproof (fx := fy) link_asink_head PcapB close_laws close_tl close_lv
    (close_strncmp fy) (close_strcmp fy)).
Qed.

(* op_unmark's and op_write's leaf callees (their walks) and the strlen wrapper *)
Lemma close_cs : forall fy : YK11.FPState,
  check_socket_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (check_socket_aproof_img (fx := fy) link_asink_head PcapB pi_link_vals pi_link_segs _ _). Qed.
Lemma close_cref : forall fy : YK11.FPState,
  check_refused_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (check_refused_aproof_img (fx := fy) link_asink_head PcapB pi_link_vals pi_link_segs _ _). Qed.
Lemma close_cwrite : forall fy : YK11.FPState,
  check_write_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (check_write_aproof_img (fx := fy) link_asink_head PcapB pi_link_vals pi_link_segs _ _). Qed.
Lemma close_index_of : forall fy : YK11.FPState,
  index_of_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof.
  intros fy. exact (index_of_aproof_img (fx := fy) link_asink_head PcapB (PcapB_palib pi_link_vals pi_link_segs)
    pi_link_vals PcapB_syms pi_link_segs _ _).
Qed.
Lemma close_cmk : forall fy : YK11.FPState,
  check_marks_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (check_marks_aproof_pcapb (fx := fy) link_asink_head pi_link_vals pi_link_segs _ _). Qed.
Lemma close_strlen : forall fy : YK11.FPState,
  RtString.astrlen_realizes (fx := fy) SEGSl PcapB (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_strlen).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_strlen) with 0x43044 by (vm_compute; reflexivity).
  exact (cmd_strlen_closed (fx := fy) PcapB PcapB_syms).
Qed.

(* mark_quietly's two arms (its instance file, every hypothesis discharged) *)
Lemma close_mqo : forall fy : YK11.FPState,
  @mark_quietly_acontract_open fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB ameter_triv
    (mo_malloc ameter_triv AMF_BLOCK) LF_CTX_link (fun _ => True) (mq_ledpost PcapB).
Proof. intros fy. exact (mark_quietly_aproof_open_pcapb fy LF_CTX_link). Qed.
Lemma close_mqa : forall fy : YK11.FPState,
  @mark_quietly_acontract_again fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (mark_quietly_aproof_again_pcapb fy). Qed.

(* the bcmp wrapper (the frame's AE2s.v bcmp_icpt_contract at its trampoline 0x4305c) *)
Lemma close_bcmp : forall fy : YK11.FPState,
  @abcmp_realizes fy rc SEGSl PcapB (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_bcmp).
Proof.
  intros fy.
  replace (@pa_sigma rc link_listing PIl LS___interceptor_trampoline_bcmp) with 0x4305c by (vm_compute; reflexivity).
  exact (AE2s.bcmp_icpt_contract (fx := fy) PcapB (AR_laws_ok tfibsegs PcapB) PcapB_syms).
Qed.

(* model_read and model_write (the kernel-call walk's instance file, every hypothesis discharged) *)
Lemma close_model_read : forall fy : YK11.FPState,
  @model_read_acontract fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (LinkWalkKernLink.model_read_aproof_pcapb fy). Qed.
Lemma close_model_write : forall fy : YK11.FPState,
  @model_write_acontract fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (LinkWalkKernLink.model_write_aproof_pcapb fy). Qed.

(* text_of (the kernel-call walk's instance file, every hypothesis discharged; generic in CTX, taken at LF_CTX_link) *)
Lemma close_txo_c : forall fy : YK11.FPState,
  text_of_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB ameter_triv LF_CTX_link.
Proof. intros fy. exact (text_of_img.text_of_aproof_pcapb fy LF_CTX_link). Qed.

(* kernel (LinkWalkKBigInst.v, every hypothesis discharged) *)
Lemma close_kernel : forall fy : YK11.FPState,
  @kernel_acontract fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (LinkWalkKBigInst.kernel_aproof_pcapb fy). Qed.

(* reac_link_alias_write and reac_served_unmark_all (LinkWalkLibInst.v, every hypothesis discharged) *)
Lemma close_alias_write : forall fy : YK11.FPState,
  @reac_link_alias_write_acontract fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (LinkWalkLibInst.reac_link_alias_write_aproof_pcapb fy). Qed.
Lemma close_unmark_all : forall fy : YK11.FPState,
  @reac_served_unmark_all_acontract fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (LinkWalkLibInst.reac_served_unmark_all_aproof_pcapb fy). Qed.

(* op_read's: text_buf (its instance), its malloc trace at the two calling sites (ACejSites
   text_buf_site_in), checked_memset in aintrin form, reac_link_alias_read (LinkWalkLib's instance), check_bounds and
   check_read (the kernel-call walk's instance) *)
Lemma close_txb_c : forall fy : YK11.FPState,
  text_buf_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB ameter_triv LF_CTX_link.
Proof.
  intros fy. exact (text_buf_img.text_buf_aproof_pcapb (fx := fy) link_asink_head pi_link_vals pi_link_segs
    LF_CTX_link _ _).
Qed.
Lemma close_txb_tr : text_buf_traces PcapB LF_CTX_link.
Proof.
  intros c Hc. apply in_app_or in Hc.
  destruct Hc as [Hc|Hc]; apply in_map_iff in Hc as (s & <- & _); cbn [tl];
    [exact (text_buf_site_in false) | exact (text_buf_site_in true)].
Qed.
Lemma close_amset : forall fy : YK11.FPState, aintrin_realizes (fx := fy) SEGSl PcapB OSet 0x53214.
Proof.
  intros fy ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
  exact (close_cms fy ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
Lemma close_alias_read : forall fy : YK11.FPState,
  @reac_link_alias_read_acontract fy rc link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (LinkWalkLibInst.reac_link_alias_read_aproof_pcapb fy). Qed.
Lemma close_cbnd : forall fy : YK11.FPState,
  check_bounds_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (check_bounds_aproof_pcapb (fx := fy) link_asink_head pi_link_vals pi_link_segs _ _). Qed.
Lemma close_cread : forall fy : YK11.FPState,
  check_read_acontract (fx := fy) link_asink_head SEGSl PCAP_RLO PCAP_RHI PcapB.
Proof. intros fy. exact (check_read_aproof_pcapb (fx := fy) link_asink_head pi_link_vals pi_link_segs _ _). Qed.

(* ==========================================================================
   THE WALK AT THE INSTANCE: lf_whole (LLVMFuzzerTestOneInput.v) with every Section hypothesis discharged above.
   ========================================================================== *)


Lemma close_whole : LF_WHOLE_A (rc := rc).
Proof.
  intros fx.
  eapply (@lf_whole fx rc link_asink_head PIl PcapB ameter_triv (fun _ : Z => 0) (fun _ : Z => 0) link_amf LA_NUL
            LF_CTX_link 0 0 0 0x545a0).
  all: first
    [ exact close_laws | exact close_tb | exact close_hsegs | exact close_lv | exact close_tl
    | exact close_snp | exact close_ass | exact close_mt_ok | exact close_mt_le | exact close_txo_ro
    | exact close_txo_tr | exact close_trace_free | exact close_trace_calloc | exact close_afree
    | exact close_afree_null | exact close_calloc | exact close_cv | exact close_cm | exact close_cr
    | exact (close_asm4 fx) | exact (close_cms fx) | exact close_rsd | exact close_mdc | exact close_cs
    | exact close_cref | exact close_cwrite | exact close_index_of | exact close_cmk | exact close_strlen
    | exact close_mqo | exact close_mqa | exact close_bcmp | exact close_model_read | exact close_model_write
    | exact close_alias_write | exact close_unmark_all
    | exact close_kernel | exact close_strcmp | exact close_txo_c | exact close_txb_c | exact close_txb_tr
    | exact close_amset | exact close_alias_read | exact close_cbnd | exact close_cread ].
Qed.

End inst.

(* The ASan build's entry contract of link, closed at the instance (the name fixed for it, consumed by a Theorem Labs lane's
   lib/A/LinkClose.v). No premise. *)
Lemma LLVMFuzzerTestOneInput_closed : forall rc,
  @LinkEntryA.tfib_lib_contract_xf_all_A rc link_asink_head PcapB ameter_triv (fun _ => 0) (fun _ => 0).
Proof.
  intros rc. exact (@LLVMFuzzerTestOneInput_aproof_A rc (@close_whole rc)).
Qed.

Print Assumptions close_ass.
Print Assumptions close_trace_free.
Print Assumptions close_afree.
Print Assumptions close_cv.
About LLVMFuzzerTestOneInput_closed.
Print Assumptions LLVMFuzzerTestOneInput_closed.
