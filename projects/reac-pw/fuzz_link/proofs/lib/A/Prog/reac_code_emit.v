(* reac_code_emit (fuzz_link.asan 0x89be4, 464 bytes; listing
   (internal path) (internal record, sha256 102ac6881148)) on image A: THE WALK,
   composed. `reac_code_emit_aproof : reac_code_emit_acontract SK pa_segs PCAP_RLO PCAP_RHI B`
   (lib/A/Prog/reac_code_emit_c.v, aleaf_fx, K 9360, EV 0, SIDE [(0, 1)]) at every FP state fx, from the segment lemmas
   over the cuts of lib/A/Prog/reac_code_emitDefs.v:
     reac_code_emitEntry.v  em_entry   the entry, frame_alloc_0, the frame's header and shadow, wrapper_fprintf
                                       ("%s: %s ", "reac-pw", "E_NOT_MARKED")                          -> +0x120
     reac_code_emitMid.v    em_mid     the va_list into the frame, wrapper_vfprintf (f, fmt, ap)        -> +0x13c
     reac_code_emitExit.v   em_exit    the frame's shadow f5, the inline release of the class-0 frame, the
                                       restores, `ret`, the post (with reac_code_emitPost.v em_apost, the FILE)
   A cut after a printf-family callee is at the FP state that callee returned, so em_mid and em_exit are taken at
   every fx'.

   Released proofs (rule 24): none of reac_code_emit (lookups lookups/walk-lookups.md (internal record, sha256 98fff7967d93) lines 1759-1790; disposition
   none: written new; the rule-24 walk check at 14:56Z confirmed it).
   Proves function reac_code_emit (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c reac_code_emitDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_code_emitEntry reac_code_emitMid reac_code_emitExit reac_code_emitPost.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
(* the frame and the image instance *)
Hypothesis LAWS : AR_laws SEGS B.                  (* the frame's AR_laws at B *)
Hypothesis HV : LinkVals (L := link_listing).       (* LinkImgInst.v pi_link_vals *)
Hypothesis TL : PALib B.                            (* LinkPaLib.v, at PcapB: PcapB_palib *)
Hypothesis TB : PcapSyms B.                         (* AD2l.PcapB_syms *)
Hypothesis HSEGS : SEGS = tfibsegs.                 (* LinkImgInst.v pi_link_segs *)
(* the runtime callees *)
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.  (* StackMalloc0.v stack_malloc0_contract B LAWS TB *)
Hypothesis FPR : forall fx' : YK11.FPState,
  @afprintf_mf_realizes fx' rc SEGS B link_amf PCAP_RLO PCAP_RHI link_vf_FF LFP_STK LinkMfDefs.LA_GOT_GUARD
    LinkMfDefs.LA_GUARD LA_W_FPRINTF.               (* LinkVfTop.v link_fprintf_mf_rel *)
Hypothesis VFPR : forall fx' : YK11.FPState,
  @avfprintf_mf_realizes fx' rc SEGS B link_amf PCAP_RLO PCAP_RHI link_vf_FF LVF_STK LinkMfDefs.LA_GOT_GUARD
    LinkMfDefs.LA_GUARD LA_W_VFPRINTF.              (* LinkVfTop.v link_vfprintf_mf_rel *)

(* the relro window [PCAP_RLO, PCAP_RHI) lies in an image segment *)
Lemma em_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
  intros a Ha. rewrite HSEGS. destruct pcap_relro_in_image as (s & Hs & H1 & H2 & H3).
  exists s. split; [exact Hs | lia].
Qed.

Theorem reac_code_emit_aproof : reac_code_emit_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
  unfold reac_code_emit_acontract, aleaf_fx.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD Hfrm HP.
  destruct HP as (fmt & ps & args & T & kf & Hf0 & Hfp0 & HFIN & HMF & HBLK & HFIT & HFMT & HL1 & HL1r & HL2 & HL2r
    & HL3 & HL3r).
  set (cx := mkEMCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fmt ps args T kf).
  assert (HB : em_base SK B cx).
  { exact (conj HPRE (conj HRD (conj Hf0 (conj Hfp0 (conj HFIN (conj HMF (conj HBLK (conj HFIT (conj HFMT
      (conj HL1 (conj HL1r (conj HL2 (conj HL2r (conj HL3 HL3r)))))))))))))). }
  assert (HPC : REAC_CODE_EMIT_A = pa_val A_TEXT + EM_entry) by (rewrite (lv_text HV); reflexivity).
  rewrite HPC.
  exact (@em_entry fx rc SK PI B LAWS HV TL TB HSEGS em_relro_img ASM0 FPR
    (fun fx' => @em_mid fx' rc SK PI B LAWS HV TB HSEGS em_relro_img VFPR
       (fun fx'' => @em_exit fx'' rc SK PI B LAWS HSEGS (@em_apost rc SK PI B)))
    cx Hfrm HB).
Qed.

End a.

About reac_code_emit_aproof.
Print Assumptions reac_code_emit_aproof.
