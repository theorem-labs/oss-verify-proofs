(* reac_served_mark (fuzz_link.asan 0x895a8, 1596 bytes; listing
   (internal path) (internal record, sha256 5943815fc488)) on image A: THE WALK,
   composed. `reac_served_mark_aproof : reac_served_mark_acontract SK pa_segs PCAP_RLO PCAP_RHI B` (lib/A/Prog/
   reac_served_mark_c.v, aleaf_fx, K 9504, EV 0, SIDE [(3,2);(1,1);(9,1);(0,1)]) from the segment lemmas over the
   cuts of lib/A/Prog/reac_served_markDefs.v:
     reac_served_markHead.v     srm_head      the entry, frame_alloc_3, the frame's header and shadow  -> MID
     reac_served_markMid*.v     srm_mid       the refusals -> EXIT; reac_link_alias_read                -> RRET
     reac_served_markRret.v     srm_rret      a failed read: reac_code_emit -> RESTORE; else            -> DEC
     reac_served_markDec.v      srm_dec       reac_served_decide, the verdict      -> VMARK / VOURS / VVLAN / VHOST
     reac_served_markVmark.v    srm_vmark     reac_link_alias_write                                     -> WRET
     reac_served_markWret.v     srm_wret      remember, or reac_code_emit after a failed write          -> RESTORE
     reac_served_markVours.v    srm_vours     wrapper_bcmp, remember on "reac-pw:served"                -> RESTORE
     reac_served_markVvlan.v    srm_vvlan     wrapper_fprintf (.str.8)                                  -> RESTORE
     reac_served_markVhost.v    srm_vhost     wrapper_fprintf (.str.9)                                  -> RESTORE
     reac_served_markExit.v     srm_restore_ok / srm_exit_ok   the buffers' shadow back, meta_fill_f5, the
                                              inline release of the class-3 frame, the restores, `ret`
   A cut reached after a printf-family callee is at the FP state that callee returned, so RESTORE / EXIT are
   proved at every fx (`srm_restore_all`).

   Released proofs (rule 24): none of reac_served_mark (lookups lookups/walk-lookups.md (internal record, sha256 98fff7967d93) lines 1726-1757; disposition
   none: written new; the rule-24 walk check at 14:56Z confirmed it).
   Proves function reac_served_mark (image A, the asan build). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkPrintf LinkWalkMkFile LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markDefs reac_served_markUniq reac_served_markKit reac_served_markKitAt reac_served_markXfer.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markPf reac_served_markPfStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkFmt reac_served_markEmitArgs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markPfArm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_link_alias_read_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markHead reac_served_markMid reac_served_markRret reac_served_markDec reac_served_markVmark
reac_served_markWret reac_served_markVours reac_served_markVvlan reac_served_markVhost reac_served_markExit.
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
Hypothesis TL : PALib B.                            (* LinkPaLib.v, at PcapB *)
Hypothesis TB : PcapSyms B.                         (* AD2l.PcapB_syms *)
Hypothesis HSEGS : SEGS = tfibsegs.                 (* LinkImgInst.v pi_link_segs *)

(* the relro window [PCAP_RLO, PCAP_RHI) lies in an image segment *)
Lemma srm_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
  intros a Ha. rewrite HSEGS. destruct pcap_relro_in_image as (s & Hs & H1 & H2 & H3).
  exists s. split; [exact Hs | lia].
Qed.
(* the runtime callees *)
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.  (* StackSideInst.v link_stack_malloc_3 *)
Hypothesis HSM3 : pc_stack_malloc (as_code B) 3 = pa_sigma LS___asan_stack_malloc_3.  (* AF0l Tfib_code, lv_sigma *)
Hypothesis ASSF5 : forall fx' : YK11.FPState, @aset_shadow_realizes fx' rc SEGS B 0x55f7c 0xf5.  (* SetShadow.v link_set_shadow_f5 *)
Hypothesis ABCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc SEGS B 0x4305c.   (* AE2s.v bcmp_icpt_contract *)
Hypothesis HFP : forall fx' : YK11.FPState,
  @afprintf_mf_realizes fx' rc SEGS B link_amf PCAP_RLO PCAP_RHI link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD
    LA_W_FPRINTF.                                   (* LinkVfTop.v link_fprintf_mf *)
(* the own callees, at every FP state *)
Hypothesis HRD : forall fx' : YK11.FPState, @reac_link_alias_read_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis HWR : forall fx' : YK11.FPState, @reac_link_alias_write_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis HDC : forall fx' : YK11.FPState, @reac_served_decide_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis HRM : forall fx' : YK11.FPState, @remember_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis HEM : forall fx' : YK11.FPState, @reac_code_emit_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.
Let RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a := srm_relro_img.

Theorem reac_served_mark_aproof : reac_served_mark_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
  pose proof (fun fx' : YK11.FPState => @srm_exit_ok fx' rc SK PI B LAWS HV TB HSEGS (ASSF5 fx')) as EXIT.
  assert (RESTORE : srm_restore_all SK B).
  { intros fx'. exact (@srm_restore_ok fx' rc SK PI B LAWS TB HSEGS RELRO_IMG (EXIT fx')). }
  eapply srm_head; try eassumption.
  eapply srm_mid; try eassumption; [exact (EXIT fx) |].
  eapply srm_rret; try eassumption.
  eapply srm_dec; try eassumption.
  - eapply srm_vmark; try eassumption. eapply srm_wret; eassumption.
  - eapply srm_vours; eassumption.
  - eapply srm_vvlan; eassumption.
  - eapply srm_vhost; eassumption.
Qed.

End a.

About reac_served_mark_aproof.
Print Assumptions reac_served_mark_aproof.
