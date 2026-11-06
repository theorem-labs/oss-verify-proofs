(* reac-pw/fuzz_link, image A: kernel_aproof, the walk of kernel (fuzz_link.asan 0x83d30) against kernel_acontract (kernel_c.v).
   kernel_defs.v's kernel_of_kstart reduces the contract to `kstart SK B (kpost SK B)`; kernel_comp.v's kn_compose builds that from the 27
   phase lemmas (the three loops by induction on their measures); each phase lemma is proved in its segment file (link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4, the table in link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).

   SECTION HYPOTHESES: the image-fact records (AR_laws, LinkVals, PALib, PcapSyms, KernImg) and the callee contracts
   (frame_alloc_8, frame_release_8, meta_fill_00, meta_fill_f8, checked_memcpy, checked_memset, attr_text, nl_error),
   each discharged where the instance is built: AR_laws by the frame's laws, LinkVals / PALib by the image tables,
   PcapSyms by AD2l.PcapB_syms, KernImg by kernel_img_tfib.v kernel_img_pcapB (kernel_img_syms over any PcapSyms B),
   frame_alloc_8 / frame_release_8 by StackSideInst.v link_stack_malloc_8 / link_stack_free_8, meta_fill_* by
   SetShadow.v link_set_shadow_00 / _f8, checked_memcpy / checked_memset by AE2q.v asan_memcpy_realizes / AE2r.v
   asan_memset_realizes, attr_text by attr_text.v attr_text_aproof, nl_error by nl_error.v nl_error_aproof.
   Released proofs (rule 24): the walk of kernel had its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new;
   confirmed by the rule-24 walk check at 14:56Z).
   Proves kernel (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YI16 YM05 YG00 YG0f YG0n YG0d YCbq YC5d AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkList LinkPa LinkPaLib LinkWalk PcapRelro link_amem link_ajkit attr_text_c nl_error_c kernel_c kernel_img
kernel_defs kernel_comp kernel_entry kernel_flags kernel_gnl kernel_setup kernel_head kernel_msg0 kernel_disp
kernel_k12_k1 kernel_k12_k2 kernel_k3 kernel_k4 kernel_k5 kernel_k6 kernel_k07h kernel_atxt kernel_a014 kernel_a014_m
kernel_a23 kernel_a5 kernel_alatch kernel_next kernel_qmsg kernel_raw kernel_latch kernel_exit.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : PcapSyms B.
Hypothesis KI : KernImg pa_segs B.
Hypothesis ASM8 : astack_malloc_sz_realizes pa_segs B 0x3df90 8.
Hypothesis ASF8 : astack_free_realizes pa_segs B 0x3e10c 8.
Hypothesis AS00 : aset_shadow_realizes pa_segs B 0x55e74 0x00.
Hypothesis ASSF8 : aset_shadow_realizes pa_segs B 0x55f94 0xf8.
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.
Hypothesis ATEXT : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ANLERR : nl_error_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

Ltac kn_close lem := intros; eapply lem; eassumption.

Theorem kernel_aproof : kernel_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
  apply (kernel_of_kstart SK B LV).
  apply (kn_compose SK B).
  - kn_close kn_entry.
  - kn_close kn_flags.
  - kn_close kn_gnl.
  - kn_close kn_setup.
  - kn_close kn_head.
  - kn_close kn_msg0.
  - kn_close kn_mz.
  - kn_close kn_disp.
  - kn_close kn_k1.
  - kn_close kn_k2.
  - kn_close kn_k3.
  - kn_close kn_k4.
  - kn_close kn_k5.
  - kn_close kn_k6.
  - kn_close kn_k07.
  - kn_close kn_atxt.
  - kn_close kn_txt.
  - kn_close kn_a0e.
  - kn_close kn_a23.
  - kn_close kn_a5.
  - kn_close kn_alatch.
  - kn_close kn_nlend.
  - kn_close kn_next.
  - kn_close kn_qmsg.
  - kn_close kn_raw.
  - kn_close kn_latch.
  - kn_close kn_exit.
Qed.
End a.

Print Assumptions kernel_aproof.
