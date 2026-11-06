(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/CfInstImgA.v, with its module paths and module names changed; 58 of its 87 lines of code are new or changed and 107 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WalkB2; integrator ReallocPrimary).
   rule 24: proves function __wrap_malloc (fuzz_reply image A, 0x53dec: its one instruction, `j ___interceptor_malloc`)
   and closes reply's malloc contract by the cf layer's body route; the body's walk is lib/A/ReplyMallocBodyA.v's.
   Reuse search: proof-index __wrap_malloc wrap_to_body_step_cf amalloc_realizes_cf_of_body, 2026-10-30T17:32:07Z:
   no released or unreleased proof of either at fuzz_reply (only the address Definition A_wrap_malloc, lib/A/AD1t.v:50);
   the donor of record is fuzz_preset A1's wrap_to_body_step_A (lib/A/WrapMallocABodyUnit.v at 9e87119fcf60).
   The allocator's malloc contract amalloc_realizes_cf (Reusable/YG0dcf.v) at plugin-hostd/fuzz_reply image A (asan), by
   YGcfMallocCompose.amalloc_realizes_cf_of_body (lib/A/YGcfMallocCompose.v:354), whose three premises are:
   - wrap_to_body_step_reply_A: YGcfMallocCompose.wrap_to_body_step_cf at B: __wrap_malloc (pc_wrap_malloc 0x53dec,
     AF0l.v:11) holds the one word 0x1d80006f = `j 0x53fc4` (jal x0, +0x1d8), so it steps to ___interceptor_malloc
     (pc_malloc 0x53fc4) with the same registers and memory. The word is read through AB1q.tfibtbl_rtA, whose row
     0x53de8 / 206 covers it. This is A1's wrap_to_body_step_A (fuzz_preset lib/A/WrapMallocABodyUnit.v at 9e87119fcf60)
     stated at the layer text, with reply's two pcs.
   - malloc_leaf_widen_reply_A: YGcfLeafWiden.malloc_leaf_widen_cf_ok at reply's two image facts: errno's four bytes
     (TFIB_ERRNO 0x5d93cc, AF0m.v) lie below kHighMemBeg <= ly_stk_lo (layout_ok's lo_top, YG0f.v:325-327), and no
     image byte lies at or above ASAN_CEIL (seg_rom_none_high above TFIB_IMG_END 0x5fb000, AF0x.v:25 / :122141).
   - the body contract: ReplyMallocBodyA.amalloc_body_q (its unwinder premise tfib_unwind_spec is AFl4.tfib_unwind_ok),
     given Allocate's contract at ARXq_cf.
   amalloc_reply_A: forall fx rc, Allocate's contract (aalloc_realizes_cf_em at ARXq_cf TfibB (fun i => i =
   as_inst TfibB), nmax cf_malloc_max, al 8, atp 1, acf 1) -> amalloc_realizes_cf at CfImg_A / CfParams_reply, the
   form of lib/A/ReplyAllocTargets.v's amalloc_target_reply. Allocate's contract is its only premise; the wrapper
   walk record (wrap_malloc_walk_cf, amalloc_realizes_cf_of_parts) is not used. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose AGif2reply YGcfLeafWiden.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require WrapMallocAConsts YGcfInstBase ReplyMallocBodyA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AD2l AFl4 CfImgA CfParamsReply ReplyAllocTargets ReplyRelroGeoA.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis Hpc : cf_pc_allocate = WrapMallocAConsts.PC_ALLOCATE.
(* part 3c: the unit's two image rows the body reads to carry arodata_ok_cf to Allocate's entry (ReplyMallocBodyA) *)
Hypothesis RS : relro_seg_t tfibsegs.
Hypothesis ER0 : errno_relro_t B.

(* ---- __wrap_malloc's one step ---- *)
Lemma fetch_wrap_malloc_stub_reply_A : fetch_word tfibsegs (Z_to_bv 64 0x53dec) = Some (0x1d80006f%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x1d80006f%bv : bv 32)). apply tfibtbl_rtA_ok. vm_compute. reflexivity. Qed.
Lemma decode_wrap_malloc_stub_reply_A : decode_any (0x1d80006f%bv : bv 32) = Some (Jal 0 (Z_to_bv 21 0x1d8), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma step_wrap_malloc_stub_reply_A regs mem :
RiscvSemantics.step tfibsegs (mkst regs (Z_to_bv 64 0x53dec) mem (seg_rom tfibsegs)) =
MachineOk (mkst regs (Z_to_bv 64 0x53fc4) mem (seg_rom tfibsegs)).
Proof.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_wrap_malloc_stub_reply_A eq_refl decode_wrap_malloc_stub_reply_A). do 2 f_equal.
Qed.

Theorem wrap_to_body_step_reply_A : wrap_to_body_step_cf tfibsegs B.
Proof.
intros ly S Hp W regs mem md ch _.
rewrite (ts_code B TB). cbv [pc_wrap_malloc pc_malloc Tfib_code]. unfold cfg_at, w64.
eapply SRr_step; [exact Hwx_tfa | reflexivity | rewrite restrict_mkst_fx; apply step_wrap_malloc_stub_reply_A |].
intros model' SBM. rewrite unrestrict_mkst_mrestrict. apply SRr_ret. split; [reflexivity|].
exists (m_vm_materialized model'). unfold same_but_materialized in SBM. rewrite <- SBM. reflexivity.
Qed.

Lemma errno_below_stack_reply_A : errno_below_stack_cf B.
Proof.
intros ly LY. rewrite (ts_errno B TB). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & Hb).
unfold TFIB_ERRNO in *. unfold kHighMemBeg in Hb. lia.
Qed.

Lemma img_below_ceil_reply_A : img_below_ceil_cf tfibsegs.
Proof.
intros a Ha. apply seg_rom_none_high. pose proof ASAN_CEIL_range as [CR _]. unfold TFIB_IMG_END. lia.
Qed.

Theorem malloc_leaf_widen_reply_A : malloc_leaf_widen_cf tfibsegs B.
Proof. exact (malloc_leaf_widen_cf_ok tfibsegs B errno_below_stack_reply_A img_below_ceil_reply_A). Qed.

(* the malloc contract at any B, from Allocate's contract at the reply call-site relation *)
Theorem amalloc_q :
  aalloc_realizes_cf_em tfibsegs B cf_malloc_max 8 1 1 (YGcfInstBase.ARXq_cf B (fun i => i = as_inst B)) ->
  amalloc_realizes_cf tfibsegs B.
Proof.
intros HAL.
exact (amalloc_realizes_cf_of_body tfibsegs B wrap_to_body_step_reply_A malloc_leaf_widen_reply_A
  (ReplyMallocBodyA.amalloc_body_q B TB AFl4.tfib_unwind_ok Hpc RS ER0 HAL)).
Qed.

End U.

(* image A's CfImg and reply's CfParams, as lib/A/ReplyAllocTargets.v takes them: the statement below is about image A
   by design *)
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsReply.CfParams_reply.

Theorem amalloc_reply_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  aalloc_realizes_cf_em (fx := fx) tfibsegs AD2l.TfibB cf_malloc_max 8 1 1
    (YGcfInstBase.ARXq_cf (rc := rc) AD2l.TfibB (fun i => i = as_inst AD2l.TfibB)) ->
  @amalloc_realizes_cf fx rc CfImgA.CfImg_A CfParamsReply.CfParams_reply tfibsegs AD2l.TfibB.
Proof.
intros fx rc HAL. exact (amalloc_q AD2l.TfibB AD2l.TfibB_syms ReplyMallocBodyA.pc_allocate_reply_A
  ReplyRelroGeoA.relro_seg_reply_A (ReplyRelroGeoA.errno_relro_reply_A AD2l.TfibB AD2l.TfibB_syms) HAL).
Qed.

(* ... so reply's malloc TARGET (lib/A/ReplyAllocTargets.v amalloc_target_reply, the text ReplyATopX's AMALLOC_CF takes)
   follows from Allocate's contract at every FP state and RunCeil *)
Corollary amalloc_target_reply_of_allocate :
  (forall (fx : YK11.FPState) (rc : YM05.RunCeil),
    aalloc_realizes_cf_em (fx := fx) tfibsegs AD2l.TfibB cf_malloc_max 8 1 1
      (YGcfInstBase.ARXq_cf (rc := rc) AD2l.TfibB (fun i => i = as_inst AD2l.TfibB))) ->
  ReplyAllocTargets.amalloc_target_reply.
Proof. intros HAL fx rc. exact (amalloc_reply_A fx rc (HAL fx rc)). Qed.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check wrap_to_body_step_reply_A. Print Assumptions wrap_to_body_step_reply_A.
Check malloc_leaf_widen_reply_A. Print Assumptions malloc_leaf_widen_reply_A.
Check amalloc_q. Print Assumptions amalloc_q.
Check amalloc_reply_A. Print Assumptions amalloc_reply_A.
Check amalloc_target_reply_of_allocate. Print Assumptions amalloc_target_reply_of_allocate.
