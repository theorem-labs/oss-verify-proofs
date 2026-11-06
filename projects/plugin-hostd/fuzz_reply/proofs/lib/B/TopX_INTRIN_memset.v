(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/TopX_INTRIN.v at commit d12d454ec30 (a Theorem Labs lane's top_x group INTRIN, its
   topx_AMEMSET_x) relocated to image B (fuzz_reply.asan-ubsan), cut to the memset row: the intrinsic contract of
   __asan_memset (B entry 0x52c1c, the callee of the B call at 0x82bd4) PROVED at image B's top_x instance
     AMEMSET_x : aintrin_realizes_x segs TfibB ARX OSet (pa_sigma WS_asan_memset)
   with ARX := TopX_RT_lock.ARX_rt (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:154-155 verbatim), so the plug is `exact`
   up to unfolding ARX.  The proof is the ARx port of the memset walk at ARx := ARX_rt: lib/B/YE6t_x.v .. YE6v_x.v,
   YE2r_x.v asan_memset_realizes_x over YE2y.icpt_laws_x.  icpt_laws_x at ARX_rt comes from RTxIcpt's bridge
   icpt_laws_of_rt: the runtime laws TopX_RT_lock.rt_laws_ARX, and the zero-shadow law from the field alx_zshadow of
   top_x's own law record (top_x.v:156-160, ARX_laws, restated here as ARX_rt_laws_x).  YE2r_x's statement is the
   memset contract at 0x52c1c with amem_range d n after the shadow premises and no source conjunct;
   topx_AMEMSET_x moves amem_range to its place and drops the OSet source premise (True).  Cut from the A file: its
   memcpy row (another lane's), with the imports only that row used.  No premise is left: every lemma here is
   closed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import TopX_RT_lock.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2y.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RTxIcpt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2r_x.
Import ListNotations.
Open Scope Z_scope.

Module IX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2y.
Module RI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RTxIcpt.
Module SET := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2r_x.

Section topx_intrin. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* top_x.v:156-160's ARX_laws at ARX_rt: the cf laws with the ghost set held at [] *)
Lemma ARX_rt_laws_x : AR_laws_x segs TfibB ARX_rt (@cf_head CfParams_reply).
Proof.
  unfold ARX_rt. apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* the interceptor law record at ARX_rt: the runtime laws and the zero-shadow law *)
Lemma icpt_laws_ARX : IX.icpt_laws_x TfibB ARX_rt.
Proof. exact (RI.icpt_laws_of_rt TfibB ARX_rt rt_laws_ARX (alx_zshadow _ _ _ ARX_rt_laws_x)). Qed.

Lemma asan_memset_id_sigma : SIGMA WS_asan_memset = 0x52c1c.
Proof. reflexivity. Qed.

(* AMEMSET_x (the hypothesis image B's top_x takes at ARX) *)
Lemma topx_AMEMSET_x : aintrin_realizes_x segs TfibB ARX_rt OSet (SIGMA WS_asan_memset).
Proof.
  rewrite asan_memset_id_sigma.
  intros ly S Hp W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM _ HRA HHULL _.
  exact (SET.asan_memset_realizes_x TfibB ARX_rt icpt_laws_ARX TfibB_syms ly S Hp W regs mem md d x n HPRE
           G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.

End topx_intrin.
