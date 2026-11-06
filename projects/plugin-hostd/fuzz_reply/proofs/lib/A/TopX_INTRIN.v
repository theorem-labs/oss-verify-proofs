(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: top_x group INTRIN (port-reply's TOPX-OWNERS.md, owner g-ph-verbs): the
   intrinsic hypothesis of A's top_x (W_LLVMFuzzerTestOneInput_top_x.v at integ bb9dae5d905) PROVED at the instance
     AMEMCPY_x (top_x.v:194) : aintrin_realizes_x segs TfibB ARX OCpy (SIGMA WS_asan_memcpy)
   with ARX := TopX_RT.ARX_rt (top_x.v:125-126 verbatim), so the plug is `exact` up to unfolding ARX.
   The proof is the ARx port of the __asan_memcpy walk at 0x52728 (lib/A/AE6k_x.v .. AE6s_x.v, AE2q_x.v
   asan_memcpy_realizes_x over AE2y.icpt_laws_x) at ARx := ARX_rt.  icpt_laws_x at ARX_rt comes from RTxIcpt's
   bridge icpt_laws_of_rt: the runtime laws TopX_RT.rt_laws_ARX, and the zero-shadow law (the shadow bytes of the
   image's zero-shadow ranges read 0) from the field alx_zshadow of top_x's own law record (top_x.v:127-131,
   ARX_laws, restated here as ARX_rt_laws_x).  The text of AE2q_x's statement is AE2y's form of the contract at
   tfibsegs and 0x52728; W_sites_x.aintrin_realizes_x at segs and SIGMA WS_asan_memcpy is the same text up to
   conversion (segs = tfibsegs and SIGMA WS_asan_memcpy = 0x52728 by reflexivity; ecall_pre_x is AE2y's ecall_pre_ix,
   RTxIcpt.ecall_pre_ix_iff).  No premise is left: every lemma here is closed.
   AMEMSET_x (top_x.v:202) is not in this file yet: its walk is the port of the __asan_memset chain (AE2r_x).
   rule 24: no function proved. rule 24: proves no function (kind: statement text). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/TopX_INTRIN.v, with its module paths changed; 33 of its 81 lines of code are new or changed and 14 lines of the source are left out. *)
(* top_x group INTRIN (TOPX-OWNERS.md (sha256 bb821fae800d; internal record)): the two
   intrinsic hypotheses of A's top_x (W_LLVMFuzzerTestOneInput_top_x.v at integ bb9dae5d905) PROVED at the instance
     AMEMCPY_x (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:194) : aintrin_realizes_x segs TfibB ARX OCpy (SIGMA WS_asan_memcpy)
     AMEMSET_x (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:202) : aintrin_realizes_x segs TfibB ARX OSet (SIGMA WS_asan_memset)
   with ARX := TopX_RT.ARX_rt (top_x.v:125-126 verbatim), so the plug is `exact` up to unfolding ARX.
   The proofs are the ARx ports of the two walks at ARx := ARX_rt: __asan_memcpy at 0x52728 (lib/A/AE6k_x.v ..
   AE6s_x.v, AE2q_x.v asan_memcpy_realizes_x) and __asan_memset at 0x52bc4 (a Theorem Labs lane's lib/A/AE6t_x.v .. AE6v_x.v,
   AE2r_x.v asan_memset_realizes_x), both over AE2y.icpt_laws_x.  icpt_laws_x at ARX_rt comes from RTxIcpt's
   bridge icpt_laws_of_rt: the runtime laws TopX_RT.rt_laws_ARX, and the zero-shadow law (the shadow bytes of the
   image's zero-shadow ranges read 0) from the field alx_zshadow of top_x's own law record (top_x.v:127-131,
   ARX_laws, restated here as ARX_rt_laws_x).  AE2q_x's statement is AE2y's form of the contract at tfibsegs and
   0x52728; W_sites_x.aintrin_realizes_x at segs and SIGMA WS_asan_memcpy is the same text up to conversion
   (segs = tfibsegs and SIGMA WS_asan_memcpy = 0x52728 by reflexivity; ecall_pre_x is AE2y's ecall_pre_ix,
   RTxIcpt.ecall_pre_ix_iff).  AE2r_x's statement is AE32.memset_icpt_realizes_x's form at 0x52bc4 (amem_range d n
   after the shadow premises, no source conjunct); topx_AMEMSET_x moves amem_range to its place and drops the OSet
   source premise (True).  No premise is left: every lemma here is closed.
   rule 24: no function proved. rule 24: proves no function (kind: statement text). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_contract_x W_palib_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import TopX_RT.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE2y.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RTxIcpt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE2q_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE2r_x.
Import ListNotations.
Open Scope Z_scope.

Module IX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE2y.
Module RI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RTxIcpt.
Module CPY := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE2q_x.
Module SET := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AE2r_x.

Section topx_intrin. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* top_x.v:127-131's ARX_laws at ARX_rt: the cf laws with the ghost set held at [] *)
Lemma ARX_rt_laws_x : AR_laws_x segs TfibB ARX_rt (@cf_head CfParams_reply).
Proof.
  unfold ARX_rt. apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* the interceptor law record at ARX_rt: the runtime laws and the zero-shadow law *)
Lemma icpt_laws_ARX : IX.icpt_laws_x TfibB ARX_rt.
Proof. exact (RI.icpt_laws_of_rt TfibB ARX_rt rt_laws_ARX (alx_zshadow _ _ _ ARX_rt_laws_x)). Qed.

Lemma asan_memcpy_id_sigma : SIGMA WS_asan_memcpy = 0x52728.
Proof. reflexivity. Qed.

(* AMEMCPY_x (top_x.v:194) *)
Lemma topx_AMEMCPY_x : aintrin_realizes_x segs TfibB ARX_rt OCpy (SIGMA WS_asan_memcpy).
Proof.
  rewrite asan_memcpy_id_sigma.
  intros ly S Hp W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM _ HRA HHULL HOP.
  exact (CPY.asan_memcpy_realizes_x TfibB ARX_rt icpt_laws_ARX TfibB_syms ly S Hp W regs mem md d x n HPRE
           G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HOP).
Qed.

Lemma asan_memset_id_sigma : SIGMA WS_asan_memset = 0x52bc4.
Proof. reflexivity. Qed.

(* AMEMSET_x (top_x.v:202) *)
Lemma topx_AMEMSET_x : aintrin_realizes_x segs TfibB ARX_rt OSet (SIGMA WS_asan_memset).
Proof.
  rewrite asan_memset_id_sigma.
  intros ly S Hp W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM _ HRA HHULL _.
  exact (SET.asan_memset_realizes_x TfibB ARX_rt icpt_laws_ARX TfibB_syms ly S Hp W regs mem md d x n HPRE
           G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.

(* QMm W1: the two intrinsic rows at top_x's W1 relation TopX_RT.ARX_rtW (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:180-182, which adds arodata_ok_cf),
   beside the rows at ARX_rt above.  The rule at ARX_rt, then arodata_ok_cf at the post memory by TopX_RT.aro_keep_view:
   the post's view frame is off the destination [d, d + n), which holds no kept byte (the rule's not-kept premise),
   and off the ESTACK window, which lies above the image (TopX_RT.stk_above_img). *)
Lemma topx_intrin_W : forall op pc, aintrin_realizes_x segs TfibB ARX_rt op pc -> aintrin_realizes_x segs TfibB ARX_rtW op pc.
Proof.
  intros op pc HR ly S Hp W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HKEPT HRA HHULL HOP.
  destruct (ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  pose proof (stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
  pose proof HPRE0 as (HA0 & _ & _ & Hlo & _).
  eapply SRr_mono; [exact (HR ly S Hp W regs mem md d x n HPRE0 G10 G11 G12 Hn Hd Hdn HDST HAM HKEPT HRA HHULL HOP)|].
  intros W' c' _ (EW & regs' & mem' & md' & Hc & (HA' & HH') & Hrp & Hsm & H10 & HCP & HV & Hpr).
  split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|].
  split; [|exact (conj Hrp (conj Hsm (conj H10 (conj HCP (conj HV Hpr)))))].
  split; [exact HA'|]. split; [exact HH'|].
  apply (aro_keep_view ly S Hp W mem md mem' (fun a => d <= a < d + n) (fun a => spZ regs - ESTACK <= a < spZ regs)
    HA0 HKEPT); [| exact HV | exact HQ].
  intros a Ha. cbv beta in Ha. unfold ESTACK in *. lia.
Qed.

(* AMEMCPY_x / AMEMSET_x at ARX_rtW *)
Lemma topx_AMEMCPY_x_W : aintrin_realizes_x segs TfibB ARX_rtW OCpy (SIGMA WS_asan_memcpy).
Proof. exact (topx_intrin_W OCpy _ topx_AMEMCPY_x). Qed.

Lemma topx_AMEMSET_x_W : aintrin_realizes_x segs TfibB ARX_rtW OSet (SIGMA WS_asan_memset).
Proof. exact (topx_intrin_W OSet _ topx_AMEMSET_x). Qed.

End topx_intrin.
