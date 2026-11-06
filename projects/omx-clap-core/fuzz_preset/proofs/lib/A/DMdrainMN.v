(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainMN.v (commit 67deba317dfb, blob 8944d91fb8f9) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0x AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMdrainG1 DMdrainG4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG MemnormLoc MemnormSafepreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma mn_safe_quar_img : forall x : word, A_QUAR + 152 <= bv_unsigned x < A_QUAR + 192 -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx. assert (EAQ : A_QUAR = 686896) by reflexivity.
apply MemnormSafepreset.mn_safe_rw. rewrite EAQ in Hx. unfold TASK_SIZE. lia.
Qed.

Section l.
Variable ly : alayout.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.

Lemma mn_safe_thr : forall x : word, ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx.
pose proof (DMdrainG1.TOBJ ly LY IMG (DMdrainG4.T_app ly LY) (DMdrainG4.T_img ly LY)) as (_ & TZ & _ & T3 & _).
exact (MemnormLoc.mn_safe_zone3 (ly_T ly) kThreadObjSize x TZ Hx T3).
Qed.

Lemma mn_safe_prim : forall x : word, ly_prim ly <= bv_unsigned x < ly_prim ly + kPrimResvSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx.
pose proof (DMdrainG1.LYB2 ly LY) as (P1 & _ & _ & P4 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kImgEnd, TASK_SIZE, YG0f.ASAN_CEIL in *. lia.
Qed.

Lemma mn_safe_stk : forall x : word, ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx.
pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

Lemma mn_safe_qhdr : forall inst (x : word), inst + o_quar = A_QUAR -> qhdr inst ly (bv_unsigned x) ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros inst x AQ HQ. unfold qhdr in HQ. rewrite AQ in HQ. destruct HQ as [HQ | [HQ | HQ]].
- apply mn_safe_quar_img. lia.
- apply mn_safe_quar_img. lia.
- apply mn_safe_thr. unfold t_qc, kThreadObjSize in *. lia.
Qed.

Lemma mn_safe_bobj : forall b (x : word),
  ly_prim ly <= ly_space ly + b_self b -> ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize ->
  bobj ly b (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros b x B1 B2 Hob. pose proof (DMdrainG1.LYB2 ly LY) as (_ & _ & P3 & _).
apply mn_safe_prim. unfold bobj in Hob. unfold kBatchBytes, kSpaceSize in *. lia.
Qed.
End l.
End f.
