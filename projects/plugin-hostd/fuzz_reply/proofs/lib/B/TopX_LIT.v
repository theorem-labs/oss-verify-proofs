(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): the B top's two snprintf literal rows.  lib/B/ReplyBTop.v's Context premises
     GN_LIT_GES_x : forall rc fx, ashp_x PB_fr top_x.ARX (pa_val .. A_lit_gesture) 14
     GN_LIT_FMT_x : forall rc fx, ashp_x PB_fr top_x.ARX (pa_val .. (A_OBJ 17)) 7
   (ReplyBTop.v:210-211; lib/B/W_LLVMFuzzerTestOneInput_top_x.v:897-898 at the Section level), stated below with
   top_x's ARX written as its body (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:175-177: ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB /\ Hp = []
   /\ arodata_ok_cf), as TopX_SNP.v does, so this file does not Require top_x (whose closure is red on this base) and
   each plug is `exact (topx_GN_LIT_GES_x rc fx)` / `exact (topx_GN_LIT_FMT_x rc fx)` up to unfolding ARX.
   - The facts are the ones of lib/B/W_LLVMFuzzerTestOneInput_gone_inst.v gi_LIT_GES :118 (.str.5
     "param_gesture\0", 0x20f20, 14 bytes) and gi_LIT_FMT :121 (.str.9 "%s %d \0", 0x20f80, 7 bytes), there at AR:
     the same shp_check decision over image B's start-up tables YF0m.Tfib_const_shadow / Tfib_zero_shadow, by
     vm_compute, made at ARX here.
   - The bridge to ARX is lib/B/TopxImageB.v tfib_shp_x (shp_ashp over a generic ARx).  Its two law bodies are
     projections of ARcf's first conjunct ARmcf (YG0ncf.v amc_const, amc_zshadow), as TopxImageB.ashp_str3_1_fr_cf.
   proves no function (kind: instance discharge). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_contract W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* top_x's ARX is shp-decidable: shp_check over B's start-up tables gives ashp_x at ARX *)
Lemma topx_lit_shp : forall (rc : YM05.RunCeil) (fx : YK11.FPState) a n,
  shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow a n = true ->
  @W_contract_x.ashp_x rc (@PB_fr rc) (fun ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB ly S Hp W mem md /\ Hp = [] /\ @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB mem) a n.
Proof.
intros rc fx a n H. apply (TopxImageB.tfib_shp_x TfibB TfibB_syms); [| | exact H].
- intros ly S Hp W mem md ((M & _) & _ & _). exact (amc_const _ _ _ _ _ M).
- intros ly S Hp W mem md r ((M & _) & _ & _) Hr. exact (proj1 (Forall_forall _ _) (amc_zshadow _ _ _ _ _ M) r Hr).
Qed.

(* ReplyBTop.v:210 GN_LIT_GES_x: .str.5 "param_gesture\0", A_OBJ 18 = 0x20f20, 14 bytes *)
Lemma topx_GN_LIT_GES_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_x.ashp_x rc (@PB_fr rc) (fun ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB ly S Hp W mem md /\ Hp = [] /\ @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB mem) (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_gesture) 14.
Proof. intros rc fx. apply (topx_lit_shp rc fx). vm_compute. reflexivity. Qed.

(* ReplyBTop.v:211 GN_LIT_FMT_x: .str.9 "%s %d \0", A_OBJ 17 = 0x20f80, 7 bytes *)
Lemma topx_GN_LIT_FMT_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_x.ashp_x rc (@PB_fr rc) (fun ly S Hp (W : world (@pa_segs rc fr_prog_listing (@PB_fr rc))) mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB ly S Hp W mem md /\ Hp = [] /\ @YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB mem) (@pa_val rc fr_prog_listing (@PB_fr rc) (A_OBJ 17)) 7.
Proof. intros rc fx. apply (topx_lit_shp rc fx). vm_compute. reflexivity. Qed.

Print Assumptions topx_GN_LIT_GES_x.
Print Assumptions topx_GN_LIT_FMT_x.
