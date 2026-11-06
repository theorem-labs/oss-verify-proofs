(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): the B top's XE_LIT_S_x row.  lib/B/ReplyBTop.v's Context premise
     XE_LIT_S_x : forall rc fx, ashp_x PB_fr top_x.ARX (pa_val .. W_bx_defs.AX_lit_empty) 1
   (ReplyBTop.v:89; lib/B/W_LLVMFuzzerTestOneInput_top_x.v:303 at the Section level), stated below token for token,
   so the plug is `exact (topx_XE_LIT_S_x rc fx)`.
   - AX_lit_empty is A_OBJ 25 (lib/B/W_bx_defs.v:91: .str.3 "", 0x20ee0, 1 byte), and lib/B/TopxImageB.v
     ashp_str3_1_fr_cf already proves that shape at the relation `ARcf segs TfibB /\ Hp = []`.  top_x's ARX is that
     relation and one more conjunct, arodata_ok_cf (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:175-177), and ashp_x is antitone in its relation, so
     the row follows by WEAKENING: the ARX hypothesis is taken apart and its first two conjuncts are handed to
     ashp_str3_1_fr_cf.  No shp_check is decided here, so no vm_compute runs (the direct route through
     TopX_LIT.topx_lit_shp did not finish in 15 minutes on a Theorem Labs lane's base).
   proves no function (kind: instance discharge). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB W_bx_defs W_LLVMFuzzerTestOneInput_top_x.
Import ListNotations.
Open Scope Z_scope.

(* ReplyBTop.v:89 XE_LIT_S_x: .str.3 "", A_OBJ 25 = 0x20ee0, 1 byte *)
Lemma topx_XE_LIT_S_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_x.ashp_x rc (@PB_fr rc) (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (@pa_val rc fr_prog_listing (@PB_fr rc) W_bx_defs.AX_lit_empty) 1.
Proof.
  intros rc fx ly S Hp W mem md (HA & HH & _).
  exact (TopxImageB.ashp_str3_1_fr_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_reply)
           ly S Hp W mem md (conj HA HH)).
Qed.

Print Assumptions topx_XE_LIT_S_x.
