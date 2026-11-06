(* Theorem Labs, 2026-10-30 (CfInstMiss, for lane F2b's drain walk at plugin-hostd/fuzz_reply, reply image A).
   rule 24: no function proved (kind: image-row discharge at reply image A).

   The three image premises of the generic cf layer's drain walk (Section T of YGcfInstDrainTop.v: SBC, IQA, CA), stated
   TOKEN-EQUAL to F2b's Definitions at IM := AImg_reply (A/AGif2reply.v): SB_CONST (A/YGcfInstDrainQ.v),
   IMG_QAPART and CONST_APART (A/YGcfInstDrainX.v), the files ReplyCfSync carries by path from cf-f2b-hull
   558af51dcc1. None of the three texts reads DImg, CfImg or CfParams, and each binds B itself under im_syms B (TfibSyms B
   at AImg_reply), so no premise is added. The cgif twin is a Theorem Labs lane's YGcfInstDrainImgcgif.v (a Theorem Labs lane
   e75683af832a). Each is CITED from reply A's image rows, not re-proved (the values are reply A's own tables, computed
   there):
   - SB_CONST_reply_A    = ReplyImg_sbconst.SB_CONST_A     (vm_compute over reply A's const table, AF0m.v's Tfib_const)
   - IMG_QAPART_reply_A  = ReplyImg_qapart.IMG_QAPART_A    (reply A's TfibSyms fields and numerals; qhdr_inst unfolded)
   - CONST_APART_reply_A = ReplyImg_constapart.CONST_APART_A (a Theorem Labs lane's case split, over ly_img_ok unfolded)
   The B twin (lib/B/YGcfInstDrainImgreply.v) has the same stems with _B. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstDrainX YGcfInstDrainQ.
(* reply A's image rows, used qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImg_sbconst ReplyImg_qapart ReplyImg_constapart.
Local Open Scope Z_scope.

Theorem SB_CONST_reply_A : SB_CONST (IM := AImg_reply).
Proof. exact ReplyImg_sbconst.SB_CONST_A. Qed.

Theorem IMG_QAPART_reply_A : IMG_QAPART (IM := AImg_reply).
Proof. exact ReplyImg_qapart.IMG_QAPART_A. Qed.

Section r. Context {rc : YM05.RunCeil}.
Theorem CONST_APART_reply_A : CONST_APART (IM := AImg_reply).
Proof. intros B ly c TS LY Hc. exact (ReplyImg_constapart.CONST_APART_A B ly c TS LY Hc). Qed.
End r.
