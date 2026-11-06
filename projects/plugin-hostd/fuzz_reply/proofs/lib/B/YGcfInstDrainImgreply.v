(* Theorem Labs, 2026-10-30 (CfInstMiss, for lane F2b's drain walk at plugin-hostd/fuzz_reply, reply image B; the B
   twin of lib/A/YGcfInstDrainImgreply.v, same stems).
   rule 24: no function proved (kind: image-row discharge at reply image B).

   The three image premises of the generic cf layer's drain walk (Section T of YGcfInstDrainTop.v: SBC, IQA, CA), stated
   TOKEN-EQUAL to F2b's Definitions at IM := AImg_reply (B/AGif2reply.v): SB_CONST (B/YGcfInstDrainQ.v), IMG_QAPART and
   CONST_APART (B/YGcfInstDrainX.v). None of the three texts reads DImg, CfImg or CfParams, and each binds B itself under
   im_syms B (TfibSyms B at AImg_reply), so no premise is added. Each is CITED from reply B's image rows, not re-proved
   (the values are reply B's own tables, computed there):
   - SB_CONST_reply_B    = ReplyImg_sbconst.SB_CONST_B
   - IMG_QAPART_reply_B  = ReplyImg_qapart.IMG_QAPART_B
   - CONST_APART_reply_B = ReplyImg_constapart.CONST_APART_B (a Theorem Labs lane's case split, 195ad575801) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstDrainX YGcfInstDrainQ.
(* reply B's image rows, used qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_sbconst ReplyImg_qapart ReplyImg_constapart.
Local Open Scope Z_scope.

Theorem SB_CONST_reply_B : SB_CONST (IM := AImg_reply).
Proof. exact ReplyImg_sbconst.SB_CONST_B. Qed.

Theorem IMG_QAPART_reply_B : IMG_QAPART (IM := AImg_reply).
Proof. exact ReplyImg_qapart.IMG_QAPART_B. Qed.

Section r. Context {rc : YM05.RunCeil}.
Theorem CONST_APART_reply_B : CONST_APART (IM := AImg_reply).
Proof. intros B ly c TS LY Hc. exact (ReplyImg_constapart.CONST_APART_B B ly c TS LY Hc). Qed.
End r.
