(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v:76-87 (link_FFL; a working branch c8557374ad2e,
   released at ossv/recipes 053df5cc35b), with its module paths changed to libreac/fuzz_ctrl's image B (ASan-UBSan) core
   (lib/Reusable/YB1v.tfibsegs, lib/Reusable/YCeg.tfib_img_cover). The proof is the donor's, step for step.
   It needs NO syms hypothesis (a Theorem Labs lane's review, 2026-10-29 17:43Z), so the theorem is stated for every B.
   frame_flag_lawP is the core's (lib/Reusable/YCbq.v:799); fuzz_ctrl's image-B model_block / identity_reply glues carry
   it as the premise FFL. Written by a Theorem Labs lane (the unit's reviewer, 17:41Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK04 YG00 YG0a YG01 YG05 YG0f YG0n YG0s YG0t YG0q YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YB1v YCeg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem frame_flag_law_ok : forall B, YCbq.frame_flag_lawP YB1v.tfibsegs B.
Proof.
intros B. pose proof (AR_laws_ok YB1v.tfibsegs B) as LAWS.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YCeg.tfib_img_cover ly S md L) as [C1 C2].
unfold YCeg.TFIB_IMG_LO, YCeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold YCbq.zone2, YCbq.off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

End b.
