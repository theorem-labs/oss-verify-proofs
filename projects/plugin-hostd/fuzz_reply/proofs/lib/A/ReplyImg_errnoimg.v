(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs: an image row of the cf layer at plugin-hostd/fuzz_reply image A.
   rule 24: no function proved (kind: image row; an instance discharge at reply's image A from reply's own proved lemmas).

   The cf layer's row ErrnoImgCf is the Record YGcfInstErrno.ErrnoImgCf
   (proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfInstErrno.v:63-73 at commit 9ac4e6bed4f7): one field per
   ErrnoApart Prop, over the image classes ImgBase.AImg / ImgBaseAG.AGImg / ImgBaseDG.DImg.  Reply does not carry that
   layer file yet, so [errno_img_cf_A] states the Record's UNFOLDED text: the conjunction of its nine fields, in the
   field order of the Record (ei_in_img, ei_unhidden, ei_dzone_ag, ei_shadow_ag, ei_inst_ag, ei_dzone_d, ei_izone,
   ei_zone3_d, ei_inst_d), at reply's instances AImg_reply (A/AGif2reply.v), AGImg_reply (A/AGif0reply.v) and DImg_reply
   (A/DGif0reply.v).  A consumer closes the layer's row with `constructor` and the nine projections once the layer is on
   reply.  Each conjunct is the Definition of reply's A/ErrnoApart.v with the same name (token-identical to the layer's
   Reusable/ErrnoApart.v), proved in A/ErrnoApartreply.v at these instances: the pattern of cgif's
   YGcfInstF1Wcgif.v:52 errno_img_cf_cgif and preset's A/YGcfInstF1WA.v:50 errno_img_cf_A. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply AGif0reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ErrnoApart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoApartreply.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ErrnoImgCf (YGcfInstErrno.v:63-73), unfolded, at image A. *)
Theorem errno_img_cf_A :
  errno_in_img (IM := AImg_reply) /\
  errno_unhidden (IM := AImg_reply) /\
  errno_apart_dzone_ag (IM := AImg_reply) (AG := AGImg_reply) /\
  errno_apart_shadow_ag (IM := AImg_reply) (AG := AGImg_reply) /\
  errno_apart_inst_ag (IM := AImg_reply) (AG := AGImg_reply) /\
  errno_apart_dzone_d (IM := AImg_reply) (DI := DImg_reply) /\
  errno_apart_izone (IM := AImg_reply) (DI := DImg_reply) /\
  errno_apart_zone3_d (IM := AImg_reply) (DI := DImg_reply) /\
  errno_apart_inst_d (IM := AImg_reply) (DI := DImg_reply).
Proof.
split; [exact ErrnoApartreply.errno_in_img_reply|].
split; [exact ErrnoApartreply.errno_unhidden_reply|].
split; [exact ErrnoApartreply.errno_apart_dzone_ag_reply|].
split; [exact ErrnoApartreply.errno_apart_shadow_ag_reply|].
split; [exact ErrnoApartreply.errno_apart_inst_ag_reply|].
split; [exact ErrnoApartreply.errno_apart_dzone_d_reply|].
split; [exact ErrnoApartreply.errno_apart_izone_reply|].
split; [exact ErrnoApartreply.errno_apart_zone3_d_reply|].
exact ErrnoApartreply.errno_apart_inst_d_reply.
Qed.

End a.
