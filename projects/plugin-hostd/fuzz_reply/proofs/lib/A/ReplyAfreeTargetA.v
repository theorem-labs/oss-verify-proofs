(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, row 3D of the primed-free plan, for a Theorem Labs lane's reply top): reply's free
   target at image A, ReplyAllocTargets.afree_target_reply (CfF1's primed text, lib/A/ReplyAllocTargets.v:42-44:
   `forall fx rc, @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_A CfParams_reply tfibsegs TfibB`), from reply's primed
   Deallocate instance ReplyDeallocInst.afree_realizes_cf_rh_reply_all, whose conclusion is that text word for word.
   rule 24: no function proved (kind: statement text; one `exact`).

   a Theorem Labs lane's generated top (lib/A/gen_ReplyATopX.py) binds its Section hypothesis AFREE_CF to afree_target_reply_A.
   It has no premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyAllocTargets ReplyDeallocInst.

Theorem afree_target_reply_A : ReplyAllocTargets.afree_target_reply.
Proof.
exact ReplyDeallocInst.afree_realizes_cf_rh_reply_all.
Qed.
