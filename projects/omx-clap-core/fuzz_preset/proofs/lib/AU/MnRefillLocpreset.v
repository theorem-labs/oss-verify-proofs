(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/MnRefillLocreply.v (commit 4d286b2e618d, file sha256 802f1ab4ec55) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillLoccgif.v (commit 30a1993588f, c5 + memnorm; file sha256 c420700196db) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/MnRefillLocpreset.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-29 (a prior worker, hand H1 of task MEMNORM; lead a prior worker, integrator ReallocPrimary).
   rule 24: no function proved (kind: location facts - the refill and Enqueue write windows are mn_safe at cgif).
   At cgif_file's image: a byte of the stack, the thread object, the primary space / region info / free arrays or the
   high shadow is [MemnormT.mn_safe tfibsegs] (off every read-only segment byte, below TASK_SIZE).  Built on a prior worker's
   MemnormHitG.mn_safe_high / mn_safe_owned and MemnormLoc (commit fd6ec37fd04); the primary space
   and its region info / free arrays are MemnormLoc.mn_safe_ceil.  Every existing statement is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitG MemnormLoc.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill windows' zones.                                                                                       *)

(* the stack [ly_stk_lo, ly_stk_hi): above kHighMemBeg, below kHighMemEnd (YG0f.v:321-323) *)
Lemma mn_safe_stack : forall ly (x : word), layout_ok ly -> ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY Hx. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

(* the thread object [ly_T, + kThreadObjSize): an owned extent *)
Lemma mn_safe_thread : forall ly (x : word), layout_ok ly -> img_cover ly ->
  ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize -> MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY IMG Hx.
exact (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG ltac:(unfold owned_extents; right; right; left; reflexivity) Hx).
Qed.

(* the high shadow [kHighShadowBeg, kHighShadowEnd) *)
Lemma mn_safe_hshadow : forall (x : word), kHighShadowBeg <= bv_unsigned x < kHighShadowEnd -> MemnormT.mn_safe tfibsegs x.
Proof. intros x Hx. apply MemnormHitG.mn_safe_high. unfold kHighShadowBeg, kHighShadowEnd, kImgEnd, TASK_SIZE in *. lia. Qed.
End b.
