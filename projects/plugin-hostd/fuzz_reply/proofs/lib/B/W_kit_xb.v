(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: HAND-WRITTEN, image B only (fuzz_reply.asan-ubsan), lane W4 for the B ARx walks.
   The generated lib/B/W_kit_x.v states blk_off_imgP_x over the Reusable YCbq's off_img, whose image top is image A's
   0x5fb000 (XcfFinish's ruling (3): B's _x kit is stated over the same YCbq as B's old kit). That is true on B but
   weaker than what B's old walks read from lib/B/W_kit.v's blk_off_imgP (lib/B/YCbq.v's off_img, top 0x5fc000).
   A B walk that separates a heap block from an image object in [0x5fb000, 0x5fc000) (W_kit.v pa_obj_img bounds the
   objects by 0x5fc000) needs B's own top: blk_off_imgB_x below states it numerically, at a generic ARx, from the
   same Section hypotheses as W_kit_x.v Section g and with W_kit_x.v's proof (its case split is already at B's top).
   Every hex literal in this file's code is an image-B number: 0x10000 (the image base) and 0x5fc000 (B's image top,
   YImgTop.IMG_TOP_B). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_kit.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Context {SK : YI16.sink_head}.
Section g.
Context {L : ptable wsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
(* W_kit_x.v Section g's three hypotheses, verbatim *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx hl.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* a live block lies below image B's base or at / above image B's top *)
Lemma blk_off_imgB_x : forall ly S Hp (W : world pa_segs) mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n <= 0x10000 \/ 0x5fc000 <= p.
Proof.
intros ly S Hp W mem md p n HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [C1 C2].
pose proof (req_size_pos n (BLKN ly S Hp W mem md p n HAR Hin)) as [Q _].
destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
{ refine (proj1 (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max p 0x10000) HAR _)).
  left. exists p, n. split; [exact Hin | lia]. }
apply Hc. unfold in_zr. lia.
Qed.
End g.
End d.
End b.
