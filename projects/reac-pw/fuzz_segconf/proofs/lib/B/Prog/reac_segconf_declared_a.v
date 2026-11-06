(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4) on the ASan build of plugin-hostd/fuzz_command
   proves its statement tchain_words_spec (chain_words_c.v:94-134) directly: from the six segments and the transport
   (chain_words_a.v's cw_run), at statement passes 4 and 5 (the FP-existential post apost_baseF, the rounding-mode
   premise, no astack_pres). The returned block's size is exact in the statement
   (chain_words_c.v:127), as the walk's post cw_Q (chain_words_d.v) carries it from the two recorder callees. The
   callee contracts and runtime rules are the statement's, in its forall-fx0 form (chain_words_c.v:84-93); the
   per-binary facts the walk names are CmdRecFacts lemmas: relro_img and cmd_ro_ok_of_aro (CmdRecRo.v),
   cmd_prog_unowned (CmdRecImg.v), all over IMG : cmd_img_facts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_exact.v, with its module paths and module names changed; 20 of its 39 lines of code are new or changed and 65 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/trim.v, with its module paths and module names changed; 49 of its 70 lines of code are new or changed and 18 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/reac_segconf_declared_a.v (commit 29221b01c4cd): the assembly
   of the walk of reac_segconf_declared (fuzz_segconf.asan-ubsan, image B, entry 0x89e7c), in the form of
   plugin-hostd/fuzz_command's lib/B/Prog/chain_words_a.v (cw_loop / cw_run): the five segment statements of
   reac_segconf_declared_d.v and an induction over the passes of the loop over c->seg take every entry state with
   dc_pre to dc_post, at image B's stack window DC_STK.
   The induction is downward in the pass index i: a pass i at or past the last entry has no state (INV_KL asks
   i < length (rc_seg rc)), so from_KL holds there without a step; below it, S4 gives from_KT i from from_KL (i+1),
   S3 gives from_KA i from from_KT i, and S2 gives from_KL i from the two. S5 gives from_KX, which S3 and S4 both
   need, and S1 then runs from the entry with from_KX and from_KL 0 at the frame position its own call returns. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
#[local] Notation PRE := (dc_pre B DC_STK RLO RHI GOTW GUARD).
(* every pass of the loop reaches the post: by induction on the passes left, length (rc_seg rc) - i; a pass at or
   past the last entry has no state (INV_KL's fourth conjunct asks i < length (dc_segs c)) *)
Lemma dc_loop_from :
  dc_S2P B DC_STK RLO RHI GOTW GUARD ->
  dc_S3P B DC_STK RLO RHI GOTW GUARD ->
  dc_S4P B DC_STK RLO RHI GOTW GUARD ->
  forall c, PRE c -> from_KX B DC_STK c ->
  forall i, from_KL B DC_STK c i.
Proof.
intros S2 S3 S4 c HP HX.
assert (H : forall n i, (length (dc_segs c) - i <= n)%nat -> from_KL B DC_STK c i).
{ induction n as [|n IH]; intros i Hi.
  - intros ti added ly3 S3' W3 regs3 mem3 md3 (_ & _ & _ & Hlt & _). exfalso. lia.
  - destruct (Nat.lt_ge_cases i (length (dc_segs c))) as [Hlt | Hge].
    + assert (HT : from_KT B DC_STK c i) by (apply (S4 c i HP); [apply IH; lia | exact HX]).
      exact (S2 c i HP HT (S3 c i HP HT HX)).
    + intros ti added ly3 S3' W3 regs3 mem3 md3 (_ & _ & _ & Hlt & _). exfalso. lia. }
intros i. exact (H (length (dc_segs c)) i ltac:(lia)).
Qed.
(* the whole walk, from the entry *)
Theorem dc_run :
  dc_S1P B DC_STK RLO RHI GOTW GUARD ->
  dc_S2P B DC_STK RLO RHI GOTW GUARD ->
  dc_S3P B DC_STK RLO RHI GOTW GUARD ->
  dc_S4P B DC_STK RLO RHI GOTW GUARD ->
  dc_S5P B DC_STK RLO RHI GOTW GUARD ->
  forall c, PRE c ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_reac_segconf_declared) (x_regs c) (x_mem c) (x_md c))
    (dc_post B DC_STK c).
Proof.
intros S1 S2 S3 S4 S5 c HP.
assert (HPf : forall f, PRE (dc_setpos c f))
  by (intros f; exact (dc_pre_setpos B DC_STK RLO RHI GOTW GUARD c f HP)).
assert (HXf : forall f, from_KX B DC_STK (dc_setpos c f))
  by (intros f; exact (S5 _ (HPf f))).
apply (S1 c HP HXf).
intros f. exact (dc_loop_from S2 S3 S4 _ (HPf f) (HXf f) 0).
Qed.
End e.
End f.
End d.
