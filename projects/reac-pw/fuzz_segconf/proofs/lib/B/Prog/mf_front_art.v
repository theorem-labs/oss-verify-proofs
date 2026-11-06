(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the steps of a program walk through a runtime entry whose contract is art_post (lib/A/Rt/RtDefs.v) and whose writes leave the errno cell, after PaArt.v's aj_art_at and cgif_file_fuzzer's aj_intrin_atS: aj_art_own_at, for an entry that writes bytes the caller's journal may write (its side-stack frame, its footprint, a block made in the call), is the sup_resp walk's lemma (an earlier version of lib/A/Prog/sup_resp_s0.v); aj_art_blk_at, for an entry that writes inside one live heap block, and awrite_ok_of_block, the entry's write premise on a range of such a block, are the sup_host_setting walk's lemmas hs5_art_wr_at and hs6_wr_block (lib/A/Prog/sup_host_setting_s5.v and sup_host_setting_s6.v), stated over any segments and symbols. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaArtOwn.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/PaArtOwn.v, with its module paths changed; 21 of its 71 lines of code are new or changed and 81 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3): the journal step of a call of a runtime entry whose
   contract is RtDefs.v's art_post with no cells (E = fun _ => False), for S_MF_FRONT's calls of the strchr
   (0x86380) and strlen (0x863a8) wrappers. It is PaArt.v:76 aj_art_at at Eb = fun _ => False, without its Section
   hypothesis errno_low : api_env SEGS B (PaArt.v:75): no hypothesis of the FRONT pieces gives api_env (only
   SegPaLib.v's PALib does, pal_env), and an entry that writes nothing outside its scratch window does not need it.
   The step is YCbq.v's ajournal_after_write (Section a0: AR_laws and the image below kLowMemEnd only), as image A's
   lib/A/Prog/m_file_memchr.v aj_memchr_at (a working branch) steps its memchr call. A walk lane
   of the image-B m_file-family owner's G2B, piece 1 (a working branch). Statement and proof; no instruction is executed
   here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* the entry writes only its scratch window [sp0 + o - stk, sp0 + o) below the call's sp, which lies inside the
   walk's STK below its sp0: the journal goes on with the same footprint, owned frames and event count *)
Lemma fr_art_at : forall stk pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_post segs B stk lyc Sc W regsT memT mdc (fun _ => False) Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr HJ Hsp Hal Hneg Hstk Hbud Hraw HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - stk <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); [|intros []].
    unfold ascratch_stk. rewrite Hsp. exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha. cbv beta in Ha. left. left. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw. apply (Hfr a Ha); [|intros []].
unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.
End j.
End d.
