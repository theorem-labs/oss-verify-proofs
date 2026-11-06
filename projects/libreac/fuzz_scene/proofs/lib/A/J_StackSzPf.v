(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the PROOFS of the two caller-side journal steps that lib/A/J_StackSz.v only
   STATES, for libreac/fuzz_scene's asan tree: `aj_set_shadow_at_stmt` (a call to an __asan_set_shadow_XX
   entry) and `aj_stack_malloc_sz_at_stmt` (a call to a size-dependent __asan_stack_malloc_N entry).  Each statement
   is J_StackSz.v's text, used unchanged: this file only Requires it and proves `<name> : <name>_stmt segs B`.
   The source of both proofs is cgif_rgb_fuzzer lib/YC05.v (c8557374ad2e): :206-258 aj_set_shadow_at and
   :143-205 aj_stack_malloc_sz_at, restated over cgif_file_fuzzer's journal.
     - set-shadow: rgb's write rule YC05.v:39-142 ajournal_after_write_win is, for this tree, the proved lemma of
       lib/Reusable/StackFreeJournal.v (a Theorem Labs lane, landed by a Theorem Labs lane), whose event premise is `st_nev S' <= st_nev Sc`
       where rgb has `bud_le Sc S' 0 0 0 0`.  The contract it consumes is lib/Reusable/SetShadowDef.v's
       aset_shadow_realizes; the proof reads only its first five post clauses (AR, registers, model, the filled
       bytes, the bytes kept), so it does not depend on whether that file's post also carries a presence clause.
       Proved by a Theorem Labs lane (a working branch 0733d73bbad); kept here byte for byte.
     - stack-malloc: the contract is lib/Reusable/AsStackSz.v's astack_malloc_sz_realizes (a Theorem Labs lane).  rgb's
       `vev S2 = vev Sc` is this journal's `st_nev S2 = st_nev Sc` (the step adds no event), rgb's qtightB is this
       tree's qtight (YG01.qtight_ext), and this ajournal has seventeen fields, not sixteen.  The body is
       lib/Reusable/YCbq.v:1749-1809 aj_stack_malloc_at (the class-only twin) with the size argument `n` threaded
       through the contract and the zero_shadow clause.
   This file names no image value: the runtime entry pc and the frame class are arguments. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFreeJournal.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import J_StackSz.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Notation frames_bounds := (YCbq.frames_bounds segs B LAWS).
(* rgb YC05.v:206-258. *)
Lemma aj_set_shadow_at : aj_set_shadow_at_stmt segs B.
Proof.
unfold aj_set_shadow_at_stmt.
intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
assert (Hoff : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
{ intros a Ha Hni Hp. destruct (Z_le_gt_dec q a) as [Hqa|Hqa]; [destruct (Z_lt_ge_dec a (q + n)) as [Han|Han]|].
  - specialize (Heff (a - q) ltac:(lia)). replace (q + (a - q)) with a in Heff by lia.
    destruct Hp as [Hh _]. split; [exact Hh|]. unfold aview, mbyte, mrestrict in Heff. rewrite Hh in Heff.
    destruct (mem2 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso.
    rewrite (seg_rom_none segs a Ha Hni) in Heff. discriminate.
  - eapply (apresent_transfer segs); [exact Ha | exact Hni | apply Hfr; [exact Ha | lia] | exact Hp].
  - eapply (apresent_transfer segs); [exact Ha | exact Hni | apply Hfr; [exact Ha | lia] | exact Hp]. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_win segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => q <= a < q + n) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha Hna).
  - intros a Ha Hp. apply Hoff; [lia | intros Hi; pose proof (segs_low a Hi); lia | exact Hp].
  - exact Hsame.
  - intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr | exact Hoff].
Qed.
(* rgb YC05.v:143-205, over the size-dependent contract AsStackSz.astack_malloc_sz_realizes and this tree's
   journal (st_nev in place of vev; qtight in place of qtightB; the seventeen-field ajournal). *)
Lemma aj_stack_malloc_sz_at : aj_stack_malloc_sz_at_stmt segs B.
Proof.
unfold aj_stack_malloc_sz_at_stmt.
intros pc cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw n
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Hn Hn8 Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 n HPRE Ha0 Hn Hn8 Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal segs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p m i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End h.
End j.
Print Assumptions aj_set_shadow_at.
Print Assumptions aj_stack_malloc_sz_at.
