(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the steps of a program walk through a runtime entry whose contract is art_post (lib/A/Rt/RtDefs.v) and whose writes leave the errno cell, after PaArt.v's aj_art_at and cgif_file_fuzzer's aj_intrin_atS: aj_art_own_at, for an entry that writes bytes the caller's journal may write (its side-stack frame, its footprint, a block made in the call), is the sup_resp walk's lemma (an earlier version of lib/A/Prog/sup_resp_s0.v); aj_art_blk_at, for an entry that writes inside one live heap block, and awrite_ok_of_block, the entry's write premise on a range of such a block, are the sup_host_setting walk's lemmas hs5_art_wr_at and hs6_wr_block (lib/A/Prog/sup_host_setting_s5.v and sup_host_setting_s6.v), stated over any segments and symbols. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaArtOwn.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/PaArtOwn.v for fuzz_segconf.asan-ubsan: module paths. *)
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
(* The step through a runtime entry with art_post whose cells [Eb] are bytes the caller's journal may write
   (awr_byte, lib/Reusable/YCbq.v): the snprintf / sprintf destination in the caller's own side-stack frame, a byte
   of its footprint in a live block, a block made in the call. PaArt's aj_art_at with that premise in place of the
   errno one; the journal goes on through ajournal_after_write (YCbq.v) with the written set [Eb] and the entry's
   scratch window. The sup_resp walk's lemma (an earlier version of
   lib/A/Prog/sup_resp_s0.v:64), unchanged. *)
Lemma aj_art_own_at : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_post segs B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr
HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha Hw He. apply (Hfr a Ha); [unfold ascratch_stk; rewrite Hsp; exact Hw | exact He]. }
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => Eb a \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr' a Ha); intros H'; apply Hna; [right | left]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (HEb a Ha) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact HQ|]. exact Hfr'.
Qed.
(* a range inside a live block is one the entries may write, at a state whose sp lies above the heap: the write
   analogue of PaArt's aread_ok_of_block. The sup_host_setting walk's hs6_wr_block (an earlier version of
   lib/A/Prog/sup_host_setting_s6.v:984), over any segments and symbols. *)
Lemma awrite_ok_of_block : forall stk lyc Sc Wc memc mdc (regs : bvmap 5 word) p k d m,
AR segs B lyc Sc Wc memc mdc -> In (p, k) (ablocks B lyc Sc) -> p <= d -> d + m <= p + k -> 0 <= m < 2 ^ 32 ->
alloc_ceiling <= spZ regs - stk ->
awrite_ok segs B stk lyc Sc Wc regs memc d m.
Proof.
intros stk lyc Sc Wc memc mdc regs p k d m HAR Hin Hd Hdm Hm Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hce & _ & Hpres & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
unfold awrite_ok. split; [lia|]. split; [lia|]. split; [exact Hm|]. split.
- intros a Ha. split; [apply (apresent_writable segs); exact (proj1 (Hpres a ltac:(lia)))|].
  split; [exact (proj2 (Hpres a ltac:(lia))) | unfold ascratch_stk; lia].
- split; [exact (amem_range_of_block segs B LAWS lyc Sc Wc memc mdc p k d m HAR Hin Hd ltac:(lia))|].
  split; [exact (range_addressable_of_block segs B LAWS lyc Sc Wc memc mdc p k d m HAR Hin Hd ltac:(lia))|].
  intros Hm0. exact (shadow_hull_vis_of_block segs B LAWS lyc Sc Wc memc mdc p k d m HAR Hin Hd ltac:(lia) Hm0).
Qed.
Hypothesis errno_low : api_env segs B.
(* The step through a runtime entry with art_post whose cells [Eb] lie inside one live block
   [bq, bq + req_size nq) of the state at the call, a block the call may write (a footprint byte of a live block,
   or a block made in this call): the strcat / sprintf target on the heap. PaArt's aj_art_at with the entry's cells
   in that block instead of the errno cell and the inner journal's footprint that block, composed by
   call_effect_journal and ajournal_sub_tok as aj_art_at composes. The sup_host_setting walk's hs5_art_wr_at
   (an earlier version of lib/A/Prog/sup_host_setting_s5.v:1132), over any segments and symbols. *)
Lemma aj_art_blk_at : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
  mdc k (o : Z) raw bq nq (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
In (bq, nq) (ablocks B lyc Sc) -> (forall a, Eb a -> bq <= a < bq + req_size nq) ->
(forall a, bq <= a < bq + req_size nq ->
  (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_post segs B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
   aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw bq nq Qr
  HJ Hsp Hal Hneg Hstk Hbud Hraw Hbq HEb Hcov HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal segs B stk (spZ regsT) (ablocks_fp [(bq, nq)]) lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
  { eapply (call_effect_journal segs B LAWS segs_low errno_low stk lyc Sc W regsT memT mdc lyc Sc W mem2 md2
      Eb (ablocks_fp [(bq, nq)]) [] 0);
    [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr
    | exact HAR | | reflexivity | lia | lia | lia | | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
    - intros a H0 _ _ H3 H4. apply (Hfr a H0); [intros Hs; apply H3; left; exact Hs | exact H4].
    - unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
      repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia].
    - intros a Ha. exists bq, nq. split; [left; exact Hbq|]. split; [exact (HEb a Ha)|].
      left. pose proof (HEb a Ha) as Hr. replace a with (bq + (a - bq)) by lia.
      apply (inFP_ablocks_fp [(bq, nq)] bq nq (a - bq)); [left; reflexivity | lia]. }
  pose proof (ajournal_sub_tok segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT)
    (ablocks_fp [(bq, nq)]) [] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)) as HJ2.
  rewrite app_nil_l, Z.add_0_r in HJ2. apply HJ2.
  intros a Ha. destruct (inFP_ablocks_fp_inv _ a Ha) as (p' & n' & Hpn & Hr).
  destruct Hpn as [Hpn | []]. injection Hpn as <- <-. exact (Hcov a Hr). }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.
End j.
End d.
