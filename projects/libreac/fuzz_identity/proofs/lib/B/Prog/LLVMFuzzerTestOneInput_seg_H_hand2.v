(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACgc.v:176-178;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjv.v:45-51, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:154-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg3.v, with its module paths and module names changed; 110 of its 170 lines of code are new or changed and 2480 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_H_hand2_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma hpd_mod8 : forall x c, x mod 32 = 0 -> (x + 8 * c) mod 8 = 0.
Proof.
intros x c Hx. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
replace (x + 8 * c) with ((4 * (x / 32) + c) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma hpd_m4096_m8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
replace x with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma hpd_dec_len_pos : forall v mn, 0 < dec_len v mn.
Proof.
intros v mn. unfold dec_len, DEC. rewrite length_app. cbn [dec_digits]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma hpd_zs_vis : forall (rd : Z -> option Z) q L a n,
  q mod 8 = 0 -> L mod 8 = 0 -> 0 <= q -> 0 <= L ->
  zero_shadow rd SHADOW_OFF q L ->
  q + 64 <= a -> 0 < n -> a + n + 64 <= q + L ->
  range_addressable rd SHADOW_OFF a n /\ shadow_hull_vis rd a n.
Proof.
intros rd q L a n Hq8 HL8 Hq0 HL0 Hz Hqa Hn Hhi.
assert (Hra : range_addressable rd SHADOW_OFF q L)
  by (apply zero_shadow_range; [exact Hq8 | exact HL8 | exact Hz]).
split; [eapply range_addressable_sub; [exact Hra | lia | lia]|].
assert (Hdq : (q + 64) / 8 = q / 8 + 8)
  by (replace (q + 64) with (q + 8 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
assert (D1 : q / 8 + 8 <= a / 8) by (rewrite <- Hdq; apply Z.div_le_mono; lia).
assert (HqL : (q + L) / 8 = q / 8 + L / 8).
{ pose proof (Z.div_mod L 8 ltac:(lia)) as DL.
  replace (q + L) with (q + (L / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (D2 : (a + n - 1) / 8 + 8 <= q / 8 + L / 8).
{ rewrite <- HqL. replace ((a + n - 1) / 8 + 8) with ((a + n - 1 + 8 * 8) / 8)
    by (rewrite Z.div_add by lia; reflexivity).
  apply Z.div_le_mono; lia. }
intros s Hs. unfold shadow_addr in Hs.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as U1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as U2.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as V1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as V2.
replace s with (shadow_of_addr SHADOW_OFF q + (s - SHADOW_OFF - q / 8))
  by (unfold shadow_of_addr; lia).
rewrite (Hz (s - SHADOW_OFF - q / 8) ltac:(unfold SHADOW_OFF in *; lia)). discriminate.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
Variable B : asyms.

Lemma h_pd_call : @h_pd_call_stmt fx rc SK PI B.
Proof.
unfold h_pd_call_stmt.
intros LAWS HPD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pos mf SF n dv mn
  HJ Hfrs Hown HSF Hev Hra H4096 H2 H3 H4 H10 H11 H12 H13 Hdv Hmn Hal Hmf1 Hmf2 Hstk
  Hceil H47 Hslo Hshi Hn Hnd Hval Hzf Hpres.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin) as (HF0 & HF1 & HFapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin) as (HF32 & _ & HFb & _).
rewrite HSF in HF0, HF1, HFapp, HF32, HFb. change (fs_frame_bytes 4) with 1024 in HF1, HFapp, HFb.
pose proof asan_consts as (C1 & _ & C3 & C4 & _).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HPS : PUT_DEC_STK = 4208) by reflexivity.
assert (HE0 : EV_PUT_DEC = 0) by reflexivity.
pose proof (hpd_dec_len_pos dv mn) as Hdl0.
assert (Hsp : spZ regs = mf).
{ unfold spZ. rewrite H2. apply unsigned_lit_small. clear - Hmf2 Hstk Hceil Hslo Hshi H47 C1 HES. lia. }
assert (H8y : (SF + 496) mod 8 = 0) by exact (hpd_mod8 SF 62 HF32).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
assert (A8 : ly_stk_lo lyc mod 8 = 0) by exact (hpd_m4096_m8 _ Hpal).
assert (B8 : ly_stk_hi lyc mod 8 = 0) by exact (hpd_m4096_m8 _ Hpah).
assert (L8 : (ly_stk_hi lyc - ly_stk_lo lyc) mod 8 = 0) by (rewrite Zminus_mod, A8, B8; reflexivity).
pose proof (hpd_zs_vis (aview SEGS (w_H W) memc) (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) (mf + 208) 8
  A8 L8 ltac:(clear - Hceil C1; lia) ltac:(clear - Hslo Hshi Hstk Hmf2 HES; lia) Hz
  ltac:(clear - Hslo Hstk HES; lia) ltac:(clear; lia) ltac:(clear - Hshi Hmf2; lia)) as (ZR & ZH).
assert (R12a : bv_unsigned (getr regs 12) mod 2 ^ 32 = dv)
  by (rewrite H12; apply Z.mod_small; clear - Hdv; lia).
assert (R12b : bv_unsigned (getr regs 12) < 2 ^ 32 \/ 10 <= dv) by (left; rewrite H12; clear - Hdv; lia).
assert (Rmn : 0 <= mn <= 10) by (clear - Hmn; lia).
assert (Rs32 : spZ regs mod 32 = 0) by (rewrite Hsp; exact Hal).
assert (Rslo : sp0 - STK <= spZ regs - PUT_DEC_STK) by (rewrite Hsp, HPS; clear - Hstk HES; lia).
assert (Rshi : spZ regs <= sp0) by (rewrite Hsp; clear - Hmf2; lia).
assert (Rfr : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; cbn [length]; lia).
assert (Rp8 : (mf + 208) mod 8 = 0) by exact (hpd_mod8 mf 26 Hal).
assert (Rb0 : 0 <= SF + 496) by (clear - HF0; lia).
assert (TW1 : twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (mf + 208) 8).
{ unfold twr_ok. intros a Ha.
  lazymatch goal with |- ?P /\ _ => assert (Hw : P) end.
  { left. clear - Ha Hmf2 Hstk HES. lia. }
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
  rewrite Hsp. clear - Ha. lia. }
assert (TW2 : twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (SF + 496 + n) (dec_len dv mn)).
{ unfold twr_ok. intros a Ha.
  lazymatch goal with |- ?P /\ _ => assert (Hw : P) end.
  { right; right; right. exists 4, pos. split; [rewrite Hown; left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite HSF. change (fs_frame_bytes 4) with 1024. clear - Ha Hn Hnd. lia. }
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
  rewrite Hsp, HES. clear - Ha Hn Hnd HF1 Hceil Hslo Hstk HES. lia. }
assert (TS1 : tsrc_ok W memc (spZ regs) (mf + 208) 8).
{ unfold tsrc_ok. split; [|split; [exact ZR|split; [exact ZH|split; [|split]]]].
  - intros a Ha. split.
    + apply (aview_some_of_apresent SEGS). apply Hpres. clear - Ha Hmf2 Hstk HES. lia.
    + rewrite Hsp. clear - Ha. lia.
  - unfold amem_range. right. rewrite C3, C4. clear - Hmf2 Hstk Hceil Hslo Hshi H47 C1 HES. lia.
  - clear - Hmf2 Hstk Hceil Hslo C1 HES. lia.
  - clear - Hmf2 Hshi H47. lia. }
assert (TS2 : tsrc_ok W memc (spZ regs) (SF + 496 + n) (dec_len dv mn)).
{ unfold tsrc_ok. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. split.
    + apply (aview_some_of_apresent SEGS). exact (proj1 (HFb a ltac:(clear - Ha Hn Hnd; lia))).
    + rewrite Hsp, HES. clear - Ha Hn Hnd HF1 Hceil Hslo Hstk HES. lia.
  - apply (range_addressable_sub _ _ (SF + 496) 16); [| clear - Hn; lia | clear - Hn Hnd; lia].
    apply zero_shadow_range; [exact H8y | reflexivity | exact Hzf].
  - exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc 4 pos (SF + 496 + n) (dec_len dv mn) HAR Hin
      ltac:(rewrite HSF; clear - Hn; lia) ltac:(rewrite HSF; change (fs_frame_bytes 4) with 1024; clear - Hn Hnd; lia)
      Hdl0).
  - exact (amem_range_sub_app SF 1024 (SF + 496 + n) (dec_len dv mn) HFapp HF1 ltac:(clear - Hn; lia)
      ltac:(clear - Hn Hnd; lia) ltac:(clear - Hdl0; lia)).
  - clear - HF0 Hn. lia.
  - clear - HF1 Hn Hnd C1. lia. }
assert (D1 : mf + 208 + 8 <= SF + 496 + n \/ SF + 496 + n + dec_len dv mn <= mf + 208)
  by (right; clear - Hn Hnd HF1 Hceil Hslo Hstk HES; lia).
assert (D2 : spZ regs <= mf + 208 \/ mf + 208 + 8 <= spZ regs - PUT_DEC_STK) by (left; rewrite Hsp; clear; lia).
assert (D3 : spZ regs <= SF + 496 + n \/ SF + 496 + n + dec_len dv mn <= spZ regs - PUT_DEC_STK)
  by (right; rewrite Hsp, HPS; clear - Hn Hnd HF1 Hceil Hslo Hstk HES; lia).
assert (EV : st_nev Sc + EV_PUT_DEC <= EV_MAX) by (rewrite HE0; clear - Hnev Hev; lia).
exact (HPD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (SF + 496) (mf + 208) n dv mn
  HJ Hra H4096 H3 H4 H10 H11 R12a R12b H13 Rmn Rs32 Rslo Rshi Rfr Rp8 Rb0 Hn Hval TW1 TW2 TS1 TS2 D1 D2 D3 EV).
Qed.

Check (h_pd_call : @h_pd_call_stmt fx rc SK PI B).
End c.
End b.
End a.
Print Assumptions h_pd_call.
