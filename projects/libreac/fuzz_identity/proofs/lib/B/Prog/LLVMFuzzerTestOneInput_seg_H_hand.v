(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 79 of its 118 lines of code are new or changed and 541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D3_hand_stmt.v; 142 of its 176 lines of code are new or changed and 84 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_identity_fw_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_H_hand_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma h_fw_n_range : forall v, 0 <= v < 65536 -> 6 <= fw_n v <= 7.
Proof.
intros v Hv. destruct (Z_lt_le_dec v 10000) as [Hl | Hl].
- rewrite (fw_n_short v) by lia. lia.
- rewrite (fw_n_long v) by lia. lia.
Qed.

Lemma h_mod8 : forall x c, x mod 32 = 0 -> (x + 8 * c) mod 8 = 0.
Proof.
intros x c Hx. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
replace (x + 8 * c) with ((4 * (x / 32) + c) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma h_mod16 : forall m s, m mod 32 = 0 -> s mod 16 = 0 -> (m - s) mod 16 = 0.
Proof.
intros m s Hm Hs. pose proof (Z.div_mod m 32 ltac:(lia)) as D1. pose proof (Z.div_mod s 16 ltac:(lia)) as D2.
rewrite Hm, Z.add_0_r in D1. rewrite Hs, Z.add_0_r in D2.
replace (m - s) with ((2 * (m / 32) - s / 16) * 16) by lia. apply Z_mod_mult.
Qed.

Lemma h_anyfw_range : h_anyfw_range_stmt.
Proof.
unfold h_anyfw_range_stmt. intros inp. unfold SlotModel.t_any_fw, SlotModel.tb.
pose proof (SlotModel.inb_range inp (SlotModel.cT inp + 9)) as A9.
pose proof (SlotModel.inb_range inp (SlotModel.cT inp + 10)) as A10.
lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
Variable B : asyms.

Lemma h_fw_call : @h_fw_call_stmt fx rc SK PI B.
Proof.
unfold h_fw_call_stmt.
intros LAWS TL HFWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pos mf SF v
  HJ Hfrs Hown HSF Hra H2 H3 H4 H10 H11 H12 Hv Hal Hmf1 Hmf2 Hstk Hzf.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin) as (HF0 & HF1 & _).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin) as (HF32 & _).
rewrite HSF in HF0, HF1, HF32. change (fs_frame_bytes 4) with 1024 in HF1.
pose proof asan_consts as (C1 & _).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HFS : REAC_IDENTITY_FW_STR_STK = 4112) by reflexivity.
pose proof (h_fw_n_range v Hv) as Hn.
assert (Hsp : spZ regs = mf).
{ unfold spZ. rewrite H2. apply unsigned_lit_small. clear - Hmf2 Hstk Hceil Hslo Hshi H47 C1 HES. lia. }
assert (H8 : (SF + 464) mod 8 = 0) by exact (h_mod8 SF 58 HF32).
assert (P1 : 0 <= SF + 464 < 2 ^ 64) by (clear - HF0 HF1 C1; lia).
assert (P2 : 0 <= 8 < 2 ^ 64) by (clear; lia).
assert (P3 : spZ regs mod 16 = 0).
{ rewrite Hsp. replace mf with (mf - 0) by ring. exact (h_mod16 mf 0 Hal eq_refl). }
assert (P4 : sp0 - STK <= spZ regs - REAC_IDENTITY_FW_STR_STK) by (rewrite Hsp, HFS; clear - Hstk HES; lia).
assert (P5 : spZ regs <= sp0) by (rewrite Hsp; clear - Hmf2; lia).
refine (HFWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v (SF + 464) 8 HJ Hra H10 H11 H12 Hv
  P1 P2 P3 P4 P5 _).
intros _. unfold fw_dest_ok. split; [|split].
- unfold tdst_ok. intros a Ha. right. exists 4, pos. split; [exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite HSF. change (fs_frame_bytes 4) with 1024. clear - Ha Hn. lia.
- unfold twr_ok. intros a Ha.
  lazymatch goal with |- ?P /\ _ => assert (Hw : P) end.
  { right; right; right. exists 4, pos. split; [rewrite Hown; left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite HSF. change (fs_frame_bytes 4) with 1024. clear - Ha Hn. lia. }
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
  rewrite Hsp, HES. clear - Ha Hn HF1 Hceil Hslo Hstk HES. lia.
- apply (range_addressable_sub _ _ (SF + 464) 8); [| clear; lia | clear - Hn; lia].
  apply zero_shadow_range; [exact H8 | reflexivity | exact Hzf].
Qed.

Lemma h_bcmp_call : @h_bcmp_call_stmt fx rc SK PI B.
Proof.
unfold h_bcmp_call_stmt.
intros LAWS ABCMP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pos mf SF n raw
  HJ Hfrs HSF Hra Hraw H2 H3 H4 H10 H11 H12 Hn Hal Hmf1 Hmf2 Hstk Hzf Hze.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin) as (HF0 & HF1 & HFapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin) as (HF32 & _ & HFb & _).
rewrite HSF in HF0, HF1, HFapp, HF32, HFb. change (fs_frame_bytes 4) with 1024 in HF1, HFapp, HFb.
pose proof asan_consts as (C1 & _).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regs = mf).
{ unfold spZ. rewrite H2. apply unsigned_lit_small. clear - Hmf2 Hstk Hceil Hslo Hshi H47 C1 HES. lia. }
assert (H8x : (SF + 464) mod 8 = 0) by exact (h_mod8 SF 58 HF32).
assert (H8y : (SF + 496) mod 8 = 0) by exact (h_mod8 SF 62 HF32).
assert (N1 : 0 <= n < 2 ^ 32) by (clear - Hn; lia).
assert (X0 : 0 <= SF + 464) by (clear - HF0; lia).
assert (X1 : SF + 464 + n <= 2 ^ 63) by (clear - Hn HF1 C1; lia).
assert (Y0 : 0 <= SF + 496) by (clear - HF0; lia).
assert (Y1 : SF + 496 + n <= 2 ^ 63) by (clear - Hn HF1 C1; lia).
assert (SP : spZ regs = sp0 + (mf - sp0)) by (rewrite Hsp; ring).
assert (O16 : (mf - sp0) mod 16 = 0) by exact (h_mod16 mf sp0 Hal Hal16).
assert (ONEG : mf - sp0 <= 0) by (clear - Hmf2; lia).
assert (OBUD : 2 * ESTACK - (mf - sp0) <= STK) by (clear - Hstk; lia).
assert (SX : src_ok SEGS W regs memc (SF + 464) n).
{ intros a Ha. split.
  - apply (aview_some_of_apresent SEGS). exact (proj1 (HFb a ltac:(clear - Ha Hn; lia))).
  - rewrite Hsp, HES. clear - Ha Hn HF1 Hceil Hslo Hstk HES. lia. }
assert (SY : src_ok SEGS W regs memc (SF + 496) n).
{ intros a Ha. split.
  - apply (aview_some_of_apresent SEGS). exact (proj1 (HFb a ltac:(clear - Ha Hn; lia))).
  - rewrite Hsp, HES. clear - Ha Hn HF1 Hceil Hslo Hstk HES. lia. }
assert (BX : forall a, SF + 464 <= a < SF + 464 + n -> ~ (sp0 + (mf - sp0) - 2 * ESTACK <= a < sp0 + (mf - sp0)))
  by (intros a Ha; clear - Ha Hn HF1 Hceil Hslo Hstk; lia).
assert (BY : forall a, SF + 496 <= a < SF + 496 + n -> ~ (sp0 + (mf - sp0) - 2 * ESTACK <= a < sp0 + (mf - sp0)))
  by (intros a Ha; clear - Ha Hn HF1 Hceil Hslo Hstk; lia).
assert (MX : amem_range (SF + 464) n)
  by exact (amem_range_sub_app SF 1024 (SF + 464) n HFapp HF1 ltac:(clear; lia) ltac:(clear - Hn; lia)
    ltac:(clear - Hn; lia)).
assert (MY : amem_range (SF + 496) n)
  by exact (amem_range_sub_app SF 1024 (SF + 496) n HFapp HF1 ltac:(clear; lia) ltac:(clear - Hn; lia)
    ltac:(clear - Hn; lia)).
assert (RX : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 464) n).
{ apply (range_addressable_sub _ _ (SF + 464) 8); [| clear; lia | clear - Hn; lia].
  apply zero_shadow_range; [exact H8x | reflexivity | exact Hzf]. }
assert (RY : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) n).
{ apply (range_addressable_sub _ _ (SF + 496) 16); [| clear; lia | clear - Hn; lia].
  apply zero_shadow_range; [exact H8y | reflexivity | exact Hze]. }
assert (HX : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) memc) (SF + 464) n).
{ intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc 4 pos (SF + 464) n HAR Hin
    ltac:(rewrite HSF; clear; lia) ltac:(rewrite HSF; change (fs_frame_bytes 4) with 1024; clear - Hn; lia)
    ltac:(clear - Hn; lia)). }
assert (HY : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) memc) (SF + 496) n).
{ intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc 4 pos (SF + 496) n HAR Hin
    ltac:(rewrite HSF; clear; lia) ltac:(rewrite HSF; change (fs_frame_bytes 4) with 1024; clear - Hn; lia)
    ltac:(clear - Hn; lia)). }
eapply SRr_mono.
{ exact (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W regs memc
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (SF + 464) (SF + 496) n (mf - sp0) raw HJ H10 H11 H12
    N1 X0 X1 Y0 Y1 SP O16 ONEG OBUD H3 H4 Hra Hraw SX SY BX BY MX MY RX HX RY HY). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hcmp & Hfr & Hpres).
split; [reflexivity|]. exists regs2, mem2, md2, res.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|].
split; [|exact Hpres].
intros a Ha Hna. apply (Hfr a Ha). replace (sp0 + (mf - sp0)) with mf by ring. exact Hna.
Qed.

Check (h_fw_call : @h_fw_call_stmt fx rc SK PI B).
Check (h_bcmp_call : @h_bcmp_call_stmt fx rc SK PI B).
End c.
End b.
End a.
Check (h_anyfw_range : h_anyfw_range_stmt).
Print Assumptions h_fw_call.
Print Assumptions h_bcmp_call.
Print Assumptions h_anyfw_range.
