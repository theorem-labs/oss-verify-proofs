(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 227 of its 280 lines of code are new or changed and 3287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/SbDec.v, with its module paths and module names changed; 78 of its 115 lines of code are new or changed and 243 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require SbDecSeg1 SbDecSeg2 SbDecSegL SbDecSegE.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma sbd_lsd_len : forall k v, (1 <= k)%nat -> (1 <= length (sb_dec_c.sb_dec_lsd v k) <= k)%nat.
Proof.
induction k as [|k IH]; intros v Hk; [lia|]. cbn [sb_dec_c.sb_dec_lsd].
destruct (v <? 10); cbn [length]; [lia|].
destruct k as [|k]; [cbn; lia|]. pose proof (IH (v / 10) ltac:(lia)). lia.
Qed.
Lemma sbd_D_len : forall v md, (md = 1 \/ md = 2) ->
  1 <= Z.of_nat (length (sb_dec_c.sb_dec_D v md)) <= 3.
Proof.
intros v md Hmd. unfold sb_dec_c.sb_dec_D. rewrite length_rev.
pose proof (sbd_lsd_len 3 v ltac:(lia)) as H.
destruct (Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3)) <? md) eqn:E.
- apply Z.ltb_lt in E. rewrite length_app. cbn [length]. lia.
- lia.
Qed.
Lemma sbd_room_nonneg : forall cap n, 0 <= sb_dec_c.sb_dec_room cap n.
Proof. intros cap n. unfold sb_dec_c.sb_dec_room. destruct (n + 1 <=? cap) eqn:E; [apply Z.leb_le in E; lia | lia]. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PX : PAXcalls lib_both3_0_listing}.
Section h.
Variable B : asyms.
Lemma sbd_loop : forall X, sbd_cx B X -> sbd_segL_stmt B -> sbd_segE_stmt B ->
  forall (j : nat) e W1 c1, sbd_atL B X (Z.of_nat j) e W1 c1 -> SRr SEGS W1 c1 (sbd_post B X).
Proof.
intros X HX SL SE j. induction j as [|j IH]; intros e W1 c1 (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hst).
- eapply SRr_bind; [exact (SL X pos (Z.of_nat 0) e regs1 lyc1 Sc1 W1 memc1 mdc1 HX Hst)|].
  intros W2 c2 _ [[Hj _] | [_ (pos2 & regs2 & lyc2 & Sc2 & memc2 & mdc2 & -> & HE)]]; [lia|].
  exact (SE X pos2 regs2 lyc2 Sc2 W2 memc2 mdc2 HX HE).
- eapply SRr_bind; [exact (SL X pos (Z.of_nat (S j)) e regs1 lyc1 Sc1 W1 memc1 mdc1 HX Hst)|].
  intros W2 c2 _ [[_ HL] | [Hj _]]; [|lia].
  replace (Z.of_nat (S j) - 1) with (Z.of_nat j) in HL by lia. exact (IH (e + 1) W2 c2 HL).
Qed.
Lemma pb_sb_dec_of_segs : sbd_seg1_stmt B -> sbd_seg2_stmt B -> sbd_segL_stmt B -> sbd_segE_stmt B ->
  tsb_dec_spec B.
Proof.
intros S1 S2 SL SE. unfold tsb_dec_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch A v md p cap n over
  HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 Hch Hal Hlo Hhi Hfr Hv Hmd HA0 HA8 HA63 HAam HAimg HAside
  Hp Hcap Hn0 Hn Hov Vp Vcap Vn Vov HAra HAhv HAwr Hout.
set (X := SbdIn fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A v md p cap n over).
pose proof (sbd_room_nonneg cap n) as Hr0.
assert (HX : sbd_cx B X).
{ unfold sbd_cx, sbd_rec, sbd_recP, sbd_outP, sbd_SP, sbd_ne, sbd_ov, sbd_room, sbd_acc, sbd_D.
  cbn [si_fq si_STK si_sp0 si_FP si_ly si_S si_W0 si_mem0 si_md0 si_own si_lyc si_Sc si_W si_memc si_mdc
    si_k si_regs si_A si_v si_md si_p si_cap si_n si_over X].
  rewrite (Z.min_l 0 _ Hr0), Z.add_0_r.
  assert (E0 : (sb_dec_c.sb_dec_room cap n <? 0) = false) by (apply Z.ltb_ge; exact Hr0). rewrite E0.
  repeat (split; [assumption|]).
  split; [split; [exact Vp|]; split; [exact Vcap|]; split; [exact Vn|]; split; [exact Vov|];
          intros _; cbn [Z.to_nat firstn]; apply garr8_nil|].
  split; [split; [exact HAra|]; split; [exact HAhv | exact HAwr]|].
  exact Hout. }
change (SRr SEGS (si_W X) (cfg_at (fx := si_fq X) SEGS (BASE + AF_both3_sb_dec) (si_regs X) (si_memc X) (si_mdc X))
  (sbd_post B X)).
eapply SRr_bind; [exact (S1 X HX)|].
intros W1 c1 _ (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & HA).
eapply SRr_bind; [exact (S2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HA)|].
intros W2 c2 _ HL.
pose proof (sbd_D_len v md Hmd) as HLr.
assert (Hj : sbd_L X - 1 = Z.of_nat (Z.to_nat (sbd_L X - 1))).
{ unfold sbd_L, sbd_D. cbn [si_v si_md X]. lia. }
rewrite Hj in HL. exact (sbd_loop X HX SL SE _ 0 W2 c2 HL).
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TSB : tsb_ch_spec B.
Theorem pb_sb_dec : tsb_dec_spec B.
Proof.
exact (pb_sb_dec_of_segs (SbDecSeg1.sbd_seg1 B LAWS TL ML ASM0 TLF SMP) (SbDecSeg2.sbd_seg2 B LAWS)
  (SbDecSegL.sbd_segL B LAWS TSB) (SbDecSegE.sbd_segE B LAWS ML ASF FFL)).
Qed.
End h.
End f.
End d.
