(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of cpg_stack_malloc_keep_io is the text of lib/Reusable/YC85.v's
   aj_stack_malloc_atS (copied there from proofs/libreac/fuzz_knock/lib/Reusable/YC85.v, origin/ossv/recipes
   4b6f0df50aa7), with the runtime contract's kept-memory clause and the model clause carried to the post, for
   libdiginet/fuzz_codec's ASan build (image A); the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkFrame.v, with its module paths and module names changed; 176 of its 217 lines of code are new or changed and 447 lines of the source are left out. *)
(* owed_counter_text's oc_now (owed_counter_text_B_inv.v) from facts at the call's entry: an object that lies in a
   heap block or in a frame of the entry state (tdst_ok) keeps, at every state the walk reaches, the value of each byte
   outside the write set (tcj_kept clauses 2 and 4) and the usable marks of its range (a block's shadow from AR's
   shadow law; a frame's shadow from tcj_kept clause 4, the write set holding no byte of the shadow map); dt on the
   caller's machine stack keeps its usable mark from the stack's zero shadow (AR's zero-shadow law); the image's tables
   keep their bytes (tcj_kept clause 3) and their window moves to owed_seg7's call state. The form is
   lib/AU/Prog/diginet_counter_text_B_now.v's. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU owed_counter_text_B_inv owed_counter_text_B_s0_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The shadow byte of a byte of a frame lies in that frame's shadow. *)
Lemma oc_frame_shadow_in : forall ly S (W : world tfibsegs) mem md cid pos x,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) -> in_zr x (frame_rng ly (cid, pos)) ->
  in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S W mem md cid pos x HAR Hin Hx.
pose proof (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hal & _).
pose proof HAR as (M & _).
pose proof (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfs & _).
unfold in_zr, frame_rng, shadow_of_addr, shadow_addr in *. cbn [fst snd] in *.
set (Fa := frame_addr ly cid pos) in *. set (fs := fs_frame_bytes cid) in *.
assert (EF : Fa = 8 * (Fa / 8)).
{ pose proof (Z.div_mod Fa 32 ltac:(lia)). pose proof (Z.div_mod Fa 8 ltac:(lia)).
  assert (Fa mod 8 = 0).
  { rewrite H. rewrite Hal, Z.add_0_r. replace (32 * (Fa / 32)) with ((4 * (Fa / 32)) * 8) by lia.
    apply Z.mod_mul. lia. }
  lia. }
assert (Efs : fs = 8 * (fs / 8)).
{ pose proof (Z.div_mod fs 64 ltac:(lia)). pose proof (Z.div_mod fs 8 ltac:(lia)).
  assert (fs mod 8 = 0).
  { rewrite H. rewrite Hfs, Z.add_0_r. replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia.
    apply Z.mod_mul. lia. }
  lia. }
split.
- apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
- assert (x / 8 < Fa / 8 + fs / 8) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* The bytes of an object of the entry state, off the write set, keep their value. *)
Lemma oc_obj_kept : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop) p n,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  tdst_ok B lyc Sc p n -> (forall a, p <= a < p + n -> ~ E a) ->
  forall a, p <= a < p + n -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a.
Proof.
intros T lyc Sc W memc W2 mem2 sp E p n (_ & K2 & _ & K4 & _) Htd HnE a Ha.
destruct (Htd a Ha) as [(b & m & Hin & Hb) | (cid & pos & Hin & Hr)].
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. exact (HnE a Ha).
- apply (K4 cid pos a Hin); [left; exact Hr | exact (HnE a Ha)].
Qed.
Lemma oc_obj_garr8 : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop) p l,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  tdst_ok B lyc Sc p (Z.of_nat (length l)) -> (forall a, p <= a < p + Z.of_nat (length l) -> ~ E a) ->
  garr8 tfibsegs (rd W memc) p l -> garr8 tfibsegs (rd W2 mem2) p l.
Proof.
intros T lyc Sc W memc W2 mem2 sp E p l HK Htd HnE Hg j Hj.
destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. pose proof (Hv 0%nat ltac:(lia)) as H0.
rewrite <- H0. apply (mbyte_of_aview tfibsegs).
apply (oc_obj_kept T lyc Sc W memc W2 mem2 sp E p (Z.of_nat (length l)) HK Htd HnE). lia.
Qed.

(* The usable marks of an object of the entry state stay, when the write set holds no byte of the shadow map's range
   [SB, SB + 2 ^ 44). *)
Lemma oc_obj_ra : forall T lyc Sc (W : world tfibsegs) memc mdc ly2 S2 W2 mem2 md2 sp (E : Z -> Prop) p n,
  AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B ly2 S2 W2 mem2 md2 ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  tdst_ok B lyc Sc p n -> (forall a, SB <= a < SB + 2 ^ 44 -> ~ E a) ->
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF p n ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF p n.
Proof.
intros T lyc Sc W memc mdc ly2 S2 W2 mem2 md2 sp E p n HAR HAR2 Hbl (_ & _ & _ & K4 & _) Htd HnE Hra x Hx.
destruct (Htd x Hx) as [(b & m & Hin & Hb) | (cid & pos & Hin & Hr)].
- destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 (Hbl b m Hin)) as (Hbs & _).
  apply (block_shadow_range _ _ b (req_size m) x 1 Hbs); lia.
- destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  pose proof (oc_frame_shadow_in lyc Sc W memc mdc cid pos x HAR Hin Hr) as Hz.
  rewrite (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin (or_intror Hz)); [exact Hs|].
  apply HnE.
  pose proof (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & Happ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  unfold in_app, shadow_of_addr, SHADOW_OFF, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* The write set of owed_counter_text holds no byte of the shadow map's range. *)
Lemma oc_wr_off_shadow : forall g, oc_pre B g -> forall a, SB <= a < SB + 2 ^ 44 -> ~ oc_wr g a.
Proof.
intros g Hpre a Ha Hw.
pose proof Hpre as ((HJ & _) & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
destruct (oc_wr_where B g Hpre a Hw) as [H | [H | Hst]].
- assert (Htd : tdst_ok B (og_lyc g) (og_Sc g) a 1) by (intros x Hx; replace x with a by lia; left; exact H).
  destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htd ltac:(lia)) as (_ & Hz).
  unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
- assert (Htd : tdst_ok B (og_lyc g) (og_Sc g) a 1) by (intros x Hx; replace x with a by lia; right; exact H).
  destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htd ltac:(lia)) as (_ & Hz).
  unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
- unfold SB in Ha. lia.
Qed.

(* A range of the caller's machine stack (inside the stack allowance of the call state's layout): its shadow is zero in
   every state the journal reaches (AR's zero-shadow law; both layouts carry the same stack range). *)
Lemma oc_stk_ra : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k own2 ly2 S2
    (W2 : world tfibsegs) mem2 md2 k2 x n,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own2 ly2 S2 W2 mem2 md2 k2 ->
  ly_stk_lo lyc <= x -> x + n <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF x n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own2 ly2 S2 W2 mem2 md2 k2 x n HJc HJ Hx0 Hx1 Hn.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof HJc as (_ & Hlyc & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo' & Eshi' & _).
pose proof (al_zshadow _ _ LAWS ly2 S2 W2 mem2 md2 _ HAR (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
pose proof HAR as (M & _). pose proof (lo_top _ (am_layout _ _ _ _ M)) as (_ & _ & _ & _ & Tlo & Thi & _).
unfold page_aligned in Tlo, Thi.
assert (Elo : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite Eslo, Eslo'; reflexivity).
assert (Ehi : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite Eshi, Eshi'; reflexivity).
rewrite Elo, Ehi in Hz. rewrite Elo in Tlo. rewrite Ehi in Thi.
clear HJ HJc Hly Hlyc Hstk M HAR Eslo Eshi Eslo' Eshi' Elo Ehi.
set (lo := ly_stk_lo lyc) in *. set (hi := ly_stk_hi lyc) in *.
assert (Dlo : lo = 4096 * (lo / 4096)) by (pose proof (Z.div_mod lo 4096 ltac:(lia)); lia).
assert (Dhi : hi = 4096 * (hi / 4096)) by (pose proof (Z.div_mod hi 4096 ltac:(lia)); lia).
assert (L8 : lo / 8 = 512 * (lo / 4096)).
{ transitivity (((512 * (lo / 4096)) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
assert (E8 : (hi - lo) / 8 = 512 * (hi / 4096 - lo / 4096)).
{ transitivity (((512 * (hi / 4096 - lo / 4096)) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
intros y Hy. exists 0. split; [|left; reflexivity].
assert (Y1 : 512 * (lo / 4096) <= y / 8) by (apply Z.div_le_lower_bound; [lia | clear - Dlo Hx0 Hy; lia]).
assert (Y2 : y / 8 < 512 * (hi / 4096)) by (apply Z.div_lt_upper_bound; [lia | clear - Dhi Hx1 Hy; lia]).
assert (Hi : 0 <= y / 8 - lo / 8 < (hi - lo) / 8) by (clear - Y1 Y2 L8 E8; lia).
pose proof (Hz _ Hi) as H0. unfold shadow_of_addr in H0 |- *.
replace (SHADOW_OFF + lo / 8 + (y / 8 - lo / 8)) with (SHADOW_OFF + y / 8) in H0 by ring. exact H0.
Qed.

(* The text, seg and dt parts of oc_now, from oc_pre and the text's place (a heap block or a frame of the entry
   state) at a boundary state. *)
Lemma oc_now_objs : forall g pos ly2 S2 (W2 : world tfibsegs) mem2 md2,
  oc_pre B g -> tdst_ok B (og_lyc g) (og_Sc g) (og_q g) (og_len g) ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  (garr8 tfibsegs (rd W2 mem2) (og_q g) (og_tb g) /\
   range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (og_q g) (og_len g)) /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (og_sg g) 8 /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (og_dt g) 1.
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre Htxt HJ2 HK Hperm.
pose proof Hpre as ((HJ & _) & _ & Hcs & _ & Hsg & _ & _ & _ & Hdt & _ & _ & Hqs & Hqd & _).
pose proof HJ as (HAR & _). pose proof HJ2 as (HAR2 & _).
assert (Hbl : forall b m, In (b, m) (ablocks B (og_lyc g) (og_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym Hperm) Hin)).
pose proof (oc_wr_off_shadow g Hpre) as Hws.
destruct Hcs as (_ & Hg & _ & (_ & _ & _ & Hra & _)).
split; [split|split].
- apply (oc_obj_garr8 TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g)
    (og_q g) (og_tb g) HK Htxt); [|exact Hg].
  intros a Ha [Hw | Hw]; unfold og_len in *; lia.
- exact (oc_obj_ra TB_owed_counter_text _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htxt Hws Hra).
- destruct Hsg as (_ & _ & Htd & _ & Hra' & _).
  exact (oc_obj_ra TB_owed_counter_text _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
- destruct Hdt as [((_ & _ & Htd & _ & Hra' & _) & _) | (_ & _ & Hlo & Hhi & _)].
  + exact (oc_obj_ra TB_owed_counter_text _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
  + exact (oc_stk_ra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2 Hlo Hhi ltac:(lia)).
Qed.

(* An object of the contract's one-object form lies, byte by byte, in a block or a frame of the entry state. *)
Lemma oc_cobj_tdst : forall lyc Sc q n, cobj_ok B lyc Sc q n -> tdst_ok B lyc Sc q n.
Proof.
intros lyc Sc q n [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] a Ha.
- left. exists b, m. split; [exact Hin | lia].
- right. exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

Section s7.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
(* The read window lies in the image. *)
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.

(* The image's read-only data keeps the image's bytes through what the call kept. *)
Lemma oc_arodata_now : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop),
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) memc) ->
  arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W2) mem2).
Proof.
intros T lyc Sc W memc W2 mem2 sp E (_ & _ & K3 & _) HR a Hro Hns Her.
rewrite (K3 a); [exact (HR a Hro Hns Her) | | exact Hns | exact Her].
destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HRELRO a Hr)].
Qed.

(* oc_now from the contract's premises. *)
Lemma oc_now_of : forall g, oc_pre B g -> oc_pre2 B RLO RHI GLYPHA ROSTRS g -> oc_now B RLO RHI GLYPHA ROSTRS g.
Proof.
intros g Hpre (Hoq & _ & Himg) pos ly2 S2 W2 mem2 md2 HJ2 HK Hperm _.
destruct (oc_now_objs g pos ly2 S2 W2 mem2 md2 Hpre (oc_cobj_tdst _ _ _ _ Hoq) HJ2 HK Hperm) as (Htxt & Hsg & Hdt).
split; [exact Htxt|]. split; [exact Hsg|]. split; [exact Hdt|].
destruct Himg as (Haro & Hl).
split; [exact (oc_arodata_now _ _ _ _ _ _ _ _ _ HK Haro)|].
eapply Forall_impl; [|exact Hl]. cbv beta.
intros r (Hro & Hrng). split; [exact Hro|].
destruct Hrng as (H0 & Hn & H63 & Hamr & Hwin & Himgb & Hus).
unfold cimg_range. split; [exact H0|]. split; [exact Hn|]. split; [exact H63|]. split; [exact Hamr|].
split; [|split; [exact Himgb | exact Hus]].
unfold coff_win, og_sp1, TB_owed_counter_text, TB_owed_seg7 in *. change ESTACK with 4096 in *.
pose proof (Z.div_mod (og_sp g - 192) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (og_sp g - 192) 32 ltac:(lia)).
lia.
Qed.
End s7.
End h.
End d.
