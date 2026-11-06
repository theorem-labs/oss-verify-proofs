(* diginet_counter_text's ct_now (diginet_counter_text_A_inv.v) from facts at the call's entry: an object that lies
   in a heap block or in a frame of the entry state (tdst_ok) keeps, at every state the walk reaches, the value of each
   byte outside the write set (tcj_kept clauses 2 and 4) and the usable marks of its range (a block's shadow from AR's
   shadow law; a frame's shadow from tcj_kept clause 4, the write set holding no byte of the shadow map). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgChkC CPgWalk CPgWalkKept.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_counter_text_A_inv.
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
Lemma ct_frame_shadow_in : forall ly S (W : world tfibsegs) mem md cid pos x,
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
Lemma ct_obj_kept : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop) p n,
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
Lemma ct_obj_garr8 : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop) p l,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  tdst_ok B lyc Sc p (Z.of_nat (length l)) -> (forall a, p <= a < p + Z.of_nat (length l) -> ~ E a) ->
  garr8 tfibsegs (rd W memc) p l -> garr8 tfibsegs (rd W2 mem2) p l.
Proof.
intros T lyc Sc W memc W2 mem2 sp E p l HK Htd HnE Hg j Hj.
destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. pose proof (Hv 0%nat ltac:(lia)) as H0.
rewrite <- H0. apply (mbyte_of_aview tfibsegs).
apply (ct_obj_kept T lyc Sc W memc W2 mem2 sp E p (Z.of_nat (length l)) HK Htd HnE). lia.
Qed.

(* The usable marks of an object of the entry state stay, when the write set holds no byte of the shadow map's range
   [SB, SB + 2 ^ 44). *)
Lemma ct_obj_ra : forall T lyc Sc (W : world tfibsegs) memc mdc ly2 S2 W2 mem2 md2 sp (E : Z -> Prop) p n,
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
  pose proof (ct_frame_shadow_in lyc Sc W memc mdc cid pos x HAR Hin Hr) as Hz.
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

(* The write set of diginet_counter_text holds no byte of the shadow map's range. *)
Lemma ct_wr_off_shadow : forall g, ct_pre B g -> forall a, SB <= a < SB + 2 ^ 44 -> ~ ct_wr g a.
Proof.
intros g Hpre a Ha Hw.
destruct Hpre as ((HJ & _) & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hw as [Hw | Hw].
- destruct Hsg as (_ & _ & Htd & _).
  destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htd Hw) as (_ & Hz).
  unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
- destruct Hdt as (_ & _ & Htd & _).
  destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htd Hw) as (_ & Hz).
  unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The text, seg and dt parts of ct_now, from ct_pre and the text's place (a heap block or a frame of the entry
   state) at a boundary state. *)
Lemma ct_now_objs : forall g pos ly2 S2 (W2 : world tfibsegs) mem2 md2,
  ct_pre B g -> tdst_ok B (cg_lyc g) (cg_Sc g) (cg_q g) (cg_len g) ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  tcj_kept tfibsegs B T_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  (garr8 tfibsegs (rd W2 mem2) (cg_q g) (cg_tb g) /\
   range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_q g) (cg_len g)) /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_sg g) 8 /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_dt g) 1.
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre Htxt HJ2 HK Hperm.
pose proof Hpre as ((HJ & _) & _ & Hcs & _ & Hsg & _ & _ & _ & Hdt & _ & _ & Hqs & Hqd & _).
pose proof HJ as (HAR & _). pose proof HJ2 as (HAR2 & _).
assert (Hbl : forall b m, In (b, m) (ablocks B (cg_lyc g) (cg_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym Hperm) Hin)).
pose proof (ct_wr_off_shadow g Hpre) as Hws.
destruct Hcs as (_ & Hg & _ & (_ & _ & _ & Hra & _)).
split; [split|split].
- apply (ct_obj_garr8 T_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g)
    (cg_q g) (cg_tb g) HK Htxt); [|exact Hg].
  intros a Ha [Hw | Hw]; unfold cg_len in *; lia.
- exact (ct_obj_ra T_counter_text _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htxt Hws Hra).
- destruct Hsg as (_ & _ & Htd & _ & Hra' & _).
  exact (ct_obj_ra T_counter_text _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
- destruct Hdt as (_ & _ & Htd & _ & Hra' & _).
  exact (ct_obj_ra T_counter_text _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
Qed.

(* An object of the contract's one-object form lies, byte by byte, in a block or a frame of the entry state. *)
Lemma cobj_tdst : forall lyc Sc q n, cobj_ok B lyc Sc q n -> tdst_ok B lyc Sc q n.
Proof.
intros lyc Sc q n [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] a Ha.
- left. exists b, m. split; [exact Hin | lia].
- right. exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

Section s7.
Variables RLO RHI SEG7TBL : Z.
(* The read window lies in the image, and the image holds a byte at each address of the seg7 table. *)
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
Hypothesis HSEG7ROM : forall a, SEG7TBL <= a < SEG7TBL + 364 -> seg_rom tfibsegs (Z_to_bv 64 a) <> None.

(* The image's read-only data keeps the image's bytes through what the call kept. *)
Lemma ct_arodata_now : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop),
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) memc) ->
  arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W2) mem2).
Proof.
intros T lyc Sc W memc W2 mem2 sp E (_ & _ & K3 & _) HR a Hro Hns Her.
rewrite (K3 a); [exact (HR a Hro Hns Her) | | exact Hns | exact Her].
destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HRELRO a Hr)].
Qed.

(* An address the image holds a byte at reads a value in every memory. *)
Lemma ct_rom_aview : forall (H : word -> bool) (m : word -> option byte) a,
  seg_rom tfibsegs (Z_to_bv 64 a) <> None -> aview tfibsegs H m a <> None.
Proof.
intros H m a Hr. unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [discriminate | exfalso; exact (Hr eq_refl)].
Qed.

(* ct_now from the contract's premises. *)
Lemma ct_now_of : forall g, ct_pre B g -> ct_pre2 B RLO RHI SEG7TBL g -> ct_now B RLO RHI SEG7TBL g.
Proof.
intros g Hpre (Hoq & _ & _ & Haro & Himg) pos ly2 S2 W2 mem2 md2 HJ2 HK Hperm _.
destruct (ct_now_objs g pos ly2 S2 W2 mem2 md2 Hpre (cobj_tdst _ _ _ _ Hoq) HJ2 HK Hperm) as (Htxt & Hsg & Hdt).
split; [exact Htxt|]. split; [exact Hsg|]. split; [exact Hdt|].
apply Forall_inv in Himg. cbn [fst snd] in Himg. destruct Himg as (Hro & Hrng).
destruct Hrng as (H0 & _ & H63 & Hamr & Hwin & _ & Hus).
pose proof HJ2 as (HAR2 & _).
split; [exact (ct_arodata_now _ _ _ _ _ _ _ _ _ HK Haro)|].
split; [exact Hro|].
destruct (Hus ly2 S2 W2 mem2 md2 HAR2) as (Hra & Hhv).
unfold crd_ok. split; [exact H0|]. split; [exact H63|].
split; [intros a Ha; apply ct_rom_aview; apply HSEG7ROM; exact Ha|].
split; [exact Hra|]. split; [exact Hhv|]. split; [exact Hamr|].
unfold coff_win, cg_sp1, T_counter_text, T_seg7 in *. change ESTACK with 4096 in *.
pose proof (Z.div_mod (cg_sp g - 160) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (cg_sp g - 160) 32 ltac:(lia)).
lia.
Qed.
End s7.
End h.
End d.
