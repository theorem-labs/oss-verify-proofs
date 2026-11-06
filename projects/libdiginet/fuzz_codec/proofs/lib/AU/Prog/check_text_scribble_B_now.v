(* check_text_scribble at image B: bs_now (lib/AU/Prog/check_text_scribble_B_inv.v) from the contract's premises.
   The text and the record each lie in one object of the call state (cobj_ok): a heap block, or a live side-stack
   frame. At a boundary state the text's bytes are kept (tcj_kept's block and frame clauses; the write set is the
   record, which the text does not meet), the usable marks of both are kept (a block's by AR's block shadow law,
   a frame's shadow bytes by the frame clause, which the write set does not meet), and the record's shadow window is
   readable (AR, for one block or one frame). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP09 YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh YCem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_inv.
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
Lemma bs_frame_shadow_in : forall ly S (W : world tfibsegs) mem md cid pos x,
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
Lemma bs_obj_kept : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop) p n,
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
Lemma bs_obj_garr8 : forall T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (E : Z -> Prop) p l,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  tdst_ok B lyc Sc p (Z.of_nat (length l)) -> (forall a, p <= a < p + Z.of_nat (length l) -> ~ E a) ->
  garr8 tfibsegs (rd W memc) p l -> garr8 tfibsegs (rd W2 mem2) p l.
Proof.
intros T lyc Sc W memc W2 mem2 sp E p l HK Htd HnE Hg j Hj.
destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. pose proof (Hv 0%nat ltac:(lia)) as H0.
rewrite <- H0. apply (mbyte_of_aview tfibsegs).
apply (bs_obj_kept T lyc Sc W memc W2 mem2 sp E p (Z.of_nat (length l)) HK Htd HnE). lia.
Qed.

(* The usable marks of an object of the entry state stay, when the write set holds no byte of the shadow map's range
   [SB, SB + 2 ^ 44). *)
Lemma bs_obj_ra : forall T lyc Sc (W : world tfibsegs) memc mdc ly2 S2 W2 mem2 md2 sp (E : Z -> Prop) p n,
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
  pose proof (bs_frame_shadow_in lyc Sc W memc mdc cid pos x HAR Hin Hr) as Hz.
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

(* An object of the contract's one-object form lies, byte by byte, in a block or a frame of the entry state. *)
Lemma bs_cobj_tdst : forall lyc Sc q n, cobj_ok B lyc Sc q n -> tdst_ok B lyc Sc q n.
Proof.
intros lyc Sc q n [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] a Ha.
- left. exists b, m. split; [exact Hin | lia].
- right. exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

(* The record holds no byte of the shadow map's range. *)
Lemma bs_wr_off_shadow : forall g, bs_pre B g -> forall a, SB <= a < SB + 2 ^ 44 -> ~ bs_wr g a.
Proof.
intros g Hpre a Ha Hw.
destruct Hpre as ((HJ & _) & _ & _ & _ & _ & _ & Hch & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hch as (_ & _ & Htd & _).
destruct (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HAR Htd Hw) as (_ & Hz).
unfold SB, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The record's shadow window is readable in a state whose blocks are the call state's and whose frames hold the
   call state's at the same addresses. *)
Lemma bs_obj_hull : forall lyc Sc ly2 S2 (W2 : world tfibsegs) mem2 md2 p n,
  AR tfibsegs B ly2 S2 W2 mem2 md2 ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S2)) ->
  (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  cobj_ok B lyc Sc p n -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W2) mem2) p n.
Proof.
intros lyc Sc ly2 S2 W2 mem2 md2 p n HAR2 Hbl Hfr Efa [(b & m & Hin & H1 & H2) | (cid & pos & Hin & H1 & H2)] Hn.
- exact (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 b m p n HAR2 (Hbl b m Hin) H1 H2 Hn).
- apply (shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 cid pos p n HAR2 (Hfr cid pos Hin));
  rewrite ?Efa; lia.
Qed.

(* bs_now from the contract's premises. *)
Lemma bs_now_of : forall g, bs_pre B g -> bs_now B g.
Proof.
intros g Hpre pos ly2 S2 W2 mem2 md2 HJ2 HK Hperm _.
pose proof Hpre as ((HJ & _) & _ & Hcs & Hoq & Hoch & _ & Hch & _ & _ & _ & _ & Hdisj & _).
pose proof HJ as (HAR & Hlyc & _ & _ & _ & Hfrsc & _). pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (Hbl : forall b m, In (b, m) (ablocks B (bs_lyc g) (bs_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym Hperm) Hin)).
assert (Hfr : forall c q, In (c, q) (frames (bs_Sc g)) -> In (c, q) (frames S2))
  by (intros c q Hin; rewrite Hfrs2, <- app_comm_cons; right; rewrite <- Hfrsc; exact Hin).
assert (Efa : forall c q, frame_addr ly2 c q = frame_addr (bs_lyc g) c q).
{ intros c q. unfold frame_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _).
  rewrite E1, E2. reflexivity. }
pose proof (bs_wr_off_shadow g Hpre) as Hws.
destruct Hcs as (_ & Hg & Hz0 & (_ & _ & _ & Hra & _)).
split; [split|split].
- apply (bs_obj_garr8 TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 mem2 (bs_sp g) (bs_wr g)
    (bs_q g) (bs_tb g) HK (bs_cobj_tdst _ _ _ _ Hoq)); [|exact Hg].
  intros a Ha Hw. unfold bs_wr, bs_len in *. lia.
- exact (bs_obj_ra TB_check_text_scribble _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK
    (bs_cobj_tdst _ _ _ _ Hoq) Hws Hra).
- destruct Hch as (_ & _ & Htd & _ & Hra' & _).
  exact (bs_obj_ra TB_check_text_scribble _ _ _ _ _ ly2 S2 W2 mem2 md2 _ _ _ _ HAR HAR2 Hbl HK Htd Hws Hra').
- split; [exact (bs_obj_hull (bs_lyc g) (bs_Sc g) ly2 S2 W2 mem2 md2 (bs_ch g) 24 HAR2 Hbl Hfr Efa Hoch ltac:(lia))|].
  apply (bs_obj_hull (bs_lyc g) (bs_Sc g) ly2 S2 W2 mem2 md2 (bs_q g) (bs_len g) HAR2 Hbl Hfr Efa Hoq).
  unfold bs_len. destruct (bs_tb g) as [|x t]; [destruct Hz0 | cbn [length]; lia].
Qed.
End h.
End d.
