(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: region_kept_tcj_stack and region_kept_tcj_frame are the text of lib/A/ACem.v's
   region_kept_ownframe_aj (copied there from projects/libreac/fuzz_knock/proofs/lib/A/ACem.v) with the call's acall_kept
   replaced by a callee's tcj_kept (lib/A/Prog/CodecCJ.v), cpw_apresent_of_writable that of lib/A/AE7f.v's
   apresent_of_writable; the re-seat in cpw_call_reseat and cpw_rebase is the text of lib/A/AWalkFw2.v's reseatL (copied
   there from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw2.v) with the environment equation kept for env_agree,
   cpw_kept_std that of lib/A/AWalkFw1.v's aconstsF with the region_kept_val cases of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgMain3.v:186-194, and cpw_leaf that of lib/A/Prog/CPgWalk.v's cw_leaf with the
   state's layout, astate and model taken through the calls' chain; for libdiginet/fuzz_codec's ASan build (image A).
   cpw_call, cpw_entry, cpw_kept_run, cpw_io, cpw_keep and cpw_sp_off are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkCall.v; 414 of its 450 lines of code are new or changed and 242 lines of the source are left out. *)
(* check_text_counter's image-A walk: the facts every segment reads off a cut (check_text_counter_A_inv.v) --
   where the side-stack frame (0, pos), its shadow and its flag byte lie, and where a range of the caller lies
   that the contract lets the call write (in a heap block or a side-stack frame of the call's entry state). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import check_text_counter_A_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

(* Two journals from the same start: their layouts place the side stack at the same base. *)
Lemma ctc_frame_addr_eq : forall STK sp0 FP ly S W0 mem0 md0 own1 ly1 S1 W1 mem1 md1 k1 own2 ly2 S2 W2 mem2 md2 k2,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own1 ly1 S1 W1 mem1 md1 k1 ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own2 ly2 S2 W2 mem2 md2 k2 ->
  (forall c p, frame_addr ly2 c p = frame_addr ly1 c p) /\ (forall c p, flag_addr ly2 c p = flag_addr ly1 c p).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own1 ly1 S1 W1 mem1 md1 k1 own2 ly2 S2 W2 mem2 md2 k2
  (_ & Hly1 & _) (_ & Hly2 & _).
destruct Hly1 as (_ & _ & _ & _ & _ & EF1 & _). destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
split; intros c p; [unfold frame_addr | unfold flag_addr]; rewrite EF1, EF2; reflexivity.
Qed.

(* Where the frame (0, pos) of a state S2 = (0, pos) :: frames Sc lies, its shadow, and its flag byte. *)
Lemma ctc_frame_facts : forall ly2 S2 (W2 : world tfibsegs) mem2 md2 lyc Sc pos,
  AR tfibsegs B ly2 S2 W2 mem2 md2 -> frames S2 = (0, pos) :: frames Sc ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) -> (forall c p, flag_addr ly2 c p = flag_addr lyc c p) ->
  let F := frame_addr lyc 0 pos in let FL := flag_addr lyc 0 pos in
  4096 <= F /\ F + 64 <= alloc_ceiling /\ F mod 64 = 0 /\ in_app F 64 /\ off_img F 64 /\
  (forall a, F <= a < F + 64 -> apresent (w_H W2) mem2 a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H W2) mem2 (SB + F / 8 + i)) /\
  4096 <= FL /\ FL < alloc_ceiling /\ app_addr FL /\ off_img FL 1 /\ apresent (w_H W2) mem2 FL /\
  aowned B ly2 S2 FL /\ (FL + 1 <= F \/ F + 64 <= FL).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc pos HAR Hfrs Efa Efl F FL.
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 0 pos HAR Hin) as (HF0 & HFc & HFapp).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 0 pos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 0 pos HAR Hin) as (_ & _ & HFp & HSp).
pose proof (frm_off_img B ly2 S2 W2 mem2 md2 0 pos HAR Hin) as HFimg.
destruct (FFL ly2 S2 W2 mem2 md2 0 pos HAR Hin) as (HLp & HLo & (HLapp & _) & (HL0 & HLz & HLc)).
rewrite Efa in HF0, HFc, HFapp, HF64, HFp, HSp, HFimg. rewrite Efl in HLp, HLo, HLapp, HL0, HLz, HLc.
fold F in HF0, HFc, HFapp, HF64, HFp, HSp, HFimg. fold FL in HLp, HLo, HLapp, HL0, HLz, HLc.
change (fs_frame_bytes 0) with 64 in HFc, HFapp, HFp, HFimg. change (fs_frame_bytes 0 / 8) with 8 in HSp.
unfold shadow_addr in HSp. rewrite <- SB_SHADOW_OFF in HSp.
split; [exact HF0|]. split; [exact HFc|]. split; [exact HF64|]. split; [exact HFapp|]. split; [exact HFimg|].
split; [intros a Ha; exact (proj1 (HFp a Ha))|]. split; [intros i Hi; exact (proj1 (HSp i Hi))|].
split; [exact HL0|]. split; [exact HLc|]. split; [exact HLapp|]. split; [exact (zone2_img _ _ HLz)|].
split; [exact HLp|]. split; [exact HLo|].
destruct (Z_lt_le_dec FL F) as [H|H]; [left; lia|].
destruct (Z_lt_le_dec FL (F + 64)) as [H'|H']; [|right; lia].
exfalso. exact (proj2 (HFp FL (conj H H')) HLo).
Qed.

(* A range of the caller that the contract lets the call write (each byte in a heap block or a side-stack frame of
   the entry state Sc) lies, at a later state S2 with the frame (0, pos) in front of Sc's frames and Sc's blocks
   (up to order), in application memory, off the image, off the frame (0, pos) and its flag byte, and each of its
   bytes is present and the client's. *)
Lemma ctc_dst_facts : forall ly2 S2 (W2 : world tfibsegs) mem2 md2 lyc Sc pos q n,
  AR tfibsegs B ly2 S2 W2 mem2 md2 -> frames S2 = (0, pos) :: frames Sc -> ~ In (0, pos) (frames Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) -> (forall c p, flag_addr ly2 c p = flag_addr lyc c p) ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  tdst_ok B lyc Sc q n -> 0 < n <= 64 ->
  in_app q n /\ off_img q n /\ q + n <= alloc_ceiling /\
  (q + n <= frame_addr lyc 0 pos \/ frame_addr lyc 0 pos + 64 <= q) /\
  (q + n <= flag_addr lyc 0 pos \/ flag_addr lyc 0 pos + 1 <= q) /\
  (forall x, q <= x < q + n -> apresent (w_H W2) mem2 x /\ ~ aowned B ly2 S2 x).
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc pos q n HAR Hfrs Hnin Efa Efl Hperm Hd Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL ly2 S2 W2 mem2 md2 0 pos HAR Hin) as (_ & HLo & _). rewrite Efl in HLo.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
(* each byte *)
assert (BY : forall x, q <= x < q + n ->
  app_addr x /\ (x + 1 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= x) /\ x < alloc_ceiling /\ ~ (F <= x < F + 64) /\ x <> FL /\
  apresent (w_H W2) mem2 x /\ ~ aowned B ly2 S2 x).
{ intros x Hx. destruct (Hd x Hx) as [(b & m & Hbm & Hr) | (c & p & Hcp & Hr)].
  - pose proof (Permutation_in _ (Permutation_sym Hperm) Hbm) as Hbm2.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hbm2) as (_ & Hb4096 & Hbc & Hbapp & Hbp & _).
    pose proof (blk_off_img B ly2 S2 W2 mem2 md2 b m HAR Hbm2) as Hbimg.
    pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 b m 0 pos HAR Hbm2 Hin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efa in Hsep. fold F in Hsep.
    change (fs_frame_bytes 0) with 64 in Hsep.
    destruct (Hbp x ltac:(lia)) as (Hxp & Hxo).
    split; [apply (in_app_addr b (req_size m) x Hbapp); lia|].
    split; [unfold off_img in Hbimg; lia|]. split; [lia|]. split; [lia|].
    split; [intros ->; exact (Hxo HLo)|]. split; [exact Hxp | exact Hxo].
  - assert (Hcp2 : In (c, p) (frames S2)) by (rewrite Hfrs; right; exact Hcp).
    destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 c p HAR Hcp2) as (_ & Hfapp & Hfp & _).
    destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 c p HAR Hcp2) as (Hf0 & Hfc & _).
    pose proof (frm_off_img B ly2 S2 W2 mem2 md2 c p HAR Hcp2) as Hfimg.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- (Efa c p) in Hr.
    assert (Hsep : zdisjoint (frame_rng ly2 (0, pos)) (frame_rng ly2 (c, p))).
    { apply in_split in Hcp as (l1 & l2 & El).
      apply (sep_frames_pos tfibsegs B LAWS ly2 S2 W2 mem2 md2 (0, pos) (c, p) [] l1 l2 HAR).
      rewrite Hfrs, El. reflexivity. }
    unfold zdisjoint, frame_rng in Hsep. cbn [fst snd] in Hsep. rewrite (Efa 0 pos) in Hsep. fold F in Hsep.
    change (fs_frame_bytes 0) with 64 in Hsep.
    destruct (Hfp x ltac:(lia)) as (Hxp & Hxo).
    split; [apply (in_app_addr _ _ x Hfapp); lia|].
    split; [unfold off_img in Hfimg; lia|]. split; [lia|]. split; [lia|].
    split; [intros ->; exact (Hxo HLo)|]. split; [exact Hxp | exact Hxo]. }
destruct (BY q ltac:(lia)) as (A1 & I1 & L1 & F1 & G1 & _).
destruct (BY (q + n - 1) ltac:(lia)) as (A2 & I2 & L2 & F2 & G2 & _).
split.
{ unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
split; [lia|]. split; [lia|].
split.
{ destruct (Z_lt_le_dec FL q) as [H|H]; [right; lia|].
  destruct (Z_lt_le_dec FL (q + n)) as [H'|H']; [|left; lia].
  exfalso. destruct (BY FL ltac:(lia)) as (_ & _ & _ & _ & HX & _). exact (HX eq_refl). }
intros x Hx. destruct (BY x Hx) as (_ & _ & _ & _ & _ & Hp & Ho). exact (conj Hp Ho).
Qed.
End d.

(* The shadow byte of an application byte is not an application byte. *)
Lemma ctc_shadow_apart : forall x c m, 0 <= x -> amem_range x 1 -> amem_range c m -> 0 <= m ->
~ (c <= shadow_of_addr SHADOW_OFF x < c + m).
Proof.
intros x c m Hx0 Hx Hc Hm Hin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Hx, Hc. unfold shadow_of_addr, SHADOW_OFF in Hin.
assert (D0 : 0 <= x / 8) by (apply Z.div_pos; lia).
destruct Hx as [Hx | [Hx1 Hx2]].
- assert (D1 : x / 8 <= 2147450878 / 8) by (apply Z.div_le_mono; lia).
  change (2147450878 / 8) with 268431359 in D1. lia.
- assert (D2 : 17594333495296 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D3 : x / 8 <= 140737488355326 / 8) by (apply Z.div_le_mono; lia).
  change (17594333495296 / 8) with 2199291686912 in D2. change (140737488355326 / 8) with 17592186044415 in D3. lia.
Qed.

(* ================ the caller's objects at a later state (ly2, S2, W2, mem2) of the walk ================
   The objects of the entry state (lyc, Sc): their bytes off what the walk wrote, and their shadow, are what the
   call has kept (tcj_kept's block and frame clauses); the state has the entry's blocks and frames, at the same
   frame addresses; the walk's write set Ew lies in application memory, so no shadow byte is in it. *)
Section o.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variables (lyc : alayout) (Sc : astate) (W : world tfibsegs) (memc : word -> option byte) (mdc : Model)
  (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs) (mem2 : word -> option byte) (md2 : Model)
  (T sp : Z) (Ew : Z -> Prop).
Hypothesis HAR : AR tfibsegs B lyc Sc W memc mdc.
Hypothesis HAR2 : AR tfibsegs B ly2 S2 W2 mem2 md2.
Hypothesis Hbl : forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2).
Hypothesis Hfr : incl (frames Sc) (frames S2).
Hypothesis Hfa : forall c p, frame_addr ly2 c p = frame_addr lyc c p.
Hypothesis KT : tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Ew.
Hypothesis Happ : forall x, Ew x -> amem_range x 1.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ctc_cobj_up : forall q n, cobj_ok B lyc Sc q n -> cobj_ok B ly2 S2 q n.
Proof.
intros q n [(b & m & Hin & H1 & H2) | (c & p & Hin & H1 & H2)].
- left. exists b, m. split; [exact (Hbl b m Hin) | lia].
- right. exists c, p. rewrite (Hfa c p). split; [exact (Hfr _ Hin) | lia].
Qed.
Lemma ctc_tdst_up : forall q n, tdst_ok B lyc Sc q n -> tdst_ok B ly2 S2 q n.
Proof.
intros q n H a Ha. destruct (H a Ha) as [(b & m & Hin & Hr) | (c & p & Hin & Hr)].
- left. exists b, m. split; [exact (Hbl b m Hin) | exact Hr].
- right. exists c, p. split; [exact (Hfr _ Hin)|]. unfold frame_rng in *. cbn [fst snd] in *. rewrite (Hfa c p). exact Hr.
Qed.
Lemma ctc_obj_keep : forall q n x, cobj_ok B lyc Sc q n -> q <= x < q + n -> ~ Ew x ->
  aview tfibsegs (w_H W2) mem2 x = aview tfibsegs (w_H W) memc x.
Proof.
intros q n x Hobj Hx HE. destruct KT as (_ & K2 & _ & K4 & _).
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- replace x with (b + (x - b)) by lia. apply (K2 b m (x - b) Hin); [lia|].
  replace (b + (x - b)) with x by lia. exact HE.
- apply (K4 cid pos x Hin); [|exact HE].
  left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
Lemma ctc_obj_val : forall q n x (w : nat) v, cobj_ok B lyc Sc q n -> q <= x -> x + Z.of_nat w <= q + n ->
  (forall y, x <= y < x + Z.of_nat w -> ~ Ew y) ->
  val_mem tfibsegs (rd W memc) x w v -> val_mem tfibsegs (rd W2 mem2) x w v.
Proof.
intros q n x w v Hobj Hlo Hhi HE Hv.
apply (cw_val_mem_kept (w_H W) (w_H W2) memc mem2 x w v); [|exact Hv].
intros y Hy. exact (ctc_obj_keep q n y Hobj ltac:(lia) (HE y Hy)).
Qed.
Lemma ctc_obj_garr : forall q n x l, cobj_ok B lyc Sc q n -> q <= x -> x + Z.of_nat (length l) <= q + n ->
  (forall y, x <= y < x + Z.of_nat (length l) -> ~ Ew y) ->
  garr8 tfibsegs (rd W memc) x l -> garr8 tfibsegs (rd W2 mem2) x l.
Proof.
intros q n x l Hobj Hlo Hhi HE Hg.
apply (garr8_frame tfibsegs (rd W memc) (rd W2 mem2) x l Hg).
intros a Ha. apply (mbyte_of_aview tfibsegs). apply (ctc_obj_keep q n); [exact Hobj | lia | apply HE; lia].
Qed.
Lemma ctc_obj_ra : forall q n, cobj_ok B lyc Sc q n -> 0 <= q -> amem_range q n ->
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF q n ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF q n.
Proof.
intros q n Hobj Hq Ham HRA.
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- exact (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 b m q n HAR2 (Hbl b m Hin) Hlo Hhi).
- destruct KT as (_ & _ & _ & K4 & _).
  intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs.
  destruct (frame_al64 tfibsegs B lyc Sc W memc mdc cid pos HAR Hin) as (HA64 & HB64 & HBpos).
  set (FA := frame_addr lyc cid pos) in *. set (bs := fs_frame_bytes cid) in *.
  assert (HAq : FA = 64 * (FA / 64)) by (pose proof (Z.div_mod FA 64 ltac:(lia)); lia).
  assert (HBq : bs = 64 * (bs / 64)) by (pose proof (Z.div_mod bs 64 ltac:(lia)); lia).
  assert (HA8 : FA / 8 = 8 * (FA / 64))
    by (rewrite HAq at 1; replace (64 * (FA / 64)) with ((8 * (FA / 64)) * 8) by lia; apply Z.div_mul; lia).
  assert (HB8 : bs / 8 = 8 * (bs / 64))
    by (rewrite HBq at 1; replace (64 * (bs / 64)) with ((8 * (bs / 64)) * 8) by lia; apply Z.div_mul; lia).
  assert (Hxs : FA / 8 <= x / 8 < FA / 8 + bs / 8).
  { split; [apply Z.div_le_mono; lia|]. rewrite HA8, HB8. apply Z.div_lt_upper_bound; lia. }
  apply (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin).
  + right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold FA bs. lia.
  + intros HEx. pose proof (Happ _ HEx) as Ha1.
    assert (Hx1 : amem_range x 1) by (unfold amem_range in *; lia).
    exact (ctc_shadow_apart x _ 1 ltac:(lia) Hx1 Ha1 ltac:(lia) ltac:(lia)).
Qed.
Lemma ctc_obj_hull : forall q n, cobj_ok B lyc Sc q n -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W2) mem2) q n.
Proof.
intros q n Hobj Hn.
destruct Hobj as [(b & m & Hin & Hlo & Hhi) | (cid & pos & Hin & Hlo & Hhi)].
- exact (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 mem2 md2 b m q n HAR2 (Hbl b m Hin) Hlo Hhi Hn).
- apply (shadow_hull_vis_of_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 cid pos q n HAR2 (Hfr _ Hin));
    try rewrite (Hfa cid pos); lia.
Qed.
Lemma ctc_crd_up : forall T0 sp1 q n sp' T', crd_ok tfibsegs W memc sp1 T0 q n -> cobj_ok B lyc Sc q n ->
  (forall x, q <= x < q + n -> ~ Ew x) -> coff_win sp' T' q n -> crd_ok tfibsegs W2 mem2 sp' T' q n.
Proof.
intros T0 sp1 q n sp' T' (Hq & Hqn & Hrd & Hra & Hhv & Ham & _) Hobj HE Hcw.
split; [exact Hq|]. split; [exact Hqn|].
split; [intros a Ha; rewrite (ctc_obj_keep q n a Hobj Ha (HE a Ha)); exact (Hrd a Ha)|].
split; [exact (ctc_obj_ra q n Hobj Hq Ham Hra)|].
split; [intros Hn; exact (ctc_obj_hull q n Hobj Hn)|].
split; [exact Ham | exact Hcw].
Qed.
Lemma ctc_cstr_up : forall T0 sp1 q tb sp' T', cstr_rd tfibsegs W memc sp1 T0 q tb ->
  cobj_ok B lyc Sc q (Z.of_nat (length tb)) ->
  (forall x, q <= x < q + Z.of_nat (length tb) -> ~ Ew x) -> coff_win sp' T' q (Z.of_nat (length tb)) ->
  cstr_rd tfibsegs W2 mem2 sp' T' q tb.
Proof.
intros T0 sp1 q tb sp' T' (Hq & Hg & H0 & Hc) Hobj HE Hcw.
split; [exact Hq|]. split; [exact (ctc_obj_garr _ _ q tb Hobj ltac:(lia) ltac:(lia) HE Hg)|].
split; [exact H0 | exact (ctc_crd_up T0 sp1 q _ sp' T' Hc Hobj HE Hcw)].
Qed.
Lemma ctc_awr_up : forall STK sp0 FP bl0 own own2 a, incl own own2 ->
  awr_byte STK sp0 FP bl0 (ablocks B lyc Sc) lyc own a -> awr_byte STK sp0 FP bl0 (ablocks B ly2 S2) ly2 own2 a.
Proof.
intros STK sp0 FP bl0 own own2 a Hinc [H | [(Hf & b & m & Hin & Hr) | [(b & m & Hin & Hn & Hr) | (c & p & Hin & Hr)]]].
- left. exact H.
- right. left. split; [exact Hf|]. exists b, m. split; [exact (Hbl b m Hin) | exact Hr].
- right. right. left. exists b, m. split; [exact (Hbl b m Hin)|]. split; [exact Hn | exact Hr].
- right. right. right. exists c, p. split; [exact (Hinc _ Hin)|]. rewrite (Hfa c p). exact Hr.
Qed.
Lemma ctc_twr_up : forall STK sp0 FP ly S own own2 sp1 sp' q n, incl own own2 ->
  twr_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp1 q n -> tdst_ok B lyc Sc q n ->
  (forall x, q <= x < q + n -> ~ (sp' - ESTACK <= x < sp')) ->
  twr_ok tfibsegs B STK sp0 FP ly S ly2 S2 own2 W2 mem2 sp' q n.
Proof.
intros STK sp0 FP ly S own own2 sp1 sp' q n Hinc Htw Htd Hwin a Ha.
destruct (Htw a Ha) as (Haw & _ & _ & _).
assert (PO : apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a).
{ destruct (Htd a Ha) as [(b & m & Hin & Hr) | (c & p & Hin & Hr)].
  - destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 (Hbl b m Hin)) as (_ & _ & _ & _ & Hbp & _).
    exact (Hbp a Hr).
  - destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 c p HAR2 (Hfr _ Hin)) as (_ & _ & Hfp & _).
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- (Hfa c p) in Hr. exact (Hfp a Hr). }
split; [exact (ctc_awr_up STK sp0 FP _ own own2 a Hinc Haw)|].
split; [exact (proj1 PO)|]. split; [exact (proj2 PO) | exact (Hwin a Ha)].
Qed.
Lemma ctc_cdst_up : forall STK sp0 FP ly S own own2 sp1 T1 q n q' n' sp' T', incl own own2 ->
  cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp1 T1 q n -> cobj_ok B lyc Sc q n ->
  q <= q' -> q' + n' <= q + n -> 0 < n' -> coff_win sp' T' q' n' ->
  (forall x, q' <= x < q' + n' -> ~ (sp' - ESTACK <= x < sp')) ->
  cdst_ok tfibsegs B STK sp0 FP ly S ly2 S2 own2 W2 mem2 sp' T' q' n'.
Proof.
intros STK sp0 FP ly S own own2 sp1 T1 q n q' n' sp' T' Hinc (Hq & Hqn & Htd & Htw & Hra & Hhv & Ham & _)
  Hobj Hlo Hhi Hn Hcw Hwin.
assert (Hobj' : cobj_ok B lyc Sc q' n')
  by (destruct Hobj as [(b & m & Hin & H1 & H2) | (c & p & Hin & H1 & H2)];
      [left; exists b, m | right; exists c, p]; split; [exact Hin | lia | exact Hin | lia]).
assert (Ham' : amem_range q' n') by (unfold amem_range in *; lia).
split; [lia|]. split; [lia|].
split; [apply ctc_tdst_up; intros a Ha; apply Htd; lia|].
split; [apply (ctc_twr_up STK sp0 FP ly S own own2 sp1 sp' q' n' Hinc);
  [intros a Ha; apply Htw; lia | intros a Ha; apply Htd; lia | exact Hwin]|].
split; [apply (ctc_obj_ra q' n' Hobj' ltac:(lia) Ham'); intros x Hx; apply Hra; lia|].
split; [intros _; exact (ctc_obj_hull q' n' Hobj' Hn)|].
split; [exact Ham' | exact Hcw].
Qed.
End o.

Section p.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* A caller object lies below the allocator ceiling and off the walk's own new frame (0, pos) of a state S2 that
   puts that frame in front of the entry state's frames. *)
Lemma ctc_obj_apart : forall lyc Sc ly2 S2 (W2 : world tfibsegs) mem2 md2 pos q n,
  AR tfibsegs B ly2 S2 W2 mem2 md2 -> frames S2 = (0, pos) :: frames Sc ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  cobj_ok B lyc Sc q n -> 0 <= n ->
  q + n <= alloc_ceiling /\ (q + n <= frame_addr lyc 0 pos \/ frame_addr lyc 0 pos + 64 <= q).
Proof.
intros lyc Sc ly2 S2 W2 mem2 md2 pos q n HAR Hfrs Efa Hbl Hobj Hn.
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct Hobj as [(b & m & Hb & Hlo & Hhi) | (c & p & Hcp & Hlo & Hhi)].
- pose proof (Hbl b m Hb) as Hb2.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hb2) as (_ & _ & Hbc & _).
  pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 b m 0 pos HAR Hb2 Hin) as Hsep.
  unfold zdisjoint, frame_rng in Hsep. cbn [fst snd] in Hsep. rewrite Efa in Hsep.
  change (fs_frame_bytes 0) with 64 in Hsep. split; lia.
- assert (Hcp2 : In (c, p) (frames S2)) by (rewrite Hfrs; right; exact Hcp).
  destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 c p HAR Hcp2) as (_ & Hfc & _).
  assert (Hsep : zdisjoint (frame_rng ly2 (0, pos)) (frame_rng ly2 (c, p))).
  { apply in_split in Hcp as (l1 & l2 & El).
    apply (sep_frames_pos tfibsegs B LAWS ly2 S2 W2 mem2 md2 (0, pos) (c, p) [] l1 l2 HAR).
    rewrite Hfrs, El. reflexivity. }
  unfold zdisjoint, frame_rng in Hsep. cbn [fst snd] in Hsep. rewrite !Efa in Hsep. rewrite Efa in Hfc.
  change (fs_frame_bytes 0) with 64 in Hsep. split; lia.
Qed.
(* The frame (0, pos) and its shadow are present in any later state of the walk that holds the frame. *)
Lemma ctc_frame_present_j : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 mem3 md3 k3 pos F,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) ly3 S3 W3 mem3 md3 k3 ->
  frames S3 = (0, pos) :: frames Sc -> frame_addr lyc 0 pos = F ->
  (forall a, F <= a < F + 64 -> apresent (w_H W3) mem3 a) /\
  (forall a, shadow_addr F <= a < shadow_addr F + 8 -> apresent (w_H W3) mem3 a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly3 S3 W3 mem3 md3 k3 pos F HJ HJ3 Hf HF.
destruct (ctc_frame_addr_eq B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k _ ly3 S3 W3 mem3 md3 k3 HJ HJ3)
  as (Efa & _).
pose proof HJ3 as (HAR3 & _). assert (Hin : In (0, pos) (frames S3)) by (rewrite Hf; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 0 pos HAR3 Hin) as (_ & _ & Hp & Hs).
rewrite Efa, HF in Hp, Hs. change (fs_frame_bytes 0) with 64 in Hp. change (fs_frame_bytes 0 / 8) with 8 in Hs.
split; [intros a Ha; exact (proj1 (Hp a Ha))|].
intros a Ha. pose proof (proj1 (Hs (a - shadow_addr F) ltac:(lia))) as H.
replace (shadow_addr F + (a - shadow_addr F)) with a in H by lia. exact H.
Qed.
End p.

(* A part of a caller object is one. *)
Lemma ctc_cobj_sub : forall B lyc Sc q n q' n', cobj_ok B lyc Sc q n -> q <= q' -> q' + n' <= q + n ->
  cobj_ok B lyc Sc q' n'.
Proof.
intros B lyc Sc q n q' n' [(b & m & Hin & H1 & H2) | (c & p & Hin & H1 & H2)] Hlo Hhi;
  [left; exists b, m | right; exists c, p]; (split; [exact Hin | lia]).
Qed.
(* The counter texts' eight digits: a 0 result has all eight. *)
Lemma ctc_ct2_len : forall n s dot k i seg d r seg' d', ct2_go n s dot i k seg d = (r, seg', d') -> r = 0 ->
  length seg' = (length seg + k)%nat.
Proof.
intros n s dot k. induction k as [|k IH]; intros i seg d r seg' d' H Hr; cbn [ct2_go] in H.
- injection H as <- <- <-. lia.
- destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0)).
  + destruct (i =? 7).
    * injection H as <- _ _. unfold E_RANGE in Hr. lia.
    * rewrite (IH _ _ _ _ _ _ H Hr), length_app. cbn [length]. lia.
  + rewrite (IH _ _ _ _ _ _ H Hr), length_app. cbn [length]. lia.
Qed.
Lemma ctc_lib_len : forall tb r s d, counter_text_spec tb = (r, s, d) -> r = 0 -> length s = 8%nat.
Proof.
intros tb r s d H Hr. unfold counter_text_spec in H.
destruct (ct1_lib tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- exact (ctc_ct2_len n s0 dot 8 0 [] 0 r s d H Hr).
- injection H as <- _ _. unfold E_RANGE in Hr. lia.
Qed.
Lemma ctc_owed_len : forall tb r s d, owed_counter_text_spec tb = (r, s, d) -> r = 0 -> length s = 8%nat.
Proof.
intros tb r s d H Hr. unfold owed_counter_text_spec in H.
destruct (ct1_owe tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- exact (ctc_ct2_len n s0 dot 8 0 [] 0 r s d H Hr).
- injection H as <- _ _. unfold E_RANGE in Hr. lia.
Qed.

(* The counter texts' result codes: 0 or E_RANGE. *)
Lemma ctc_ct2_rc : forall n s dot k i seg d r seg' d', ct2_go n s dot i k seg d = (r, seg', d') -> r = 0 \/ r = E_RANGE.
Proof.
intros n s dot k. induction k as [|k IH]; intros i seg d r seg' d' H; cbn [ct2_go] in H.
- injection H as <- _ _. left. reflexivity.
- destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0)).
  + destruct (i =? 7); [injection H as <- _ _; right; reflexivity | exact (IH _ _ _ _ _ _ H)].
  + exact (IH _ _ _ _ _ _ H).
Qed.
Lemma ctc_owed_rc : forall tb r s d, owed_counter_text_spec tb = (r, s, d) -> r = 0 \/ r = E_RANGE.
Proof.
intros tb r s d H. unfold owed_counter_text_spec in H.
destruct (ct1_owe tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- exact (ctc_ct2_rc n s0 dot 8 0 [] 0 r s d H).
- injection H as <- _ _. right. reflexivity.
Qed.
(* A run whose state has no write window changes no byte. *)
Lemma ctc_frame_of_closed : forall (E : env) rs H (m1 m2 : word -> option byte),
  (forall a, ~ in_wrange E rs a) -> frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H m2 a = aview tfibsegs H m1 a.
Proof.
intros E rs H m1 m2 Hno HF a Ha. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. apply Hno.
Qed.

(* A word chunk of a region whose value is an atom holding v (the walk's save slots, the frame's flag pointer). *)
Lemma ctc_chunk8 : forall E m (n : nat) b lo hi wlo whi cs od (x : nat) v addr,
  YP09.region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 (SOff x 0))) cs -> ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> addr = b + od ->
  val_mem tfibsegs m addr 8 v.
Proof.
intros E m n b lo hi wlo whi cs od x v addr HR Hn Hc Hx Hv ->.
pose proof (field_of_region_any E m n b cs lo hi wlo whi od 8 (SOff x 0) HR Hn Hc ltac:(lia)) as H.
cbn [sv_denot N.to_nat Pos.to_nat] in H. rewrite Hx, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in H by lia.
rewrite Z.mod_small in H by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia). exact H.
Qed.
(* Bytes that read v in aview are a garr8 of v's. *)
Lemma ctc_garr8_of_aview : forall H (m : word -> option byte) a (k : nat) v, 0 <= v < 256 ->
  (forall i, 0 <= i < Z.of_nat k -> aview tfibsegs H m (a + i) = Some v) ->
  garr8 tfibsegs (mrestrict H m) a (repeat v k).
Proof.
intros H m a k v Hv Ha j Hj. rewrite repeat_length in Hj.
rewrite (nth_indep (repeat v k) 0 v) by (rewrite repeat_length; lia). rewrite nth_repeat.
split; [|lia].
destruct (aview_byte tfibsegs H m (a + Z.of_nat j) v (Ha (Z.of_nat j) ltac:(lia))) as (b & Hb & Ev & _).
apply cpg_val_mem1; [lia|]. rewrite Hb. f_equal. subst v. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* A garr8 whose bytes' aview is kept. *)
Lemma ctc_garr8_kept : forall H H' (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg. apply (garr8_frame tfibsegs (mrestrict H m) (mrestrict H' m') a l Hg).
intros x Hx. apply (mbyte_of_aview tfibsegs). apply Hk. exact Hx.
Qed.

(* A one-byte value read back as the byte it stores: a value below 256 that every byte holding the same value holds. *)
Lemma ctc_vm1 : forall m a v, val_mem tfibsegs m a 1 v ->
  exists z, 0 <= z < 256 /\ val_mem tfibsegs m a 1 z /\ (forall a', val_mem tfibsegs m a' 1 v -> val_mem tfibsegs m a' 1 z).
Proof.
intros m a v H. exists (bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 1 0))).
assert (Hr : 0 <= bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 1 0)) < 256)
  by (pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (YO0f.le_byte v 1 0))) as Hq; change (bv_modulus 8) with 256 in Hq; exact Hq).
assert (K : forall a', val_mem tfibsegs m a' 1 v -> val_mem tfibsegs m a' 1 (bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 1 0)))).
{ intros a' H' k Hk. assert (k = 0%nat) by lia. subst k. rewrite (H' 0%nat Hk). f_equal.
  rewrite (YI04.le_byte_small (bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 1 0))) 1 0) by (first [change (2 ^ (8 * Z.of_nat 1)) with 256; exact Hr | lia]).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
split; [exact Hr|]. split; [exact (K a H) | exact K].
Qed.

(* A byte of image A's read-only window is a byte of the image. *)
Lemma ctc_ro_img : forall a, in_roP tfibsegs CA_RLO CA_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. unfold CA_RLO, CA_RHI in Hgot. lia.
Qed.
(* The tables a call reads, at a later state and a deeper window, for a sub-list of the rows. *)
Lemma ctc_cimg_up : forall B lyc Sc (W : world tfibsegs) memc W2 mem2 T sp Ew,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Ew ->
  forall spc Tc sp' T' l l', cimg_rd tfibsegs B CA_RLO CA_RHI W memc spc Tc l ->
  spc - Tc <= sp' - T' -> sp' <= spc -> incl l' l -> cimg_rd tfibsegs B CA_RLO CA_RHI W2 mem2 sp' T' l'.
Proof.
intros B lyc Sc W memc W2 mem2 T sp Ew (_ & _ & K3 & _) spc Tc sp' T' l l' (HR & HF) Hw Hs Hinc.
split.
- intros a Hro Ho He. rewrite (K3 a (ctc_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HF r (Hinc r Hr)) as (Hi & Hc).
  split; [exact Hi|]. destruct Hc as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [unfold coff_win in *; lia|]. split; [exact H6 | exact H7].
Qed.
End b.
