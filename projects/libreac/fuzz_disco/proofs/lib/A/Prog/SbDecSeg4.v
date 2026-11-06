(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths and module names changed; 1107 of its 1208 lines of code are new or changed and 990 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib SbDecCut SbDecLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Definition s4_buf (v md : Z) : list Z :=
  let ds := sb_dec_c.sb_dec_lsd v 3 in if Z.of_nat (length ds) <? md then ds ++ [48] else ds.
Lemma s4_lsd_S : forall v k, sb_dec_c.sb_dec_lsd v (S k) =
  (48 + v mod 10) :: (if v <? 10 then [] else sb_dec_c.sb_dec_lsd (v / 10) k).
Proof. intros v k. reflexivity. Qed.
Lemma s4_lsd_0 : forall v, sb_dec_c.sb_dec_lsd v 0 = [].
Proof. intros v. reflexivity. Qed.
Lemma s4_len_cons : forall (x : Z) l, length (x :: l) = S (length l).
Proof. intros x l. reflexivity. Qed.
Lemma s4_len_nil : length (@nil Z) = 0%nat.
Proof. reflexivity. Qed.
Lemma s4_lsd_len : forall v k, (1 <= length (sb_dec_c.sb_dec_lsd v (S k)) <= S k)%nat.
Proof.
intros v k. revert v. induction k as [|k IH]; intros v; rewrite s4_lsd_S, s4_len_cons.
- destruct (v <? 10); [rewrite s4_len_nil; lia|]. rewrite s4_lsd_0, s4_len_nil. lia.
- destruct (v <? 10); [rewrite s4_len_nil; lia|]. specialize (IH (v / 10)). lia.
Qed.
Lemma s4_D_rev : forall v md, sb_dec_c.sb_dec_D v md = rev (s4_buf v md).
Proof. intros v md. reflexivity. Qed.
Lemma s4_buf_len : forall v md, md = 1 \/ md = 2 -> (1 <= length (s4_buf v md) <= 3)%nat.
Proof.
intros v md Hmd. unfold s4_buf. cbv zeta.
pose proof (s4_lsd_len v 2) as Hl. change (S 2) with 3%nat in Hl.
destruct (Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3)) <? md) eqn:Hb; [|lia].
apply Z.ltb_lt in Hb. rewrite length_app. change (length [48]) with 1%nat. lia.
Qed.
Lemma s4_D_len : forall v md, length (sb_dec_c.sb_dec_D v md) = length (s4_buf v md).
Proof. intros v md. rewrite s4_D_rev. apply length_rev. Qed.
Lemma s4_keep : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  sbd_keep_regs regs regs2 cl -> existsb (Z.eqb (bv_unsigned r)) cl = false -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r HK Hb.
pose proof (u5_range r) as Hr.
assert (Hn : ~ In (bv_unsigned r) cl).
{ intros Hin. assert (E : existsb (Z.eqb (bv_unsigned r)) cl = true)
    by (apply existsb_exists; exists (bv_unsigned r); split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in Hb. discriminate. }
pose proof (HK _ Hr Hn) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma s4_uoff : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof.
intros E n v Hn Hv. rewrite U_SOff, Hn, unsigned_lit_small by lia. rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma s4_c_geu : forall E m n x y, ew E m = Z_to_bv 64 x -> ew E n = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y <= x ->
  branch_taken BC_GEU (sv_denot E (SOff m 0)) (sv_denot E (SOff n 0)) = true.
Proof.
intros E m n x y Hm Hn Hx Hy Hle. cbn [branch_taken]. unfold bv_ltu.
fold (U E (SOff m 0)). fold (U E (SOff n 0)).
rewrite (s4_uoff E m x Hm Hx), (s4_uoff E n y Hn Hy).
apply negb_true_iff. apply Z.ltb_ge. exact Hle.
Qed.
Lemma s4_c_ltu : forall E m n x y, ew E m = Z_to_bv 64 x -> ew E n = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x < y ->
  branch_taken BC_LTU (sv_denot E (SOff m 0)) (sv_denot E (SOff n 0)) = true.
Proof.
intros E m n x y Hm Hn Hx Hy Hlt. cbn [branch_taken]. unfold bv_ltu.
fold (U E (SOff m 0)). fold (U E (SOff n 0)).
rewrite (s4_uoff E m x Hm Hx), (s4_uoff E n y Hn Hy).
apply Z.ltb_lt. exact Hlt.
Qed.
Lemma s4_sv_of_U : forall E e v, U E e = zcanon v -> sv_denot E e = Z_to_bv 64 v.
Proof.
intros E e v H. apply bv_eq. unfold U in H. rewrite H, Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma s4_denot_lit : forall E z v, zcanon z = zcanon v -> sv_denot E (SLit z) = Z_to_bv 64 v.
Proof. intros E z v H. apply s4_sv_of_U. rewrite U_SLit. exact H. Qed.
Lemma s4_alu : forall op (x y : word) v,
  bv_wrap 64 (zalu_raw 63 64 op (bv_unsigned x) (bv_unsigned y)) = bv_wrap 64 v ->
  alu64 op x y = Z_to_bv 64 v.
Proof.
intros op x y v H. apply bv_eq. rewrite alu64_unsigned, H, Z_to_bv_unsigned. reflexivity.
Qed.
Lemma s4_add : forall (x y : word) a b, bv_unsigned x = a -> bv_unsigned y = b ->
  alu64 ALU_ADD x y = Z_to_bv 64 (a + b).
Proof.
intros x y a b Hx Hy. apply s4_alu. cbn [zalu_raw]. rewrite Hx, Hy. reflexivity.
Qed.
Lemma s4_sub0 : forall (y : word) b, bv_unsigned y = b ->
  alu64 ALU_SUB (Z_to_bv 64 0) y = Z_to_bv 64 (- b).
Proof.
intros y b Hy. apply s4_alu. cbn [zalu_raw]. rewrite Hy, unsigned_lit_small by lia.
f_equal; lia.
Qed.
Lemma s4_srl3 : forall (x : word) a, bv_unsigned x = a ->
  alu64 ALU_SRL x (Z_to_bv 64 3) = Z_to_bv 64 (a / 8).
Proof.
intros x a Hx. apply s4_alu. cbn [zalu_raw]. rewrite Hx, unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. reflexivity.
Qed.
Lemma s4_and7 : forall (x : word) a, bv_unsigned x = a -> a mod 8 = 0 ->
  alu64 ALU_AND x (Z_to_bv 64 7) = Z_to_bv 64 0.
Proof.
intros x a Hx Hm. apply s4_alu. cbn [zalu_raw]. rewrite Hx, unsigned_lit_small by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hm. reflexivity.
Qed.
Lemma s4_shadow0 : forall (x y : word) a B, bv_unsigned x = a -> bv_unsigned y = B ->
  0 <= B + a / 8 < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SRL x (Z_to_bv 64 3)) y = Z_to_bv 64 (B + a / 8).
Proof.
intros x y a B Hx Hy Hb.
pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. rewrite Hx in Hr.
assert (Hd : 0 <= a / 8) by (apply Z.div_pos; lia).
rewrite (s4_srl3 x a Hx), (s4_add _ y (a / 8) B ltac:(apply unsigned_lit_small; lia) Hy).
f_equal. lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma s4_fresh : forall lyc Sc lyc1 S2 W2 mem2 md2 cid pos slo shi (Er : Z -> Prop) a,
  AR SEGS B lyc1 S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc1 S2 = ablocks B lyc Sc ->
  (forall c p, frame_addr lyc1 c p = frame_addr lyc c p) -> 0 <= cid ->
  (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
  sbd_wr B lyc Sc slo shi Er a.
Proof.
intros lyc Sc lyc1 S2 W2 mem2 md2 cid pos slo shi Er a HAR2 Hfrs2 Eab HFeq Hcid Ha.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HFa & HFb & HF64).
rewrite HFeq in HF4096, HFc, HFapp, HFa.
pose proof asan_consts as (C1 & _).
set (F := frame_addr lyc cid pos) in *.
destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
split.
{ intros Himg. destruct Ha as [Ha | Ha].
  - assert (Ha' : frame_addr lyc1 cid pos <= a < frame_addr lyc1 cid pos + fs_frame_bytes cid)
      by (rewrite HFeq; exact Ha).
    apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR2
      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin2 Ha'))))))). exact Himg.
  - pose proof (pa_segs_low a Himg). unfold kLowMemEnd, SHADOW_OFF in *. lia. }
right. right. split; [unfold in_app, SHADOW_OFF, kHighMemBeg in *; destruct Ha as [Ha | Ha]; lia|].
split.
- intros b m Hb Hr. rewrite <- Eab in Hb.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd. fold F in Hd.
  destruct Ha as [Ha | Ha]; [lia|].
  apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia | unfold in_app in *; lia | exact Ha].
- intros cid' pos' Hin'.
  assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & _ & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
  rewrite HFeq in HGapp, HG4096, HGc, HGa.
  apply in_split in Hin' as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (cid, pos) (cid', pos') [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !HFeq in Hd. fold F in Hd.
  set (G := frame_addr lyc cid' pos') in *.
  unfold in_zr, frame_rng. cbn [fst snd]. fold G.
  destruct Ha as [Ha | Ha].
  + split; [lia|]. intros Hs.
    apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | exact Hs].
  + split; [intros Hf; apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia | unfold in_app in *; lia | exact Ha]|].
    intros Hs. exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Ha Hs).
Qed.
Lemma s4_not_new : forall STK sp0 FP ly S own lyc Sc lyc1 S2 W2 mem2 md2 cid pos a,
  frames Sc = own ++ frames S -> alloc_ceiling <= sp0 - STK ->
  AR SEGS B lyc1 S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc1 S2 = ablocks B lyc Sc ->
  (forall c p, frame_addr lyc1 c p = frame_addr lyc c p) -> 0 <= cid ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid) /\
  ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8).
Proof.
intros STK sp0 FP ly S own lyc Sc lyc1 S2 W2 mem2 md2 cid pos a Hfrs Hc HAR2 Hfrs2 Eab HFeq Hcid Haw.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HFa & HFb & HF64).
rewrite HFeq in HF4096, HFc, HFapp, HFa.
pose proof asan_consts as (C1 & _).
set (F := frame_addr lyc cid pos) in *.
destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
destruct Haw as [Hs | [[_ (b & m & Hb & Hr)] | [(b & m & Hb & _ & Hr) | (cid' & pos' & Hown & Hr)]]].
- unfold SHADOW_OFF, kHighMemBeg in *. split; lia.
- rewrite <- Eab in Hb. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd. fold F in Hd.
  split; [lia|].
  apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
- rewrite <- Eab in Hb. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd. fold F in Hd.
  split; [lia|].
  apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
- assert (Hin' : In (cid', pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & _ & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
  rewrite HFeq in HGapp, HG4096, HGc, HGa.
  apply in_split in Hin' as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (cid, pos) (cid', pos') [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !HFeq in Hd. fold F in Hd.
  set (G := frame_addr lyc cid' pos') in *.
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + split; [lia|].
    apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
  + pose proof (fs_frame_bytes_nonneg cid') as Hb'.
    split; [intros Hf; apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | lia]|].
    intros Hs. exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Hs Hr).
Qed.
Lemma s4_geom : forall X pos lyc1 Sc1 memc1 mdc1 sh,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh ->
  4096 <= sbd_F X pos /\ sbd_F X pos + 64 <= alloc_ceiling /\ sbd_F X pos mod 64 = 0 /\
  (sbd_F X pos + 64 <= kLowShadowBeg \/ kHighMemBeg <= sbd_F X pos) /\
  sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8 /\
  SHADOW_OFF <= sbd_SH X pos /\ sbd_SH X pos + 8 < kHighMemBeg /\
  (forall a, sbd_F X pos <= a < sbd_F X pos + 64 -> apresent (w_H (si_W X)) memc1 a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H (si_W X)) memc1 (sbd_SH X pos + i)) /\
  alloc_ceiling <= sbd_SP X - SB_DEC_STK /\ sbd_SP X <= 2 ^ 47 /\
  sbd_SP X - 112 <= sbd_SP1 X <= sbd_SP X - 96 /\ sbd_SP1 X mod 32 = 0 /\
  si_sp0 X - si_STK X <= sbd_SP X - SB_DEC_STK /\ sbd_SP X <= si_sp0 X /\
  alloc_ceiling <= si_sp0 X - si_STK X /\ si_sp0 X <= 2 ^ 47.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 sh HX HM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (HSPdef : sbd_SP X = spZ (si_regs X)) by reflexivity.
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hbud & Hsp & _).
pose proof HJX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & _).
pose proof (proj1 HJ1) as HAR1.
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin0) as (HFlo & HFhi & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR1 Hin0) as (HFa & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR1 Hin0) as (_ & _ & HFpres & HSHpres).
rewrite HFeq in HFlo, HFhi, HFapp, HFa, HFpres, HSHpres.
change (fs_frame_bytes 0) with 64 in HFhi, HFapp, HFpres, HSHpres.
change (64 / 8) with 8 in HSHpres.
fold (sbd_F X pos) in HFlo, HFhi, HFapp, HFa, HFpres, HSHpres.
fold (sbd_SH X pos) in HSHpres.
assert (HSH : sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8) by reflexivity.
destruct (shadow_cell_bound (sbd_F X pos) 64 ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2].
change (64 / 8) with 8 in S2. fold (sbd_SH X pos) in S1, S2.
assert (Hsp96 : (sbd_SP X + -96) mod 16 = 0) by (rewrite Zplus_mod, HSPdef, Hal; reflexivity).
destruct (sp1_facts (sbd_SP X + -96) ltac:(lia) Hsp96) as (Hsp1 & Hsp1a & _).
fold (sbd_SP1 X) in Hsp1, Hsp1a.
split; [lia|]. split; [lia|]. split; [exact HFa|].
split; [unfold in_app, ASAN_CEIL in HFapp; lia|].
split; [exact HSH|]. split; [lia|]. split; [lia|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HSHpres i Hi))|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hsp1a|].
split; [lia|]. split; [lia|]. split; lia.
Qed.
Definition s4_wz (X : sbd_in) (pos : Z) (a : Z) : Prop := sbd_F X pos + 33 <= a < sbd_F X pos + 34.
Lemma s4_wz_wr : forall X pos lyc1 Sc1 memc1 mdc1 sh a,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh -> s4_wz X pos a ->
  sbd_wr B (si_lyc X) (si_Sc X) (sbd_SP X - SB_DEC_STK) (sbd_SP X)
    (sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X)) a.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 sh a HX HM Hw.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & _).
pose proof (proj1 HJ1) as HAR1.
apply (s4_fresh (si_lyc X) (si_Sc X) lyc1 Sc1 (si_W X) memc1 mdc1 0 pos _ _ _ a HAR1 Hfrs1 Eab1 HFeq ltac:(lia)).
left. change (fs_frame_bytes 0) with 64. fold (sbd_F X pos). unfold s4_wz in Hw. lia.
Qed.
Lemma s4_rec_nwz : forall X pos lyc1 Sc1 memc1 mdc1 sh a,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh -> si_A X <= a < si_A X + 28 -> ~ s4_wz X pos a.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 sh a HX HM Ha.
destruct (s4_geom X pos lyc1 Sc1 memc1 mdc1 sh HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & HAwr & _).
pose proof HJX as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & _).
pose proof (proj1 HJ1) as HAR1.
destruct (s4_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
  lyc1 Sc1 (si_W X) memc1 mdc1 0 pos a Hfrs Hc0 HAR1 Hfrs1 Eab1 HFeq ltac:(lia) (HAwr a Ha)) as [N1 N2].
change (fs_frame_bytes 0) with 64 in N1. fold (sbd_F X pos) in N1.
unfold s4_wz. lia.
Qed.
Lemma s4_mid_write : forall X pos lyc1 Sc1 memc1 mdc1 memc2 mdc2 sh,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh -> (length sh <= 8)%nat ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) memc2 mdc2 (si_k X) ->
  (forall x : word, ~ s4_wz X pos (bv_unsigned x) ->
     mrestrict (w_H (si_W X)) memc2 x = mrestrict (w_H (si_W X)) memc1 x) ->
  mem_grows (mrestrict (w_H (si_W X)) memc1) (mrestrict (w_H (si_W X)) memc2) ->
  sbd_mid B X pos lyc1 Sc1 memc2 mdc2 sh /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ s4_wz X pos a ->
     aview SEGS (w_H (si_W X)) memc2 a = aview SEGS (w_H (si_W X)) memc1 a).
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 memc2 mdc2 sh HX HM Hlen HJ2 Hfr Hgr.
destruct (s4_geom X pos lyc1 Sc1 memc1 mdc1 sh HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
pose proof HX as (HJX & _).
pose proof (proj1 HJX) as HARX.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ s4_wz X pos a ->
  aview SEGS (w_H (si_W X)) memc2 a = aview SEGS (w_H (si_W X)) memc1 a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia. exact Hn. }
split; [|exact KW].
split; [exact HJ2|]. split; [exact Hfrs1|]. split; [exact Eab1|]. split; [exact HFeq|]. split; [exact HFLeq|].
split.
{ unfold sbd_kept_at.
  eapply (sbd_kept_run B LAWS (si_lyc X) (si_Sc X) (si_W X) (si_memc X) memc1 memc2 (si_mdc X) _ _ _ (s4_wz X pos));
  [exact HARX | exact HK1 | exact Hfr | exact Hgr |].
  intros a _ Hw. exact (s4_wz_wr X pos lyc1 Sc1 memc1 mdc1 sh a HX HM Hw). }
split.
{ intros j r Hj.
  assert (Hjr : (j < 9)%nat)
    by (apply (proj1 (nth_error_Some sbd_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memc2); [| exact (HFr1 j r Hj)].
  intros k Hk. apply KW; [lia | unfold s4_wz; lia]. }
split.
{ apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memc2); [| exact HFL1].
  intros k Hk. apply KW; [lia | unfold s4_wz; lia]. }
intros j Hj.
assert (EL : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (ES : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (Hb1 : 0 <= sbd_SH X pos + j < 2 ^ 64) by lia.
assert (Hb2 : ~ s4_wz X pos (sbd_SH X pos + j)) by (unfold s4_wz; lia).
rewrite (KW _ Hb1 Hb2). exact (HSh1 j Hj).
Qed.
Lemma s4_A_band : forall X, sbd_cx B X ->
  4096 <= si_A X /\ si_A X + 28 <= 2 ^ 47 /\
  (si_A X + 28 <= kLowShadowBeg \/ kHighMemBeg <= si_A X).
Proof.
intros X HX.
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbud & Hsp & _ & _ & _ & _ & HAapp & _).
pose proof HJX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
destruct HAapp as [HAapp | HAapp];
[unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HAapp |- *; lia
| unfold kLowShadowBeg, kHighMemBeg in *; lia].
Qed.
Lemma s4_awr_mono : forall STK sp0 FP bl0 blc ly own cid pos a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly ((cid, pos) :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own cid pos a Haw.
destruct Haw as [Hs | [Hb | [Hb | (cid' & pos' & Hown & Hr)]]];
[left; exact Hs | right; left; exact Hb | right; right; left; exact Hb|].
right; right; right. exists cid', pos'. split; [right; exact Hown | exact Hr].
Qed.
Lemma s4_awr_up : forall X pos lyc1 Sc1 a,
  ablocks B lyc1 Sc1 = ablocks B (si_lyc X) (si_Sc X) ->
  (forall c p, frame_addr lyc1 c p = frame_addr (si_lyc X) c p) ->
  awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
    (ablocks B (si_lyc X) (si_Sc X)) (si_lyc X) (si_own X) a ->
  awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
    (ablocks B lyc1 Sc1) lyc1 ((0, pos) :: si_own X) a.
Proof.
intros X pos lyc1 Sc1 a Eab1 HFeq Haw. apply s4_awr_mono. rewrite Eab1.
destruct Haw as [Hs | [[Hfp Hb] | [Hb | (cid & p' & Hown & Hr)]]];
[left; exact Hs | right; left; split; [exact Hfp | exact Hb] | right; right; left; exact Hb|].
right; right; right. exists cid, p'. split; [exact Hown|]. rewrite (HFeq cid p'). exact Hr.
Qed.
Lemma s4_awr_pres : forall X pos lyc1 Sc1 memc2 mdc2 a,
  sbd_cx B X -> frames Sc1 = (0, pos) :: frames (si_Sc X) ->
  ablocks B lyc1 Sc1 = ablocks B (si_lyc X) (si_Sc X) ->
  (forall c p, frame_addr lyc1 c p = frame_addr (si_lyc X) c p) ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) memc2 mdc2 (si_k X) ->
  awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
    (ablocks B (si_lyc X) (si_Sc X)) (si_lyc X) (si_own X) a ->
  apresent (w_H (si_W X)) memc2 a.
Proof.
intros X pos lyc1 Sc1 memc2 mdc2 a HX Hfrs1 Eab1 HFeq HJ2 Haw.
pose proof HX as (HJX & _).
pose proof HJX as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk2 & _).
assert (Haw1 : awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
  (ablocks B lyc1 Sc1) lyc1 ((0, pos) :: si_own X) a).
{ apply s4_awr_mono. rewrite Eab1.
  destruct Haw as [Hs | [[Hfp Hb] | [Hb | (cid & pos' & Hown & Hr)]]];
  [left; exact Hs | right; left; split; [exact Hfp | exact Hb] | right; right; left; exact Hb|].
  right; right; right. exists cid, pos'. split; [exact Hown|]. rewrite (HFeq cid pos'). exact Hr. }
exact (awr_present B LAWS (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) ((0, pos) :: si_own X)
  lyc1 Sc1 Sc1 (si_W X) memc2 mdc2 a
  ltac:(rewrite Hfrs1, Hfrs; reflexivity) (fun c Hc => Hc) HAR2 eq_refl Hstk2 Haw1).
Qed.
Lemma s4_addr_cur : forall STK sp0 FP (ly : alayout) S own lyc Sc W memc mdc lyc1 S' mem' md'
  slo shi (Er : Z -> Prop) x,
  frames Sc = own ++ frames S -> astk_ok STK ly sp0 ->
  ly_stk_lo lyc1 = ly_stk_lo ly -> ly_stk_hi lyc1 = ly_stk_hi ly ->
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc1 S' W mem' md' -> ablocks B lyc1 S' = ablocks B lyc Sc ->
  sbd_kept B lyc Sc W memc mem' slo shi Er -> ~ Er (shadow_of_addr SHADOW_OFF x) ->
  (x < kLowShadowBeg \/ kHighMemBeg <= x) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x 1 ->
  range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF x 1.
Proof.
intros STK sp0 FP ly S own lyc Sc W memc mdc lyc1 S' mem' md' slo shi Er x Hfrs Hstk Elo Ehi HAR HAR' Eab
  (_ & _ & _ & K4 & _) HnE Happ Haw HRA y Hy.
assert (Hyx : y = x) by lia. subst y.
pose proof (am_layout _ _ _ _ (proj1 HAR')) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Plo & Phi & _).
destruct Hstk as (_ & _ & Hc & Hslo & Hshi & _).
destruct Haw as [Hs | [[_ (b & m & Hb & Hr)] | [(b & m & Hb & _ & Hr) | (cid & pos & Hown & Hr)]]].
- pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo lyc1, ly_stk_hi lyc1 - ly_stk_lo lyc1) HAR'
    (or_introl eq_refl)) as Hz.
  exists 0. split; [|left; reflexivity]. cbn [fst snd] in Hz.
  pose proof (div8_page _ Plo) as Elo8. pose proof (div8_page _ Phi) as Ehi8.
  rewrite Elo in Hz, Elo8. rewrite Ehi in Hz, Ehi8.
  set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
  assert (L1 : lo <= x < hi) by lia.
  assert (Q1 : lo / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (Q2 : x / 8 < hi / 8) by (apply Z.div_lt_upper_bound; lia).
  assert (Q3 : (hi - lo) / 8 = hi / 8 - lo / 8).
  { rewrite Elo8 at 1. rewrite Ehi8 at 1. replace (8 * (hi / 8) - 8 * (lo / 8)) with ((hi / 8 - lo / 8) * 8) by lia.
    apply Z.div_mul. lia. }
  specialize (Hz (x / 8 - lo / 8) ltac:(lia)). unfold shadow_of_addr in *.
  replace (SHADOW_OFF + lo / 8 + (x / 8 - lo / 8)) with (SHADOW_OFF + x / 8) in Hz by lia. exact Hz.
- rewrite <- Eab in Hb. destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR' Hb) as [(Hb8 & Hn0 & Hcells) _].
  set (nn := req_size m) in *.
  pose proof (Z.div_mod (x - b) 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (x - b) 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod nn 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as Dn7. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as Mn7.
  pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
  assert (Exd : x / 8 = b / 8 + (x - b) / 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Exm : x mod 8 = (x - b) mod 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. apply Z.mod_add. lia. }
  set (i := (x - b) / 8) in *.
  exists (if i <? nn / 8 then 0 else nn mod 8). split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + b / 8 + i) by lia.
    apply Hcells. lia.
  + unfold saddr_ok. destruct (Z.ltb_spec i (nn / 8)); [left; reflexivity | right]. lia.
- rewrite <- Eab in Hb. destruct (al_shadow _ _ LAWS _ _ _ _ _ b m HAR' Hb) as [(Hb8 & Hn0 & Hcells) _].
  set (nn := req_size m) in *.
  pose proof (Z.div_mod (x - b) 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (x - b) 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod nn 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as Dn7. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as Mn7.
  pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
  assert (Exd : x / 8 = b / 8 + (x - b) / 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Exm : x mod 8 = (x - b) mod 8).
  { replace x with ((x - b) + (b / 8) * 8) at 1 by lia. apply Z.mod_add. lia. }
  set (i := (x - b) / 8) in *.
  exists (if i <? nn / 8 then 0 else nn mod 8). split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + b / 8 + i) by lia.
    apply Hcells. lia.
  + unfold saddr_ok. destruct (Z.ltb_spec i (nn / 8)); [left; reflexivity | right]. lia.
- assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (HF4096 & HFc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR Hin) as (HFa & HFb & HF64).
  pose proof asan_consts as (C1 & _).
  set (F := frame_addr lyc cid pos) in *.
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + destruct (HRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin); [exact Hs | right | exact HnE].
    unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold F.
    pose proof (div8_64 F HFa) as EF8. pose proof (div8_64 _ HFb) as Eb8.
    assert (Q1 : F / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (Q2 : x / 8 < F / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia).
    lia.
  + exfalso. pose proof (fs_frame_bytes_nonneg cid) as Hb0.
    destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) Hb0 ltac:(lia)) as [S1 S2].
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Definition s4_regs2 (X : sbd_in) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
  sbd_base B X pos regs2 /\ getr regs2 16 = w64 (sbd_F X pos) /\ getr regs2 17 = w64 (sbd_SH X pos) /\
  getr regs2 11 = w64 (si_A X + 16) /\ getr regs2 12 = w64 (si_A X + 8) /\ getr regs2 13 = w64 (si_A X + 24) /\
  getr regs2 5 = w64 (- Z.of_nat (length (s4_buf (si_v X) (si_md X)))) /\
  getr regs2 14 = w64 (sbd_F X pos + 32 + Z.of_nat (length (s4_buf (si_v X) (si_md X))) - 1) /\
  getr regs2 6 = w64 (sbd_F X pos + 32 + Z.of_nat (length (s4_buf (si_v X) (si_md X))) - 1) /\
  getr regs2 7 = w64 (SHADOW_OFF + si_A X / 8) /\ getr regs2 28 = w64 (SHADOW_OFF + (si_A X + 16) / 8) /\
  getr regs2 29 = w64 (SHADOW_OFF + (si_A X + 8) / 8) /\ getr regs2 30 = w64 (SHADOW_OFF + (si_A X + 24) / 8) /\
  getr regs2 31 = w64 3 /\ getr regs2 19 = w64 1.
Definition s4_atL2 (X : sbd_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (memc1 : word -> option byte)
  : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = si_W X /\ exists regs2 mem2 md2,
    c2 = sbd_cfg X SBD_L2 regs2 mem2 md2 /\
    ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
      ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) mem2 md2 (si_k X) /\
    sbd_mid B X pos lyc1 Sc1 mem2 md2 sbd_sh_hdr /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ s4_wz X pos a ->
       aview SEGS (w_H (si_W X)) mem2 a = aview SEGS (w_H (si_W X)) memc1 a) /\
    garr8 SEGS (mrestrict (w_H (si_W X)) mem2) (sbd_F X pos + 32) (s4_buf (si_v X) (si_md X)) /\
    sbd_rec (mrestrict (w_H (si_W X)) mem2) (si_A X) (si_p X) (si_cap X) (si_n X) (si_over X) /\
    s4_regs2 X pos regs2.
Definition s4_rrN : smem := [ YP09.mkRegion (Some 14%nat) 1 2 1 2 [] ].
Definition s4_ssT : sstate :=
  mkSS (AF_sb_dec + SBD_P4) sr_atoms [] None (mkFacts [] [mkAC BC_GEU (SOff 11 0) (SOff 19 0)] []).
Definition s4_ssN : sstate :=
  mkSS (AF_sb_dec + SBD_P4) sr_atoms s4_rrN None (mkFacts [] [mkAC BC_LTU (SOff 11 0) (SOff 19 0)] []).
Definition ES4 (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma s4_lsd_bnd : forall X, (1 <= length (sbm_lsd X) <= 3)%nat.
Proof.
intros X. unfold sbm_lsd. pose proof (s4_lsd_len (si_v X) 2) as Hx. change (S 2) with 3%nat in Hx. exact Hx.
Qed.
Lemma s4_entryT : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 memc1 mdc1,
  sbd_cx B X -> sbd_st4 B X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  si_md X <= Z.of_nat (length (sbm_lsd X)) ->
  st_ok_pi SEGS VAL (ES4 regs1) s4_ssT
    (restrict (w_H (si_W X)) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_P4))) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hge.
pose proof HS4 as (HM & (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427) & R19 & R16 & R17 & R14 & R11 & R15 & HD & Hrec).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hmd & _).
pose proof (s4_lsd_bnd X) as Hl.
rewrite restrict_mkst_fx.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ES4 regs1) n = getr regs1 r)
  by (intros n r Hn; unfold ES4; apply ew_Eimg_Ereg_nat; exact Hn).
unfold s4_ssT. apply pa_entry_st_ok_full.
- unfold ES4. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I|]. split; [|exact I]. split; [|exact I].
  unfold acond_ok. cbn [ac_c ac_a ac_b].
  apply (s4_c_geu _ 11%nat 19%nat (Z.of_nat (length (sbm_lsd X))) (si_md X)).
  + rewrite (EE 11%nat 11%bv eq_refl). exact R11.
  + rewrite (EE 19%nat 19%bv eq_refl). exact R19.
  + lia.
  + lia.
  + exact Hge.
Qed.
Lemma s4_entryN : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 memc1 mdc1,
  sbd_cx B X -> sbd_st4 B X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  Z.of_nat (length (sbm_lsd X)) < si_md X ->
  st_ok_pi SEGS VAL (ES4 regs1) s4_ssN
    (restrict (w_H (si_W X)) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_P4))) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hlt.
pose proof HS4 as (HM & (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427) & R19 & R16 & R17 & R14 & R11 & R15 & HD & Hrec).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hmd & _).
pose proof (s4_lsd_bnd X) as Hl.
destruct (s4_geom X pos lyc1 Sc1 memc1 mdc1 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ES4 regs1) n = getr regs1 r)
  by (intros n r Hn; unfold ES4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EF : bv_unsigned (ew (ES4 regs1) 14) = sbd_F X pos + 32)
  by (rewrite (EE 14%nat 14%bv eq_refl), R14; unfold w64; apply unsigned_lit_small; lia).
unfold s4_ssN, s4_rrN. apply pa_entry_st_ok_full.
- unfold ES4. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite EF. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HFpres. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I|]. split; [|exact I]. split; [|exact I].
  unfold acond_ok. cbn [ac_c ac_a ac_b].
  apply (s4_c_ltu _ 11%nat 19%nat (Z.of_nat (length (sbm_lsd X))) (si_md X)).
  + rewrite (EE 11%nat 11%bv eq_refl). exact R11.
  + rewrite (EE 19%nat 19%bv eq_refl). exact R19.
  + lia.
  + lia.
  + exact Hlt.
Qed.
Lemma s4_bv24 : Z_to_bv 5 24 = (24%bv : bv 5) /\ Z_to_bv 5 25 = (25%bv : bv 5) /\
  Z_to_bv 5 26 = (26%bv : bv 5) /\ Z_to_bv 5 27 = (27%bv : bv 5).
Proof.
split; [|split; [|split]]; apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma s4_runT : forall X pos regs1 lyc1 Sc1 memc1 mdc1,
  sbd_cx B X -> sbd_st4 B X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  si_md X <= Z.of_nat (length (sbm_lsd X)) ->
  SRr SEGS (si_W X) (sbd_cfg X SBD_P4 regs1 memc1 mdc1) (s4_atL2 X pos lyc1 Sc1 memc1).
Proof.
intros X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hge.
pose proof HS4 as (HM & HBase & R19 & R16 & R17 & R14 & R11 & R15 & HD & Hrec).
pose proof HBase as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
destruct (s4_geom X pos lyc1 Sc1 memc1 mdc1 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
destruct (s4_A_band X HX) as (HA4096 & HA47 & HAband).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hmd & HA8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s4_lsd_bnd X) as Hl.
destruct s4_bv24 as (B24 & B25 & B26 & B27).
assert (Hdiv : forall d, 0 <= d <= 24 -> 0 <= (si_A X + d) / 8 < 2 ^ 45).
{ intros d Hd. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (HA24 : (si_A X + 24) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
assert (Hbf : (Z.of_nat (length (sb_dec_c.sb_dec_lsd (si_v X) 3)) <? si_md X) = false)
  by (apply Z.ltb_ge; exact Hge).
assert (Hbuf : s4_buf (si_v X) (si_md X) = sbm_lsd X)
  by (unfold s4_buf, sbm_lsd; cbv zeta; rewrite Hbf; reflexivity).
pose proof (s4_entryT (si_fq X) X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hge) as HS.
pose proof (@SRr_run_to_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
remember (ES4 regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ES4; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ES4; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (EA : ew E 18 = Z_to_bv 64 (si_A X)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (EF : ew E 14 = Z_to_bv 64 (sbd_F X pos + 32)) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (ELn : ew E 15 = Z_to_bv 64 (Z.of_nat (length (sbm_lsd X))))
  by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (EO : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
unfold sbd_cfg, cfg_at, w64.
replace (BASE + AF_sb_dec + SBD_P4) with (BASE + (AF_sb_dec + SBD_P4)) by lia.
paj_run_to_sh RUNTOP HS HJ1 (AF_sb_dec + SBD_L2).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_nil. }
assert (Hfr0 : forall x : word, ~ s4_wz X pos (bv_unsigned x) ->
  mrestrict (w_H (si_W X)) (ms_mem ms) x = mrestrict (w_H (si_W X)) memc1 x).
{ intros x _. apply HFr. intros (r & Hin & _). unfold s4_ssT in Hin. cbn [ss_mem In] in Hin. destruct Hin. }
assert (KW0 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H (si_W X)) (ms_mem ms) a = aview SEGS (w_H (si_W X)) memc1 a).
{ intros a Ha. apply aview_eq_of. apply HFr. intros (r & Hin & _).
  unfold s4_ssT in Hin. cbn [ss_mem In] in Hin. destruct Hin. }
destruct (s4_mid_write X pos lyc1 Sc1 memc1 mdc1 (ms_mem ms) _ sbd_sh_hdr HX HM
  ltac:(unfold sbd_sh_hdr; cbn [length]; lia) HJ1 Hfr0 HG) as (HM2 & KW).
assert (HD2 : garr8 SEGS (mrestrict (w_H (si_W X)) (ms_mem ms)) (sbd_F X pos + 32) (s4_buf (si_v X) (si_md X))).
{ rewrite Hbuf. apply (garr8_frame SEGS (mrestrict (w_H (si_W X)) memc1)); [exact HD|].
  intros a Ha. apply (mbyte_of_aview SEGS). apply KW0. lia. }
apply SRr_ret. pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (5%bv : bv 5) Q5. prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (14%bv : bv 5) Q14. prreg HS (16%bv : bv 5) Q16. prreg HS (17%bv : bv 5) Q17.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
prreg HS (30%bv : bv 5) Q30. prreg HS (31%bv : bv 5) Q31.
assert (UA : bv_unsigned (ew E 18) = si_A X) by (rewrite EA; apply unsigned_lit_small; lia).
assert (UF : bv_unsigned (ew E 14) = sbd_F X pos + 32) by (rewrite EF; apply unsigned_lit_small; lia).
assert (UL : bv_unsigned (ew E 15) = Z.of_nat (length (sbm_lsd X)))
  by (rewrite ELn; apply unsigned_lit_small; lia).
assert (UO : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite EO; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc1) mat mdc1).
split.
{ unfold sbd_cfg, cfg_at, w64.
  replace (BASE + AF_sb_dec + SBD_L2) with (BASE + 17132) by (unfold AF_sb_dec, SBD_L2; lia). reflexivity. }
split; [exact HJ1|]. split; [exact HM2|]. split; [exact KW|]. split; [exact HD2|].
split.
{ destruct Hrec as (V0 & V8 & V16 & V24). unfold sbd_rec. split; [|split; [|split]].
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V0].
    intros k Hk. apply KW0. lia.
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V8].
    intros k Hk. apply KW0. lia.
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V16].
    intros k Hk. apply KW0. lia.
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V24].
    intros k Hk. apply KW0. lia. }
unfold s4_regs2, sbd_base. rewrite Hbuf.
split.
{ split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); exact R2|].
  split; [rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite Q8, (EE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite Q9, (EE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite Q18, (EE 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite Q21, (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite Q10, (EE 10%nat 10%bv eq_refl); exact R10|].
  intros r Hr. rewrite <- (R2427 r Hr).
  assert (Hc : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - rewrite B24, Q24. apply (EE 24%nat 24%bv eq_refl).
  - rewrite B25, Q25. apply (EE 25%nat 25%bv eq_refl).
  - rewrite B26, Q26. apply (EE 26%nat 26%bv eq_refl).
  - rewrite B27, Q27. apply (EE 27%nat 27%bv eq_refl). }
split; [rewrite Q16, (EE 16%nat 16%bv eq_refl); exact R16|].
split; [rewrite Q17, (EE 17%nat 17%bv eq_refl); exact R17|].
split; [rewrite Q11, UA; reflexivity|].
split; [rewrite Q12, UA; reflexivity|].
split; [rewrite Q13, UA; reflexivity|].
split; [rewrite Q5, (s4_sub0 (ew E 15) _ UL); reflexivity|].
split.
{ rewrite Q14, UF, (s4_add (Z_to_bv 64 (sbd_F X pos + 32 + -1)) (ew E 15) (sbd_F X pos + 32 + -1)
    (Z.of_nat (length (sbm_lsd X))) (unsigned_lit_small (sbd_F X pos + 32 + -1) ltac:(lia)) UL).
  unfold w64. f_equal. lia. }
split.
{ rewrite Q6, UF, (s4_add (Z_to_bv 64 (sbd_F X pos + 32 + -1)) (ew E 15) (sbd_F X pos + 32 + -1)
    (Z.of_nat (length (sbm_lsd X))) (unsigned_lit_small (sbd_F X pos + 32 + -1) ltac:(lia)) UL).
  unfold w64. f_equal. lia. }
split.
{ rewrite Q7, (s4_shadow0 (ew E 18) (ew E 21) (si_A X) SHADOW_OFF UA UO
    ltac:(pose proof (Hdiv 0 ltac:(lia)); rewrite Z.add_0_r in *; unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q28, UA, (s4_shadow0 (Z_to_bv 64 (si_A X + 16)) (ew E 21) (si_A X + 16) SHADOW_OFF
    (unsigned_lit_small (si_A X + 16) ltac:(lia)) UO
    ltac:(pose proof (Hdiv 16 ltac:(lia)); unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q29, UA, (s4_shadow0 (Z_to_bv 64 (si_A X + 8)) (ew E 21) (si_A X + 8) SHADOW_OFF
    (unsigned_lit_small (si_A X + 8) ltac:(lia)) UO
    ltac:(pose proof (Hdiv 8 ltac:(lia)); unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q30, UA, (s4_shadow0 (Z_to_bv 64 (si_A X + 24)) (ew E 21) (si_A X + 24) SHADOW_OFF
    (unsigned_lit_small (si_A X + 24) ltac:(lia)) UO
    ltac:(pose proof (Hdiv 24 ltac:(lia)); unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q31, UA, (s4_and7 (Z_to_bv 64 (si_A X + 24)) (si_A X + 24)
    (unsigned_lit_small (si_A X + 24) ltac:(lia)) HA24),
    (s4_add (Z_to_bv 64 0) (Z_to_bv 64 3) 0 3 (unsigned_lit_small 0 ltac:(lia))
       (unsigned_lit_small 3 ltac:(lia))).
  unfold w64. f_equal; lia. }
rewrite Q19. reflexivity.
Qed.
Lemma s4_runN : forall X pos regs1 lyc1 Sc1 memc1 mdc1,
  sbd_cx B X -> sbd_st4 B X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  Z.of_nat (length (sbm_lsd X)) < si_md X ->
  SRr SEGS (si_W X) (sbd_cfg X SBD_P4 regs1 memc1 mdc1) (s4_atL2 X pos lyc1 Sc1 memc1).
Proof.
intros X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hlt.
pose proof HS4 as (HM & HBase & R19 & R16 & R17 & R14 & R11 & R15 & HD & Hrec).
pose proof HBase as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
destruct (s4_geom X pos lyc1 Sc1 memc1 mdc1 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
destruct (s4_A_band X HX) as (HA4096 & HA47 & HAband).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hmd & HA8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s4_lsd_bnd X) as Hl.
destruct s4_bv24 as (B24 & B25 & B26 & B27).
assert (Hdiv : forall d, 0 <= d <= 24 -> 0 <= (si_A X + d) / 8 < 2 ^ 45).
{ intros d Hd. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (HA24 : (si_A X + 24) mod 8 = 0) by (rewrite Zplus_mod, HA8; reflexivity).
assert (HlenL : length (sbm_lsd X) = 1%nat) by lia.
assert (Hbt : (Z.of_nat (length (sb_dec_c.sb_dec_lsd (si_v X) 3)) <? si_md X) = true)
  by (apply Z.ltb_lt; exact Hlt).
assert (Hbuf : s4_buf (si_v X) (si_md X) = sbm_lsd X ++ [48])
  by (unfold s4_buf, sbm_lsd; cbv zeta; rewrite Hbt; reflexivity).
assert (HlenB : length (s4_buf (si_v X) (si_md X)) = 2%nat)
  by (rewrite Hbuf, length_app, HlenL; reflexivity).
pose proof (s4_entryN (si_fq X) X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hlt) as HS.
pose proof (@SRr_run_to_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
remember (ES4 regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ES4; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ES4; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (EA : ew E 18 = Z_to_bv 64 (si_A X)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (EF : ew E 14 = Z_to_bv 64 (sbd_F X pos + 32)) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (EO : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (UF : bv_unsigned (ew E 14) = sbd_F X pos + 32) by (rewrite EF; apply unsigned_lit_small; lia).
unfold sbd_cfg, cfg_at, w64.
replace (BASE + AF_sb_dec + SBD_P4) with (BASE + (AF_sb_dec + SBD_P4)) by lia.
paj_run_to_sh RUNTOP HS HJ1 (AF_sb_dec + SBD_L2).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 14%nat (sbd_F X pos + 32));
    [reflexivity | exact UF | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists 0, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite (HFeq 0 pos). change (fs_frame_bytes 0) with 64.
  fold (sbd_F X pos). lia. }
assert (Hfr0 : forall x : word, ~ s4_wz X pos (bv_unsigned x) ->
  mrestrict (w_H (si_W X)) (ms_mem ms) x = mrestrict (w_H (si_W X)) memc1 x).
{ intros x Hx. apply HFr. intros (r & Hin & Hw).
  unfold s4_ssN, s4_rrN in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite UF in Hw.
  apply Hx. unfold s4_wz. lia. }
destruct (s4_mid_write X pos lyc1 Sc1 memc1 mdc1 (ms_mem ms) _ sbd_sh_hdr HX HM
  ltac:(unfold sbd_sh_hdr; cbn [length]; lia) HJ1 Hfr0 HG) as (HM2 & KW).
pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
assert (V48 : val_mem SEGS (mrestrict (w_H (si_W X)) (ms_mem ms)) (sbd_F X pos + 32 + 1) 1 48).
{ apply (field_of_region E _ 14 (sbd_F X pos + 32) _ 1 2 1 2 1 1 (SLit 48) 48 RF);
    [ exact UF | left; reflexivity | apply s4_denot_lit; reflexivity | cbn; lia | cbn; lia]. }
assert (HD2 : garr8 SEGS (mrestrict (w_H (si_W X)) (ms_mem ms)) (sbd_F X pos + 32) (s4_buf (si_v X) (si_md X))).
{ rewrite Hbuf.
  apply (garr8_app1 SEGS (mrestrict (w_H (si_W X)) memc1) (mrestrict (w_H (si_W X)) (ms_mem ms))
    (sbd_F X pos + 32) (sbm_lsd X) 48 HD).
  - rewrite HlenL. change (Z.of_nat 1) with 1. exact V48.
  - lia.
  - intros a Ha. rewrite HlenL in Ha. change (Z.of_nat 1) with 1 in Ha.
    apply (mbyte_of_aview SEGS). apply KW; [lia | unfold s4_wz; lia]. }
apply SRr_ret. pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (5%bv : bv 5) Q5. prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (14%bv : bv 5) Q14. prreg HS (16%bv : bv 5) Q16. prreg HS (17%bv : bv 5) Q17.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
prreg HS (30%bv : bv 5) Q30. prreg HS (31%bv : bv 5) Q31.
assert (UA : bv_unsigned (ew E 18) = si_A X) by (rewrite EA; apply unsigned_lit_small; lia).
assert (UO : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite EO; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc1) mat mdc1).
split.
{ unfold sbd_cfg, cfg_at, w64.
  replace (BASE + AF_sb_dec + SBD_L2) with (BASE + 17132) by (unfold AF_sb_dec, SBD_L2; lia). reflexivity. }
split; [exact HJ1|]. split; [exact HM2|]. split; [exact KW|]. split; [exact HD2|].
split.
{ destruct Hrec as (V0 & V8 & V16 & V24). unfold sbd_rec. split; [|split; [|split]].
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V0].
    intros k Hk. apply KW; [lia | apply (s4_rec_nwz X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr _ HX HM); lia].
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V8].
    intros k Hk. apply KW; [lia | apply (s4_rec_nwz X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr _ HX HM); lia].
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V16].
    intros k Hk. apply KW; [lia | apply (s4_rec_nwz X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr _ HX HM); lia].
  - apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [|exact V24].
    intros k Hk. apply KW; [lia | apply (s4_rec_nwz X pos lyc1 Sc1 memc1 mdc1 sbd_sh_hdr _ HX HM); lia]. }
unfold s4_regs2, sbd_base. rewrite HlenB.
split.
{ split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); exact R2|].
  split; [rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite Q8, (EE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite Q9, (EE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite Q18, (EE 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite Q21, (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite Q10, (EE 10%nat 10%bv eq_refl); exact R10|].
  intros r Hr. rewrite <- (R2427 r Hr).
  assert (Hc : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - rewrite B24, Q24. apply (EE 24%nat 24%bv eq_refl).
  - rewrite B25, Q25. apply (EE 25%nat 25%bv eq_refl).
  - rewrite B26, Q26. apply (EE 26%nat 26%bv eq_refl).
  - rewrite B27, Q27. apply (EE 27%nat 27%bv eq_refl). }
split; [rewrite Q16, (EE 16%nat 16%bv eq_refl); exact R16|].
split; [rewrite Q17, (EE 17%nat 17%bv eq_refl); exact R17|].
split; [rewrite Q11, UA; reflexivity|].
split; [rewrite Q12, UA; reflexivity|].
split; [rewrite Q13, UA; reflexivity|].
split.
{ rewrite Q5. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
split.
{ rewrite Q14, UF. unfold w64. f_equal. lia. }
split.
{ rewrite Q6, UF. unfold w64. f_equal. lia. }
split.
{ rewrite Q7, (s4_shadow0 (ew E 18) (ew E 21) (si_A X) SHADOW_OFF UA UO
    ltac:(pose proof (Hdiv 0 ltac:(lia)); rewrite Z.add_0_r in *; unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q28, UA, (s4_shadow0 (Z_to_bv 64 (si_A X + 16)) (ew E 21) (si_A X + 16) SHADOW_OFF
    (unsigned_lit_small (si_A X + 16) ltac:(lia)) UO
    ltac:(pose proof (Hdiv 16 ltac:(lia)); unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q29, UA, (s4_shadow0 (Z_to_bv 64 (si_A X + 8)) (ew E 21) (si_A X + 8) SHADOW_OFF
    (unsigned_lit_small (si_A X + 8) ltac:(lia)) UO
    ltac:(pose proof (Hdiv 8 ltac:(lia)); unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q30, UA, (s4_shadow0 (Z_to_bv 64 (si_A X + 24)) (ew E 21) (si_A X + 24) SHADOW_OFF
    (unsigned_lit_small (si_A X + 24) ltac:(lia)) UO
    ltac:(pose proof (Hdiv 24 ltac:(lia)); unfold SHADOW_OFF; lia)). reflexivity. }
split.
{ rewrite Q31, UA, (s4_and7 (Z_to_bv 64 (si_A X + 24)) (si_A X + 24)
    (unsigned_lit_small (si_A X + 24) ltac:(lia)) HA24),
    (s4_add (Z_to_bv 64 0) (Z_to_bv 64 3) 0 3 (unsigned_lit_small 0 ltac:(lia))
       (unsigned_lit_small 3 ltac:(lia))).
  unfold w64. f_equal; lia. }
rewrite Q19. reflexivity.
Qed.
Lemma s4_ra_at : forall X pos lyc1 Sc1 mem2 md2 lo n,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 mem2 md2 sbd_sh_hdr ->
  (forall a, lo <= a < lo + n -> awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
     (ablocks B (si_lyc X) (si_Sc X)) (si_lyc X) (si_own X) a) ->
  (forall a, lo <= a < lo + n -> a < kLowShadowBeg \/ kHighMemBeg <= a) ->
  (forall a, lo <= a < lo + n ->
     ~ sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) (shadow_of_addr SHADOW_OFF a)) ->
  range_addressable (aview SEGS (w_H (si_W X)) (si_memc X)) SHADOW_OFF lo n ->
  range_addressable (aview SEGS (w_H (si_W X)) mem2) SHADOW_OFF lo n.
Proof.
intros X pos lyc1 Sc1 mem2 md2 lo n HX HM Hawr Hband HnE HRA x Hx.
pose proof HX as (HJX & _).
pose proof HJX as (HARX & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & _).
pose proof HJ1 as (HAR2 & Hly1 & _).
destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
refine (s4_addr_cur (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
  (si_W X) (si_memc X) (si_mdc X) lyc1 Sc1 mem2 md2 _ _ _ x
  Hfrs Hstk Elo Ehi HARX HAR2 Eab1 HK1 (HnE x Hx) (Hband x Hx) (Hawr x Hx)
  ltac:(apply (range_addressable_sub _ _ lo n x 1 HRA); lia) x ltac:(lia)).
Qed.
Lemma s4_ra_buf : forall X pos lyc1 Sc1 mem2 md2 n,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 mem2 md2 sbd_sh_hdr -> 0 <= n <= 3 ->
  range_addressable (aview SEGS (w_H (si_W X)) mem2) SHADOW_OFF (sbd_F X pos + 32) n.
Proof.
intros X pos lyc1 Sc1 mem2 md2 n HX HM Hn x Hx.
destruct (s4_geom X pos lyc1 Sc1 mem2 md2 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & HSh1).
assert (HF8 : sbd_F X pos = 8 * (sbd_F X pos / 8)) by (apply div8_64; lia).
exists 4. split.
- unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (sbd_SH X pos + 4) by (rewrite HSH; lia).
  rewrite (HSh1 4 ltac:(unfold sbd_sh_hdr; cbn [length]; lia)). reflexivity.
- unfold saddr_ok. right. split; [|lia].
  assert (HM8 : sbd_F X pos mod 8 = 0) by lia. lia.
Qed.
Lemma s4_er_out : forall X pos lyc1 Sc1 mem2 md2 a,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 mem2 md2 sbd_sh_hdr ->
  (sbd_F X pos <= a < sbd_F X pos + 64 \/ sbd_SH X pos <= a < sbd_SH X pos + 8 \/
   sbd_SP X - 112 <= a < sbd_SP X) ->
  ~ sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) a.
Proof.
intros X pos lyc1 Sc1 mem2 md2 a HX HM Ha.
destruct (s4_geom X pos lyc1 Sc1 mem2 md2 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAsp &
  _ & _ & _ & _ & _ & _ & _ & _ & HAwr & Hroom).
pose proof HJX as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & _).
pose proof (proj1 HJ1) as HAR1.
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (HSPdef : sbd_SP X = spZ (si_regs X)) by reflexivity.
intros HEr. unfold sbd_Er in HEr. destruct HEr as [HEr | (Hrm & HEr)].
- destruct (s4_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
    lyc1 Sc1 (si_W X) mem2 md2 0 pos a Hfrs Hc0 HAR1 Hfrs1 Eab1 HFeq ltac:(lia)
    (HAwr a ltac:(lia))) as [N1 N2].
  change (fs_frame_bytes 0) with 64 in N1. change (fs_frame_bytes 0 / 8) with 8 in N2.
  fold (sbd_F X pos) in N1, N2. fold (sbd_SH X pos) in N2. lia.
- destruct (Hroom Hrm) as (_ & Hin & _ & _ & Hsp2 & _ & Hwb). unfold sbm_acc, sbm_room in Hsp2.
  destruct (s4_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
    lyc1 Sc1 (si_W X) mem2 md2 0 pos a Hfrs Hc0 HAR1 Hfrs1 Eab1 HFeq ltac:(lia)
    (proj1 (Hwb a HEr))) as [N1 N2].
  change (fs_frame_bytes 0) with 64 in N1. change (fs_frame_bytes 0 / 8) with 8 in N2.
  fold (sbd_F X pos) in N1, N2. fold (sbd_SH X pos) in N2. lia.
Qed.
Lemma s4_mid_er : forall X pos lyc1 Sc1 mem2 md2 mem3 md3,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 mem2 md2 sbd_sh_hdr ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) mem3 md3 (si_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) a ->
     aview SEGS (w_H (si_W X)) mem3 a = aview SEGS (w_H (si_W X)) mem2 a) ->
  (forall a, apresent (w_H (si_W X)) mem2 a -> apresent (w_H (si_W X)) mem3 a) ->
  sbd_mid B X pos lyc1 Sc1 mem3 md3 sbd_sh_hdr.
Proof.
intros X pos lyc1 Sc1 mem2 md2 mem3 md3 HX HM HJ3 HEQ HPres.
destruct (s4_geom X pos lyc1 Sc1 mem2 md2 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAimg & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom).
pose proof (proj1 HJX) as HARX.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (HSPdef : sbd_SP X = spZ (si_regs X)) by reflexivity.
assert (HEo : forall a, sbd_F X pos <= a < sbd_F X pos + 64 \/ sbd_SH X pos <= a < sbd_SH X pos + 8 \/
  sbd_SP X - 112 <= a < sbd_SP X ->
  aview SEGS (w_H (si_W X)) mem3 a = aview SEGS (w_H (si_W X)) mem2 a).
{ intros a Ha. apply HEQ; [unfold SHADOW_OFF in *; lia|].
  exact (s4_er_out X pos lyc1 Sc1 mem2 md2 a HX HM Ha). }
split; [exact HJ3|]. split; [exact Hfrs1|]. split; [exact Eab1|]. split; [exact HFeq|]. split; [exact HFLeq|].
split.
{ destruct HK1 as (K1 & K2 & K3 & K4 & K5 & K6). unfold sbd_kept_at, sbd_kept.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hs He. rewrite (HEQ a ltac:(lia) He). exact (K1 a Ha Hs He).
  - intros b m i Hb Hi He.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARX Hb) as (_ & Hb4096 & Hbc & _).
    rewrite (HEQ (b + i) ltac:(lia) He). exact (K2 b m i Hb Hi He).
  - intros a Hia Ho Herr.
    pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite (HEQ a ltac:(lia)).
    + exact (K3 a Hia Ho Herr).
    + intros HEr. unfold sbd_Er in HEr. pose proof (pa_img_range a Hia) as Hir.
      destruct HEr as [HEr | (Hrm & HEr)].
      * unfold boxed, IMG_LO, IMG_TOP in *. lia.
      * destruct (Hroom Hrm) as (_ & _ & Himg2 & _).
        unfold boxed, IMG_LO, IMG_TOP, sbm_acc in *. lia.
  - intros cid p a Hcp Hr He.
    assert (Hin1 : In (cid, p) (frames (si_Sc X))) by exact Hcp.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HARX Hin1) as (HG4096 & HGc & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct (shadow_cell_bound (frame_addr (si_lyc X) cid p) (fs_frame_bytes cid) ltac:(lia) Hcnn ltac:(lia))
      as [T1 T2].
    assert (Hab : 0 <= a < 2 ^ 64).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr;
      unfold SHADOW_OFF, kHighMemBeg in *; lia. }
    rewrite (HEQ a Hab He). exact (K4 cid p a Hcp Hr He).
  - intros a Ha Hs Hp. apply HPres. exact (K5 a Ha Hs Hp).
  - intros a Ha. apply HPres. exact (K6 a Ha). }
split.
{ intros j r Hj.
  assert (Hjr : (j < 9)%nat)
    by (apply (proj1 (nth_error_Some sbd_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) mem2 mem3); [|exact (HFr1 j r Hj)].
  intros k Hk. apply HEo. right; right. unfold sbd_SP in *. lia. }
split.
{ apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) mem2 mem3); [|exact HFL1].
  intros k Hk. apply HEo. left. lia. }
intros j Hj. rewrite (HEo (sbd_SH X pos + j) ltac:(right; left; unfold sbd_sh_hdr in Hj; cbn [length] in Hj; lia)).
exact (HSh1 j Hj).
Qed.
Lemma s4_shadow_not_er : forall X a, sbd_cx B X -> 4096 <= a -> a < 2 ^ 47 ->
  ~ sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) (shadow_of_addr SHADOW_OFF a).
Proof.
intros X a HX Ha1 Ha2.
destruct (s4_A_band X HX) as (HA4096 & HA47 & HAband).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EL : kLowShadowBeg = 2147446784) by reflexivity.
assert (ES : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hd1 : 512 <= a / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hd2 : a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold shadow_of_addr. intros HEr. unfold sbd_Er in HEr. destruct HEr as [HEr | (Hrm & HEr)].
- lia.
- destruct (Hroom Hrm) as (_ & Hin & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hin. unfold sbm_acc in Hin. lia.
Qed.
Hypothesis L2F : sbd_L2_spec B.
Lemma s4_fromL2 : forall X pos lyc1 Sc1 memc1 W3 c3,
  sbd_cx B X -> s4_atL2 X pos lyc1 Sc1 memc1 W3 c3 -> SRr SEGS W3 c3 (sbd_at5 B X).
Proof.
intros X pos lyc1 Sc1 memc1 W3 c3 HX (-> & regs2 & mem2 & md2 & -> & HJ2 & HM2 & KW & HD2 & HR2 & HRg).
destruct (s4_geom X pos lyc1 Sc1 mem2 md2 _ HX HM2) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
destruct (s4_A_band X HX) as (HA4096 & HA47 & HAband).
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & Hmd & HA8 & HAapp & HA63 &
  HAimg & HAsp & Rp & Rcap & Rn0 & Rn1 & Rover & Hrec0 & HRA & HApres & HAwr & Hroom).
pose proof (proj1 HJX) as HARX.
pose proof HJX as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HM2 as (HJ1' & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct s4_bv24 as (B24 & B25 & B26 & B27).
rs_hide_all. apply rs_hide in Hroom.
assert (EL : kLowShadowBeg = 2147446784) by reflexivity.
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (Hlb : (1 <= length (s4_buf (si_v X) (si_md X)) <= 3)%nat) by (apply s4_buf_len; exact Hmd).
assert (HDlen : length (sbm_D X) = length (s4_buf (si_v X) (si_md X))) by apply s4_D_len.
assert (HDrev : sbm_D X = rev (s4_buf (si_v X) (si_md X))) by apply s4_D_rev.
assert (Hacc : sb_dec_c.sb_dec_acc (si_v X) (si_md X) (si_cap X) (si_n X) =
  Z.min (Z.of_nat (length (s4_buf (si_v X) (si_md X)))) (sb_dec_c.sb_dec_room (si_cap X) (si_n X))).
{ unfold sb_dec_c.sb_dec_acc. unfold sbm_D in HDlen. rewrite HDlen. reflexivity. }
assert (Hch : Forall (fun c => 0 <= c < 256) (s4_buf (si_v X) (si_md X)))
  by (apply (garr8_bytes_ok SEGS _ _ _ HD2)).
assert (Hpres2 : forall a, awr_byte (si_STK X) (si_sp0 X) (si_FP X) (ablocks B (si_ly X) (si_S X))
    (ablocks B (si_lyc X) (si_Sc X)) (si_lyc X) (si_own X) a -> apresent (w_H (si_W X)) mem2 a)
  by (intros a Haw; exact (s4_awr_pres X pos lyc1 Sc1 mem2 md2 a HX Hfrs1 Eab1 HFeq HJ2 Haw)).
assert (HdA : si_A X + 28 <= sbd_F X pos + 32 \/
  sbd_F X pos + 32 + Z.of_nat (length (s4_buf (si_v X) (si_md X))) <= si_A X).
{ apply (range_disj_of_pt (si_A X) 28 (sbd_F X pos + 32)
    (Z.of_nat (length (s4_buf (si_v X) (si_md X))))); [|lia|lia].
  intros a Ha.
  destruct (s4_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
    lyc1 Sc1 (si_W X) mem2 md2 0 pos a Hfrs Hc0 (proj1 HJ1') Hfrs1 Eab1 HFeq ltac:(lia)
    (HAwr a Ha)) as [N1 _].
  change (fs_frame_bytes 0) with 64 in N1. fold (sbd_F X pos) in N1. lia. }
assert (HdP : 0 < sb_dec_c.sb_dec_room (si_cap X) (si_n X) ->
  si_p X + si_n X + Z.min (Z.of_nat (length (s4_buf (si_v X) (si_md X))))
    (sb_dec_c.sb_dec_room (si_cap X) (si_n X)) <= sbd_F X pos + 32 \/
  sbd_F X pos + 32 + Z.of_nat (length (s4_buf (si_v X) (si_md X))) <= si_p X + si_n X).
{ intros Hrm. destruct (Hroom Hrm) as (_ & _ & _ & _ & _ & _ & Hwb).
  apply (range_disj_of_pt (si_p X + si_n X)
    (Z.min (Z.of_nat (length (s4_buf (si_v X) (si_md X)))) (sb_dec_c.sb_dec_room (si_cap X) (si_n X)))
    (sbd_F X pos + 32) (Z.of_nat (length (s4_buf (si_v X) (si_md X))))); [|lia|lia].
  intros a Ha.
  destruct (s4_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
    lyc1 Sc1 (si_W X) mem2 md2 0 pos a Hfrs Hc0 (proj1 HJ1') Hfrs1 Eab1 HFeq ltac:(lia)
    (proj1 (Hwb a ltac:(unfold sbm_acc; rewrite Hacc in *; lia)))) as [N1 _].
  change (fs_frame_bytes 0) with 64 in N1. fold (sbd_F X pos) in N1. lia. }
pose proof HRg as ((P2 & P3 & P4 & P8 & P9 & P18 & P21 & P10 & P2427) & P16 & P17 & P11 & P12 & P13 & P5 &
  P14 & P6 & P7 & P28 & P29 & P30 & P31 & P19).
destruct HR2 as (V0 & V8 & V16 & V24).
rs_hide_all. apply rs_hide in HdP.
eapply SRr_bind.
{ apply (L2F (si_fq X) (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) mem2 md2 (si_k X) regs2
    (si_A X) (si_p X) (si_cap X) (si_n X) (si_over X) (sbd_F X pos + 32) (s4_buf (si_v X) (si_md X))).
  - exact HJ2.
  - exact HA8.
  - exact HA4096.
  - exact HA47.
  - unfold rs_hold in HAband. lia.
  - exact Rp.
  - exact Rcap.
  - exact Rn0.
  - exact Rn1.
  - exact Rover.
  - exact V0.
  - exact V8.
  - exact V16.
  - exact V24.
  - apply (s4_ra_at X pos lyc1 Sc1 mem2 md2 (si_A X) 28 HX HM2).
    + intros a Ha. exact (HAwr a Ha).
    + intros a Ha. unfold rs_hold in HAband. lia.
    + intros a Ha. apply (s4_shadow_not_er X a HX); lia.
    + exact HRA.
  - intros a Ha. split;
    [exact (s4_awr_up X pos lyc1 Sc1 a Eab1 HFeq (HAwr a ltac:(lia)))
    | exact (Hpres2 a (HAwr a ltac:(lia)))].
  - exact Hlb.
  - exact Hch.
  - exact HD2.
  - lia.
  - lia.
  - apply (s4_ra_buf X pos lyc1 Sc1 mem2 md2 _ HX HM2). lia.
  - exact HdA.
  - intros Hrm. destruct (Hroom Hrm) as (Hpc & Hin & Himg2 & HdA2 & Hsp2 & HRAp & Hwb).
    unfold sbm_acc in Hin, HdA2, Hsp2, HRAp, Hwb. rewrite Hacc in Hin, HdA2, Hsp2, HRAp, Hwb. rs_hide_all.
    split; [exact Hpc|]. split; [exact Hin|].
    split.
    { apply (s4_ra_at X pos lyc1 Sc1 mem2 md2 (si_p X + si_n X) _ HX HM2).
      - intros a Ha. exact (proj1 (Hwb a Ha)).
      - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hin. lia.
      - intros a Ha. apply (s4_shadow_not_er X a HX);
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hin; lia.
      - exact HRAp. }
    split.
    { intros a Ha. split;
      [exact (s4_awr_up X pos lyc1 Sc1 a Eab1 HFeq (proj1 (Hwb a Ha)))
      | exact (Hpres2 a (proj1 (Hwb a Ha)))]. }
    split; [exact HdA2 | exact (HdP Hrm)].
  - exact P11.
  - exact P12.
  - exact P13.
  - exact P5.
  - exact P14.
  - exact P6.
  - exact P7.
  - exact P28.
  - exact P29.
  - exact P30.
  - exact P31.
  - exact P19.
  - exact P18.
  - exact P21. }
cbv beta. intros W4 c4 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HKr & W16 & W24 & HGar & HEQ & HPres).
apply SRr_ret.
assert (HEQ' : forall a, 0 <= a < 2 ^ 64 ->
  ~ sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X) a ->
  aview SEGS (w_H (si_W X)) mem3 a = aview SEGS (w_H (si_W X)) mem2 a).
{ intros a Ha HnE. apply HEQ; [exact Ha | intros Hc; apply HnE; left; exact Hc |].
  intros (Hrm & Hc). apply HnE. right. split; [exact Hrm | rewrite Hacc; exact Hc]. }
assert (HKg : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [5; 6; 14; 15; 20; 22; 23] = false ->
  getr regs3 r = getr regs2 r) by (intros r Hr; exact (s4_keep regs2 regs3 _ r HKr Hr)).
split; [reflexivity|].
exists pos, regs3, lyc1, Sc1, mem3, md3.
split; [reflexivity|].
split.
{ exact (s4_mid_er X pos lyc1 Sc1 mem2 md2 mem3 md3 HX HM2 HJ3 HEQ' HPres). }
split.
{ split; [rewrite (HKg 2%bv ltac:(reflexivity)); exact P2|].
  split; [rewrite (HKg 3%bv ltac:(reflexivity)); exact P3|].
  split; [rewrite (HKg 4%bv ltac:(reflexivity)); exact P4|].
  split; [rewrite (HKg 8%bv ltac:(reflexivity)); exact P8|].
  split; [rewrite (HKg 9%bv ltac:(reflexivity)); exact P9|].
  split; [rewrite (HKg 18%bv ltac:(reflexivity)); exact P18|].
  split; [rewrite (HKg 21%bv ltac:(reflexivity)); exact P21|].
  split; [rewrite (HKg 10%bv ltac:(reflexivity)); exact P10|].
  intros r Hr. rewrite <- (P2427 r Hr).
  assert (Hc : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - rewrite B24. exact (HKg 24%bv ltac:(reflexivity)).
  - rewrite B25. exact (HKg 25%bv ltac:(reflexivity)).
  - rewrite B26. exact (HKg 26%bv ltac:(reflexivity)).
  - rewrite B27. exact (HKg 27%bv ltac:(reflexivity)). }
split; [rewrite (HKg 16%bv ltac:(reflexivity)); exact P16|].
split; [rewrite (HKg 17%bv ltac:(reflexivity)); exact P17|].
split.
{ unfold sbd_rec. unfold sbm_acc, sbm_over. rewrite Hacc.
  split.
  { apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) mem2 mem3); [|exact V0].
    intros k Hk. apply HEQ'; [lia|]. unfold sbd_Er. intros [Hc | (Hrm & Hc)]; [lia|].
    destruct (Hroom Hrm) as (_ & _ & _ & HdA2 & _). unfold sbm_acc in HdA2. rewrite Hacc in HdA2, Hc. lia. }
  split.
  { apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) mem2 mem3); [|exact V8].
    intros k Hk. apply HEQ'; [lia|]. unfold sbd_Er. intros [Hc | (Hrm & Hc)]; [lia|].
    destruct (Hroom Hrm) as (_ & _ & _ & HdA2 & _). unfold sbm_acc in HdA2. rewrite Hacc in HdA2, Hc. lia. }
  split; [exact W16|].
  unfold sbm_room. rewrite HDlen. exact W24. }
intros Hrm. rewrite HDrev. unfold sbm_acc. rewrite Hacc. exact (HGar Hrm).
Qed.
Theorem sbd_seg4 : sbd_seg4_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4.
destruct (Z_le_gt_dec (si_md X) (Z.of_nat (length (sbm_lsd X)))) as [Hge | Hlt].
- eapply SRr_bind; [exact (s4_runT X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 Hge)|].
  intros W3 c3 _ H3. exact (s4_fromL2 X pos lyc1 Sc1 memc1 W3 c3 HX H3).
- eapply SRr_bind; [exact (s4_runN X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS4 ltac:(lia))|].
  intros W3 c3 _ H3. exact (s4_fromL2 X pos lyc1 Sc1 memc1 W3 c3 HX H3).
Qed.
End h.
End f.
End d.
