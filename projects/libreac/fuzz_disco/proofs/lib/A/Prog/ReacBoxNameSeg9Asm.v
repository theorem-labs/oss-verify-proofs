(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:137-139 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:56-61 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa0.v:172-173. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg9.v, with its module paths, module names and numbers changed; 181 of its 529 lines of code are new or changed and 1539 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
SbDec DiscoRo ReacBoxName ReacBoxNameCut ReacBoxNameLoops ReacBoxNameSeg9.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac r9ar T := lazymatch T with
  | ?a /\ ?b => r9ar a; r9ar b
  | ?a \/ ?b => r9ar a; r9ar b
  | ~ ?a => r9ar a
  | @eq Z _ _ => idtac
  | Z.le _ _ => idtac
  | Z.lt _ _ => idtac
  | Z.ge _ _ => idtac
  | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac
  | le _ _ => idtac
  | lt _ _ => idtac
  | False => idtac
  | True => idtac
  end.
Ltac r9lia :=
  repeat match goal with H : ?T |- _ =>
    lazymatch type of T with Prop => tryif r9ar T then fail else clear H end end;
  lia.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition rbn9_box (P : Prop) : Prop := P.
Ltac r9box H := let T := type of H in change (rbn9_box T) in H.
Lemma rbn9_mb_eq : forall H H' (m m' : word -> option byte) a a',
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rbn9_garr8_move : forall (H H' : word -> bool) (m m' : word -> option byte) p p' L,
  (forall i, 0 <= i < Z.of_nat (length L) -> aview SEGS H' m' (p' + i) = aview SEGS H m (p + i)) ->
  garr8 SEGS (mrestrict H m) p L -> garr8 SEGS (mrestrict H' m') p' L.
Proof.
intros H H' m m' p p' L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. pose proof (Hv k Hk) as Hb.
rewrite (rbn9_mb_eq H H' m m' (p + Z.of_nat j + Z.of_nat k) (p' + Z.of_nat j + Z.of_nat k)); [exact Hb|].
replace (p' + Z.of_nat j + Z.of_nat k) with (p' + (Z.of_nat j + Z.of_nat k)) by lia.
replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia.
apply HE. lia.
Qed.
Lemma rbn9_val1_of_aview : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate].
injection Hv as <-. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
assert (Hle : YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity. }
rewrite Hle, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma rbn9_hull_frame : forall (rd : reader) F x n,
  F mod 8 = 0 -> (forall i, 0 <= i < 64 -> rd (shadow_addr F + i) <> None) ->
  F + 64 <= x -> x + n <= F + 240 -> 0 < n -> shadow_hull_vis rd x n.
Proof.
intros rd F x n HF8 HP Hx Hxn Hn s Hs.
replace s with (shadow_addr F + (s - shadow_addr F)) by lia. apply HP.
unfold shadow_addr in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D0. rewrite HF8, Z.add_0_r in D0.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_app_sh : forall x, app_addr x -> ~ (kLowShadowBeg <= x < kHighMemBeg).
Proof. intros x [_ [H | [H _]]] Hc; lia. Qed.
Lemma rbn9_ra_true : forall W1 (m : word -> option byte) F,
  rbn_shadow_at W1 m (shadow_addr F) (rbn_sh true true true true) -> F mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 64) 24 /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 128) 24 /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 192) 48.
Proof.
intros W1 m F Hs HF8.
assert (L64 : Z.of_nat (length (rbn_sh true true true true)) = 64) by reflexivity.
split; [|split].
- replace (F + 64) with (F + 8 * 8) by lia. replace 24 with (8 * (11 - 8)) by lia.
  apply (rbn9_ra_frame W1 m F _ 8 11 Hs HF8); [lia | lia | rewrite L64; lia |].
  intros j Hj. assert (j = 8 \/ j = 9 \/ j = 10) as Hjj by lia. destruct Hjj as [-> | [-> | ->]]; reflexivity.
- replace (F + 128) with (F + 8 * 16) by lia. replace 24 with (8 * (19 - 16)) by lia.
  apply (rbn9_ra_frame W1 m F _ 16 19 Hs HF8); [lia | lia | rewrite L64; lia |].
  intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as Hjj by lia. destruct Hjj as [-> | [-> | ->]]; reflexivity.
- replace (F + 192) with (F + 8 * 24) by lia. replace 48 with (8 * (30 - 24)) by lia.
  apply (rbn9_ra_frame W1 m F _ 24 30 Hs HF8); [lia | lia | rewrite L64; lia |].
  intros j Hj. assert (j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29) as Hjj by lia.
  destruct Hjj as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.
Lemma rbn9_same3 : forall r0 r1 r2 r3 l0 l1 l2 r,
  rbn9_same r0 r1 l0 -> rbn9_same r1 r2 l1 -> rbn9_same r2 r3 l2 -> In r l0 -> In r l1 -> In r l2 ->
  getr r3 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Proof. intros r0 r1 r2 r3 l0 l1 l2 r S1 S2 S3 I1 I2 I3. rewrite (S3 r I3), (S2 r I2), (S1 r I1). reflexivity. Qed.
Lemma rbn9_same4 : forall r0 r1 r2 r3 r4 l0 l1 l2 l3 r,
  rbn9_same r0 r1 l0 -> rbn9_same r1 r2 l1 -> rbn9_same r2 r3 l2 -> rbn9_same r3 r4 l3 ->
  In r l0 -> In r l1 -> In r l2 -> In r l3 -> getr r4 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Proof.
intros r0 r1 r2 r3 r4 l0 l1 l2 l3 r S1 S2 S3 S4 I1 I2 I3 I4.
rewrite (S4 r I4), (S3 r I3), (S2 r I2), (S1 r I1). reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis L7F : rbn_L7_fits B.
Lemma rbn9_awr_mid : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B (ri_lyc X) (ri_Sc X))
    (ri_lyc X) (ri_own X) a ->
  awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc1 Sc1)
    lyc1 ((3, pos) :: ri_own X) a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a HX HM Hw.
pose proof (rbn9_fa B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM) as FA.
pose proof HM as (_ & _ & Hperm & _).
destruct Hw as [Hs | [(Hf & b & n & Hb & Hab) | [(b & n & Hb & Hn0 & Hab) | (cid & p & Hcp & Hr)]]].
- left; exact Hs.
- right; left. split; [exact Hf|]. exists b, n. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hb) | exact Hab].
- right; right; left. exists b, n. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hb)|].
  split; [exact Hn0 | exact Hab].
- right; right; right. exists cid, p. split; [right; exact Hcp|]. rewrite (FA cid p). exact Hr.
Qed.
Lemma rbn9_buf_lin : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh b n,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X)
    (rbn_SP X) b n -> 0 < n ->
  0 <= b /\ b + n <= 2 ^ 63 /\
  (b + n <= kLowMemEnd - 1 \/ (kHighMemBeg <= b /\ b + n <= kHighMemEnd - 1)) /\
  (rbn_SP X <= b \/ b + n <= rbn_SP X - REAC_BOX_NAME_STK) /\
  (b + n <= rbn_F X pos \/ rbn_F X pos + 512 <= b).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh b n HX HM Hbuf Hn.
pose proof Hbuf as (Hb0 & Hbn & Ham & Hsp & _).
split; [exact Hb0|]. split; [exact Hbn|]. split; [exact Ham|]. split; [exact Hsp|].
destruct (Z_le_gt_dec (b + n) (rbn_F X pos)) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (rbn_F X pos + 512) b) as [H2 | H2]; [right; exact H2|].
exfalso.
destruct (rbn9_buf_byte B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 sh b n (Z.max b (rbn_F X pos)) HX HM Hbuf ltac:(lia))
  as (_ & Hf & _).
apply Hf. lia.
Qed.
Lemma rbn9_cpy_mk : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh (m : word -> option byte) md (Wr : Z -> Prop) b nb n xo,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) ->
  rbn9_kept W1 memc1 m Wr ->
  (forall a, Wr a -> (rbn_F X pos <= a < rbn_F X pos + 512) \/ (alloc_ceiling <= a) \/
     (rbn_SH X pos <= a < rbn_SH X pos + 64)) ->
  rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X)
    (rbn_SP X) b nb ->
  0 < n <= nb -> n < 2 ^ 32 -> 64 <= xo -> xo + n <= 240 ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (rbn_F X pos + xo) n ->
  rbn9_cpy B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 m (rbn_A X) b
    (rbn_F X pos + xo) n.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh m md Wr b nb n xo HX HM HJm KP HWr Hbuf Hn Hn32 Hxo Hxn HRA.
pose proof Hbuf as (_ & _ & _ & _ & _ & _ & Hw).
destruct (rbn9_buf_lin X pos lyc1 Sc1 W1 memc1 mdc1 sh b nb HX HM Hbuf ltac:(lia)) as (Hb0 & Hbn & Ham & Hsp & HbF).
destruct (rbn9_buf_shadow B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 sh m md Wr b nb n HX HM HJm KP HWr Hbuf Hn) as [RAd HVd].
destruct (rbn9_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
destruct (rbn9_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ m md HX HM HJm)
  as (HF4096 & HFceil & HF32 & HFapp & HFpr & HSpr).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split.
  - apply (rbn9_awr_mid X pos lyc1 Sc1 W1 memc1 mdc1 _ _ a HX HM). exact (proj1 (Hw a ltac:(lia))).
  - lia. }
split; [unfold amem_range; lia|].
split; [exact RAd|].
split; [intros _; exact HVd|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [exact (aview_some_of_apresent SEGS _ _ _ (proj1 (HFpr a ltac:(lia))))|]. lia. }
split; [lia|].
split; [exact (amem_range_sub_app (rbn_F X pos) 512 (rbn_F X pos + xo) n HFapp HFceil ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact HRA|].
intros Hn0. apply (rbn9_hull_frame _ (rbn_F X pos)); [exact HF8 | | lia | lia | exact Hn0].
intros i Hi. exact (aview_some_of_apresent SEGS _ _ _ (HSpr i Hi)).
Qed.
Lemma rbn_seg9 : rbn_seg9_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX Hst.
destruct (rbn9_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hst as (HM & (H2 & H3 & H4 & H8 & H9 & H19 & H22) & H18 & H27 & H24 & H25 & H20 & H26 & H21 & HC &
  G64 & G128 & G192 & HA).
pose proof HM as (HJ1 & _ & _ & _ & _ & _ & _ & Hsh).
pose proof (rbn9_fa B X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM 3 pos) as FA.
change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos) in FA.
destruct (rbn9_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ memc1 mdc1 HX HM HJ1)
  as (HF4096 & HFceil & HF32 & HFapp & _ & _).
unfold rbn_locs6, rbn_locs4, rbn_rec2 in HC. cbn [rbn_cells app] in HC.
destruct HC as (C8 & C16 & C32 & C56 & C64 & C80 & C88 & C152 & C160 & C168 & C176 & C24 & C48 & C72 & C120 & C128 &
  C136 & C144 & C40 & _).
rewrite rbn9_tok in C40.
destruct (rbn9_D9_ovf X HA) as (Hov47 & _ & _). rewrite Hov47 in C144.
destruct (rbn9_D9_len X HA) as (_ & HD9).
pose proof (rbn9_NB_len X) as HNB.
assert (HTB : (length (rbm_TB X) <= 23)%nat) by (unfold rbm_TB; rewrite length_firstn; lia).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rnm & _ & Rnml &
  _ & Rtk & _ & Rtkl & _ & Rd & _ & Rdl & _).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(r9lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by r9lia. apply Z.mod_mul. lia. }
assert (HSHb : 0x7fff8000 + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 0x10007fff8000).
{ assert (ESH : rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8) by reflexivity. rewrite ESH. unfold SHADOW_OFF. r9lia. }
assert (HSHn : forall j, 0 <= j < 64 -> ~ (rbn_F X pos <= rbn_SH X pos + j < rbn_F X pos + 512)).
{ intros j Hj Hc. apply (rbn9_app_sh _ (in_app_addr _ _ _ HFapp Hc)). unfold kLowShadowBeg, kHighMemBeg. r9lia. }
apply (rbn9_head B LAWS DRO GM HV L7F X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ HX Hst).
intros regs3 mem3 mdc3 HJ3 SAME3 H23_3 H12_3 KD3 GD3.
remember (Z.of_nat (length (rbm_D9 X)) + 5) as nF eqn:EnF.
assert (HnF : 5 <= nF <= 40) by r9lia.
assert (KC3 : forall a n v, val_mem SEGS (mrestrict (w_H W1) memc1) a n v -> rbn_A X <= a ->
  a + Z.of_nat n <= rbn_A X + 184 -> val_mem SEGS (mrestrict (w_H W1) mem3) a n v).
{ intros a n v Hv Ha1 Ha2.
  apply (rbn9_kept_val _ _ _ _ _ _ _ KD3); [intros i Hi; cbv beta; r9lia | r9lia | r9lia | exact Hv]. }
destruct (rbn9_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem3 mdc3 HX HM HJ3) as (_ & _ & _ & _ & HFpr3 & _).
assert (Hsh3 : rbn_shadow_at W1 mem3 (rbn_SH X pos) (rbn_sh true true true true)).
{ apply (rbn9_sh_kept W1 memc1 mem3 _ _ _ Hsh KD3);
    [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
  intros j Hj Hc. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta in Hc.
  apply (HSHn j); r9lia. }
pose proof (rbn9_ra_true W1 mem3 (rbn_F X pos) Hsh3 HF8) as (_ & _ & RAD3).
apply (rbn9_checks B LAWS (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem3 mdc3 (ri_k X) regs3 (rbn_A X) (rbn_F X pos) nF (ri_display X) (ri_name X)
  (ri_token X) (ri_token_len X) (ri_display_len X) (ri_name_len X) (Z.of_nat (length (rbm_NB X)))
  (rbm_ovf 23 (rbm_NM X)) (Z.of_nat (length (rbm_TB X))) _ HJ3).
- exact (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9).
- exact (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19).
- exact (eq_trans (SAME3 20 ltac:(cbn; tauto)) H20).
- exact (eq_trans (SAME3 22 ltac:(cbn; tauto)) H22).
- exact H23_3.
- exact H12_3.
- exact (eq_trans (SAME3 24 ltac:(cbn; tauto)) H24).
- exact (eq_trans (SAME3 25 ltac:(cbn; tauto)) H25).
- exact (eq_trans (SAME3 26 ltac:(cbn; tauto)) H26).
- exact AR7.
- r9lia.
- r9lia.
- r9lia.
- exact HF4096.
- r9lia.
- r9lia.
- exact (rbn9_ovf01 23 (rbm_NM X)).
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- r9lia.
- apply KC3; [exact C8 | r9lia | r9lia].
- apply KC3; [exact C16 | r9lia | r9lia].
- apply KC3; [exact C24 | r9lia | r9lia].
- apply KC3; [exact C32 | r9lia | r9lia].
- apply KC3; [exact C40 | r9lia | r9lia].
- apply KC3; [exact C48 | r9lia | r9lia].
- apply KC3; [exact C56 | r9lia | r9lia].
- apply KC3; [exact C64 | r9lia | r9lia].
- apply KC3; [exact C72 | r9lia | r9lia].
- apply KC3; [exact C144 | r9lia | r9lia].
- apply KC3; [exact C176 | r9lia | r9lia].
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPW3 & _).
  apply HPW3. r9lia.
- exact (proj1 (HFpr3 (rbn_F X pos + 192 + nF) ltac:(r9lia))).
- apply (range_addressable_sub _ _ (rbn_F X pos + 192) 48); [exact RAD3 | r9lia | r9lia].
- unfold SHADOW_OFF. intros Hc.
  apply (rbn9_app_sh (rbn_F X pos + 192 + nF) (in_app_addr _ _ (rbn_F X pos + 192 + nF) HFapp ltac:(r9lia))).
  unfold kLowShadowBeg, kHighMemBeg. r9lia.
- intros a Ha. left. r9lia.
- right; right; right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite FA. change (fs_frame_bytes 3) with 512. r9lia.
- intros regs4 mem4 mdc4 (HJ4 & SAME4 & K4 & V4 & V144) H21_4 Hnacc.
  assert (HREF : rbm_acc X = false).
  { destruct (rbm_acc X) eqn:E; [|reflexivity]. exfalso. apply Hnacc.
    rewrite (rbn9_acc X HA) in E.
    apply andb_true_iff in E as [E E4]. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
    apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.ltb_lt in E3. apply Z.ltb_lt in E4.
    rewrite EnF. split; [exact E1|]. split; [exact E4|]. split; [exact E2 | exact E3]. }
  pose proof (rbn9_kept_trans _ _ _ _ _ _ KD3 K4) as K14.
  destruct (rbn9_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem4 mdc4 HX HM HJ4) as (_ & _ & _ & _ & _ & HSpr4).
  assert (Hsh4 : rbn_shadow_at W1 mem4 (rbn_SH X pos) (rbn_sh true true true true)).
  { apply (rbn9_sh_kept W1 memc1 mem4 _ _ _ Hsh K14);
      [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
    intros j Hj. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta.
    intros [Hc | [Hc | Hc]]; [apply (HSHn j); r9lia | r9lia | apply (HSHn j); r9lia]. }
  apply (rbn9_tail B LAWS (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X)
    (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem4 mdc4 (ri_k X) regs4 (rbn_A X) (rbn_F X pos) (rbn_SH X pos) _ HJ4).
  + exact (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9)).
  + exact (eq_trans (SAME4 18 ltac:(cbn; tauto)) (eq_trans (SAME3 18 ltac:(cbn; tauto)) H18)).
  + exact (eq_trans (SAME4 19 ltac:(cbn; tauto)) (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19)).
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + apply (rbn9_kept_val _ _ _ _ _ _ _ K14); [intros i Hi; cbv beta; r9lia | r9lia | r9lia | exact C72].
  + intros a Ha. replace a with (rbn_SH X pos + (a - rbn_SH X pos)) by r9lia. apply HSpr4. r9lia.
  + intros a Ha. right; right; right. exists 3, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite FA. change (fs_frame_bytes 3 / 8) with 64. unfold rbn_SH in Ha. r9lia.
  + intros j Hj. apply rbn9_val1_of_aview.
    exact (Hsh4 j ltac:(change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia)).
  + intros regs6 mem6 mdc6 HJ6 SAME6 H26_6 K6 HSH6.
    apply SRr_ret. exists pos, regs6, lyc1, Sc1, mem6, mdc6. split; [reflexivity|].
    apply (rbn9_close B LAWS X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs6 mem6 mdc6 HX Hst HJ6).
    * apply (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ K14 K6)).
      intros a Ha. cbv beta in Ha. unfold rbn9_W.
      destruct Ha as [[Ha | [Ha | Ha]] | Ha];
        [left; r9lia | right; left; r9lia | left; r9lia | right; right; left; r9lia].
    * exact HSH6.
    * intros r Hr. apply (rbn9_same3 regs1 regs3 regs4 regs6 _ _ _ r SAME3 SAME4 SAME6); cbn [In] in Hr |- *; tauto.
    * exact H26_6.
    * rewrite HREF. exact (eq_trans (SAME6 21 ltac:(cbn; tauto)) H21_4).
    * intros Hc. rewrite HREF in Hc. discriminate.
- intros regs4 mem4 mdc4 (HJ4 & SAME4 & K4 & V4 & V144) Hacc.
  destruct Hacc as (E1 & E4 & E2 & E3).
  assert (HACC : rbm_acc X = true).
  { rewrite (rbn9_acc X HA). rewrite E1. rewrite EnF in E4.
    rewrite (proj2 (Z.ltb_lt _ _) E2), (proj2 (Z.ltb_lt _ _) E3), (proj2 (Z.ltb_lt _ _) E4). reflexivity. }
  destruct (rbn9_acc_parts X HA E1) as (ENB & ETB & EDP).
  destruct (rbn9_acc_lens X HACC) as (_ & L1 & L2 & L3).
  assert (LDP : Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) = nF)
    by (rewrite <- EDP, length_app; cbn [length]; r9lia).
  assert (Hlnb : Z.of_nat (length (rbm_NB X)) = Z.of_nat (length (rbm_NM X))) by (rewrite ENB; reflexivity).
  assert (Hltb : Z.of_nat (length (rbm_TB X)) = Z.of_nat (length (bn_TK (rbm_NM X)))) by (rewrite ETB; reflexivity).
  pose proof (rbn9_kept_trans _ _ _ _ _ _ KD3 K4) as K14.
  pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & Hargs).
  destruct (Hargs HA) as (_ & Bn & Bt & Bd & HD12 & HD13 & HD23). clear Hargs.
  r9box HD12. r9box HD13. r9box HD23.
  destruct (rbn9_buf_lin X pos lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX HM Bn ltac:(r9lia))
    as (Bn0 & Bn1 & Bnam & Bnsp & BnF).
  destruct (rbn9_buf_lin X pos lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX HM Bt ltac:(r9lia))
    as (Bt0 & Bt1 & Btam & Btsp & BtF).
  destruct (rbn9_buf_lin X pos lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX HM Bd ltac:(r9lia))
    as (Bd0 & Bd1 & Bdam & Bdsp & BdF).
  r9box Bnam. r9box Bnsp. r9box BnF. r9box Btam. r9box Btsp. r9box BtF. r9box Bdam. r9box Bdsp. r9box BdF.
  assert (Hsh4 : rbn_shadow_at W1 mem4 (rbn_SH X pos) (rbn_sh true true true true)).
  { apply (rbn9_sh_kept W1 memc1 mem4 _ _ _ Hsh K14);
      [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
    intros j Hj. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta.
    intros [Hc | [Hc | Hc]]; [apply (HSHn j); r9lia | r9lia | apply (HSHn j); r9lia]. }
  pose proof (rbn9_ra_true W1 mem4 (rbn_F X pos) Hsh4 HF8) as (RA64 & RA128 & RA192).
  assert (KC4 : forall a n v, val_mem SEGS (mrestrict (w_H W1) memc1) a n v -> rbn_A X <= a ->
    a + Z.of_nat n <= rbn_A X + 144 -> val_mem SEGS (mrestrict (w_H W1) mem4) a n v).
  { intros a n v Hv Ha1 Ha2.
    apply (rbn9_kept_val _ _ _ _ _ _ _ K14); [intros i Hi; cbv beta; r9lia | r9lia | r9lia | exact Hv]. }
  assert (HW14 : forall a, (rbn_F X pos + 192 <= a < rbn_F X pos + 240) \/
      (rbn_A X + 144 <= a < rbn_A X + 148 \/ a = rbn_F X pos + 192 + nF) ->
    (rbn_F X pos <= a < rbn_F X pos + 512) \/ (alloc_ceiling <= a) \/ (rbn_SH X pos <= a < rbn_SH X pos + 64)).
  { intros a [Ha | [Ha | Ha]]; [left; r9lia | right; left; r9lia | left; r9lia]. }
  apply (rbn9_copies B LAWS AMEMCPY (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X)
    (ri_mem0 X) (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem4 mdc4 (ri_k X) regs4 (rbn_A X) (rbn_F X pos)
    (ri_name X) (ri_token X) (ri_display X) (Z.of_nat (length (rbm_NB X))) (Z.of_nat (length (rbm_TB X))) nF _ HJ4).
  + exact (eq_trans (SAME4 2 ltac:(cbn; tauto)) (eq_trans (SAME3 2 ltac:(cbn; tauto)) H2)).
  + exact (eq_trans (SAME4 3 ltac:(cbn; tauto)) (eq_trans (SAME3 3 ltac:(cbn; tauto)) H3)).
  + exact (eq_trans (SAME4 4 ltac:(cbn; tauto)) (eq_trans (SAME3 4 ltac:(cbn; tauto)) H4)).
  + exact (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9)).
  + exact (eq_trans (SAME4 19 ltac:(cbn; tauto)) (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19)).
  + exact (eq_trans (SAME4 20 ltac:(cbn; tauto)) (eq_trans (SAME3 20 ltac:(cbn; tauto)) H20)).
  + exact (eq_trans (SAME4 23 ltac:(cbn; tauto)) H23_3).
  + exact (eq_trans (SAME4 24 ltac:(cbn; tauto)) (eq_trans (SAME3 24 ltac:(cbn; tauto)) H24)).
  + exact (eq_trans (SAME4 26 ltac:(cbn; tauto)) (eq_trans (SAME3 26 ltac:(cbn; tauto)) H26)).
  + exact (eq_trans (SAME4 27 ltac:(cbn; tauto)) (eq_trans (SAME3 27 ltac:(cbn; tauto)) H27)).
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + r9lia.
  + unfold kHighMemBeg. r9lia.
  + apply KC4; [exact C8 | r9lia | r9lia].
  + apply KC4; [exact C16 | r9lia | r9lia].
  + apply KC4; [exact C24 | r9lia | r9lia].
  + apply KC4; [exact C48 | r9lia | r9lia].
  + apply (rbn9_cpy_mk X pos lyc1 Sc1 W1 memc1 mdc1 _ mem4 mdc4 _ (ri_name X) (Z.min (ri_name_len X) 24)
      (Z.of_nat (length (rbm_NB X)) + 1) 64 HX HM HJ4 K14 HW14 Bn); [r9lia | r9lia | r9lia | r9lia |].
    apply (range_addressable_sub _ _ (rbn_F X pos + 64) 24); [exact RA64 | r9lia | r9lia].
  + apply (rbn9_cpy_mk X pos lyc1 Sc1 W1 memc1 mdc1 _ mem4 mdc4 _ (ri_token X) (Z.min (ri_token_len X) 24)
      (Z.of_nat (length (rbm_TB X)) + 1) 128 HX HM HJ4 K14 HW14 Bt); [r9lia | r9lia | r9lia | r9lia |].
    apply (range_addressable_sub _ _ (rbn_F X pos + 128) 24); [exact RA128 | r9lia | r9lia].
  + apply (rbn9_cpy_mk X pos lyc1 Sc1 W1 memc1 mdc1 _ mem4 mdc4 _ (ri_display X) (Z.min (ri_display_len X) 48)
      (nF + 1) 192 HX HM HJ4 K14 HW14 Bd); [r9lia | r9lia | r9lia | r9lia |].
    apply (range_addressable_sub _ _ (rbn_F X pos + 192) 48); [exact RA192 | r9lia | r9lia].
  + unfold rbn9_box in HD12. destruct HD12 as [Hd | Hd]; [left | right]; r9lia.
  + unfold rbn9_box in HD13. destruct HD13 as [Hd | Hd]; [left | right]; r9lia.
  + unfold rbn9_box in HD23. destruct HD23 as [Hd | Hd]; [left | right]; r9lia.
  + intros a [Ha | [Ha | Ha]].
    * unfold rbn9_box in Bnsp, BnF. split; r9lia.
    * unfold rbn9_box in Btsp, BtF. split; r9lia.
    * unfold rbn9_box in Bdsp, BdF. split; r9lia.
  + intros regs5 mem5 mdc5 HJ5 SAME5 H21_5 K5 CP1 CP2 CP3.
    destruct (rbn9_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem5 mdc5 HX HM HJ5) as (_ & _ & _ & _ & _ & HSpr5).
    assert (Hsh5 : rbn_shadow_at W1 mem5 (rbn_SH X pos) (rbn_sh true true true true)).
    { apply (rbn9_sh_kept W1 mem4 mem5 _ _ _ Hsh4 K5);
        [r9lia | change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia |].
      intros j Hj. change (Z.of_nat (length (rbn_sh true true true true))) with 64 in Hj. cbv beta.
      intros [Hc | [Hc | [Hc | Hc]]].
      - unfold rbn9_box in Bnam. r9lia.
      - unfold rbn9_box in Btam. r9lia.
      - unfold rbn9_box in Bdam. r9lia.
      - r9lia. }
    apply (rbn9_tail B LAWS (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X)
      (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem5 mdc5 (ri_k X) regs5 (rbn_A X) (rbn_F X pos) (rbn_SH X pos) _
      HJ5).
    * exact (eq_trans (SAME5 9 ltac:(cbn; tauto))
        (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (SAME3 9 ltac:(cbn; tauto)) H9))).
    * exact (eq_trans (SAME5 18 ltac:(cbn; tauto))
        (eq_trans (SAME4 18 ltac:(cbn; tauto)) (eq_trans (SAME3 18 ltac:(cbn; tauto)) H18))).
    * exact (eq_trans (SAME5 19 ltac:(cbn; tauto))
        (eq_trans (SAME4 19 ltac:(cbn; tauto)) (eq_trans (SAME3 19 ltac:(cbn; tauto)) H19))).
    * r9lia.
    * r9lia.
    * r9lia.
    * r9lia.
    * r9lia.
    * apply (rbn9_kept_val _ _ _ _ _ _ _ K5); [ | r9lia | r9lia | apply KC4; [exact C72 | r9lia | r9lia]].
      intros i Hi; cbv beta. unfold rbn9_box in Bnsp, Btsp, Bdsp. r9lia.
    * intros a Ha. replace a with (rbn_SH X pos + (a - rbn_SH X pos)) by r9lia. apply HSpr5. r9lia.
    * intros a Ha. right; right; right. exists 3, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite FA. change (fs_frame_bytes 3 / 8) with 64. unfold rbn_SH in Ha. r9lia.
    * intros j Hj. apply rbn9_val1_of_aview.
      exact (Hsh5 j ltac:(change (Z.of_nat (length (rbn_sh true true true true))) with 64; r9lia)).
    * intros regs6 mem6 mdc6 HJ6 SAME6 H26_6 K6 HSH6.
      apply SRr_ret. exists pos, regs6, lyc1, Sc1, mem6, mdc6. split; [reflexivity|].
      apply (rbn9_close B LAWS X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs6 mem6 mdc6 HX Hst HJ6).
      -- apply (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ K14 K5) K6)).
         intros a Ha. cbv beta in Ha. unfold rbn9_W, rbn_wr.
         change (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) with (rbm_NM X).
         destruct Ha as [[[Ha | [Ha | Ha]] | [Ha | [Ha | [Ha | Ha]]]] | Ha].
         ++ left; r9lia.
         ++ right; left; r9lia.
         ++ left; r9lia.
         ++ right; right; right. split; [exact HACC|]. left. r9lia.
         ++ right; right; right. split; [exact HACC|]. right; left. r9lia.
         ++ right; right; right. split; [exact HACC|]. right; right. r9lia.
         ++ right; left; r9lia.
         ++ right; right; left; r9lia.
      -- exact HSH6.
      -- intros r Hr. apply (rbn9_same4 regs1 regs3 regs4 regs5 regs6 _ _ _ _ r SAME3 SAME4 SAME5 SAME6);
           cbn [In] in Hr |- *; tauto.
      -- exact H26_6.
      -- rewrite HACC. exact (eq_trans (SAME6 21 ltac:(cbn; tauto)) H21_5).
      -- intros _. split; [|split].
         ++ apply (rbn9_garr8_move (w_H W1) (w_H W1) mem4 mem6 (rbn_F X pos + 64) (ri_name X)).
            ** intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
               rewrite (proj1 K6 (ri_name X + i)); [apply CP1; r9lia | r9lia | cbv beta; unfold rbn9_box in Bnam; r9lia].
            ** rewrite <- ENB. apply (rbn9_kept_garr W1 memc1 mem4 _ _ _ K14); [ | | | exact G64].
               --- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. cbv beta. r9lia.
               --- r9lia.
               --- rewrite length_app. cbn [length]. r9lia.
         ++ apply (rbn9_garr8_move (w_H W1) (w_H W1) mem4 mem6 (rbn_F X pos + 128) (ri_token X)).
            ** intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
               rewrite (proj1 K6 (ri_token X + i)); [apply CP2; r9lia | r9lia | cbv beta; unfold rbn9_box in Btam; r9lia].
            ** rewrite <- ETB. apply (rbn9_kept_garr W1 memc1 mem4 _ _ _ K14); [ | | | exact G128].
               --- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. cbv beta. r9lia.
               --- r9lia.
               --- rewrite length_app. cbn [length]. r9lia.
         ++ apply (rbn9_garr8_move (w_H W1) (w_H W1) mem4 mem6 (rbn_F X pos + 192) (ri_display X)).
            ** intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
               rewrite (proj1 K6 (ri_display X + i)); [apply CP3; r9lia | r9lia | cbv beta; unfold rbn9_box in Bdam; r9lia].
            ** rewrite <- EDP. apply rbn9_garr8_app.
               --- apply (rbn9_kept_garr W1 mem3 mem4 _ _ _ K4);
                     [ | r9lia | rewrite length_app; cbn [length]; r9lia | exact GD3].
                   intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. cbv beta. r9lia.
               --- intros j Hj. cbn [length] in Hj. assert (Hj0 : j = 0%nat) by lia. subst j. cbn [nth].
                   split; [|lia].
                   replace (rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X ++ [32; 111; 117; 116; 41])) + Z.of_nat 0)
                     with (rbn_F X pos + 192 + nF) by (rewrite length_app; cbn [length]; r9lia).
                   exact V4.
Qed.
End h.
End f.
End d.
