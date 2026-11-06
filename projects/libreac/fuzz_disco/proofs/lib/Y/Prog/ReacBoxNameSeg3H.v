(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 766 of its 871 lines of code are new or changed and 986 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameSeg3D.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition rbn3h_Bx : sv := SOff 22 0.
Definition rbn3h_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition rbn3h_rA : YP09.region := YP09.mkRegion (Some 9%nat) 40 56 40 56 [].
Definition rbn3h_rS : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition rbn3h_fa0 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition rbn3h_fa1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (25%nat, mkAF 1 (2 ^ 47 - 2) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition rbn3h_ss0 : sstate := mkSS 14516 sr_atoms [rbn3h_rA] None rbn3h_fa0.
Definition rbn3h_ss1 : sstate := mkSS 14516 sr_atoms [rbn3h_rA; rbn3h_rS] None rbn3h_fa1.
Definition rbn3h_SH1 : list shent := [mkSHE 25 0 1].
Definition rbn3h_rT : YP09.region := YP09.mkRegion (Some (A_OBJ 26)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition rbn3h_fa2 : facts :=
  mkFacts [(22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_OBJ 26, mkAF YImgTop.IMG_LO YImgTop.IMG_TOP 3)] [] [].
Definition rbn3h_ss2 : sstate := mkSS 14552 sr_atoms [rbn3h_rT] None rbn3h_fa2.
Definition rbn3h_SH2 : list shent := [mkSHE (A_OBJ 26) 0 24].
Definition rbn3h_kl : list (bv 5) := [2; 3; 4; 8; 9; 14; 15; 18; 19; 21; 22; 23; 24; 26]%bv.
Lemma rbn3h_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn3h_ex_in : forall (r : bv 5) l, existsb (bv_eqb r) l = true -> In r l.
Proof. intros r l H. apply existsb_exists in H as (x & Hx & He). apply bv_eqb_eq in He. subst x. exact Hx. Qed.
Lemma rbn3h_den_mod : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 (v mod 2 ^ 64).
Proof.
intros E n v H. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r, !Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite !Zmod_mod. reflexivity.
Qed.
Lemma rbn3h_bad : forall E v, ew E 27 = Z_to_bv 64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 27 0) (SLit (-1)))) = false ->
  v = 1 \/ v = 2 \/ v = 3.
Proof.
intros E v H27 Hv Hc. rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
rewrite (U_of_S E (SAluw ALU_ADD (SOff 27 0) (SLit (-1)))), S_SAluw, !U_SLit, U_SOff, H27 in Hc. cbn [zalu_raw] in Hc.
rewrite Z_to_bv_unsigned in Hc.
assert (W64 : forall z, bv_wrap 64 z = z mod 18446744073709551616) by (intros z; reflexivity).
assert (S32 : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648) by (intros z; reflexivity).
rewrite !W64, S32 in Hc. unfold zcanon, M64 in Hc.
change (2 ^ 64) with 18446744073709551616 in Hc. change (2 ^ 32) with 4294967296 in Hc.
change (2 ^ 31) with 2147483648 in Hv.
Z.div_mod_to_equations. lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn3h_vm8_mod : forall (m : word -> option byte) a v, val_mem SEGS m a 8 (v mod 2 ^ 64) <-> val_mem SEGS m a 8 v.
Proof.
intros m a v.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite E in H | rewrite <- E in H]; exact H.
Qed.
Lemma rbn3h_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbn3h_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn3h_mbyte_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' a Hm. unfold mbyte. rewrite Hm. reflexivity. Qed.
Lemma rbn3h_aview_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hm. apply aview_eq_of. apply Hm. Qed.
Lemma rbn3h_apresent_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hm (Ha & b & Hb). split; [exact Ha|]. exists b.
pose proof (Hm (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Ha in Hx. rewrite Hx. exact Hb.
Qed.
Lemma rbn3h_val_mem_mr : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v Hm Hv k Hk. rewrite (rbn3h_mbyte_mr H m m' _ Hm). exact (Hv k Hk). Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn3h_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn3h_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_A X mod 32 = 0 /\ rbn_SP X + 16 <= 2 ^ 47 /\
  ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  ly_stk_lo (ri_ly X) + ri_STK X <= ri_sp0 X /\ ri_sp0 X <= ly_stk_hi (ri_ly X) /\ rbn_SP X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
rewrite WS in Hstk. unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
repeat split; lia.
Qed.
Lemma rbn3h_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn3h_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
Qed.
Lemma rbn3h_mid_write : forall X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh -> Z.of_nat (length sh) <= 64 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc2 mdc2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 40 <= a < rbn_A X + 56) ->
     aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) memc2) ->
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 sh HX HM Hsh HJ2 Hkp Hgr.
destruct (rbn3h_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
pose proof (proj1 (proj1 HX)) as HARc.
destruct HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
split; [exact HJ2|]. split; [exact Hfrs1|]. split; [exact Hperm|].
split.
{ intros a Hroa Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hroa as [(sg & Hsg & _ & Hr) | Hr];
        [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow.
  rewrite (Hkp a ltac:(lia) ltac:(lia)). exact (Hro1 a Hroa Ho He). }
split.
{ split.
  { intros a Ha Hn He. rewrite (Hkp a ltac:(lia) ltac:(lia)). exact (K1 a Ha Hn He). }
  split.
  { intros b m j Hb Hj He.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & Hb4 & Hbc & _).
    rewrite (Hkp (b + j) ltac:(lia) ltac:(lia)). exact (K2 b m j Hb Hj He). }
  split.
  { intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow.
    rewrite (Hkp a ltac:(lia) ltac:(lia)). exact (K3 a Hia Ho He). }
  split.
  { intros cid p a Hcp Ha He.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HARc Hcp) as (Hc4096 & Hcceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct Ha as [Ha | Ha].
    - pose proof Ha as Ha'. unfold in_zr, frame_rng in Ha'. cbn [fst snd] in Ha'.
      rewrite (Hkp a ltac:(lia) ltac:(lia)). exact (K4 cid p a Hcp (or_introl Ha) He).
    - pose proof Ha as Ha'. unfold in_zr in Ha'. cbn [fst snd] in Ha'.
      pose proof (rbn3h_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
      rewrite (Hkp a ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)
        ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)).
      exact (K4 cid p a Hcp (or_intror Ha) He). }
  split.
  { intros a Ha Hn Hp. apply (apresent_grows _ _ _ _ Hgr). exact (K5 a Ha Hn Hp). }
  intros a Ha. apply (apresent_grows _ _ _ _ Hgr). exact (K6 a Ha). }
split.
{ intros j r Hj.
  assert (Hjr : (j < 13)%nat)
    by (apply (proj1 (nth_error_Some rbn_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [| exact (HFr1 j r Hj)].
  intros k Hk. apply Hkp; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [| exact HFL1].
  intros k Hk. apply Hkp; lia. }
intros j Hj.
pose proof (rbn3h_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH in *.
rewrite (Hkp (shadow_addr (rbn_F X pos) + j) ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)
  ltac:(unfold kLowShadowBeg, kHighMemBeg in *; lia)).
exact (HSh1 j Hj).
Qed.
Lemma rbn3h_mid_same : forall X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) ->
  (forall x, mrestrict (w_H W1) memc3 x = mrestrict (w_H W1) memc2 x) ->
  rbn_mid B X pos lyc1 Sc1 W1 memc3 mdc3 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh
  (HJ & Hfr & Hp & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & HFr & HFL & HSh) HJ3 Hm.
assert (Hv : forall a, aview SEGS (w_H W1) memc3 a = aview SEGS (w_H W1) memc2 a)
  by (intros a; apply rbn3h_aview_mr; exact Hm).
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hp|].
split; [intros a H1 H2 H3; rewrite Hv; exact (Hro a H1 H2 H3)|].
split.
{ split; [intros a H1 H2 H3; rewrite Hv; exact (K1 a H1 H2 H3)|].
  split; [intros b m j H1 H2 H3; rewrite Hv; exact (K2 b m j H1 H2 H3)|].
  split; [intros a H1 H2 H3; rewrite Hv; exact (K3 a H1 H2 H3)|].
  split; [intros cid p a H1 H2 H3; rewrite Hv; exact (K4 cid p a H1 H2 H3)|].
  split; [intros a H1 H2 H3; apply (rbn3h_apresent_mr _ memc2 memc3 a Hm); exact (K5 a H1 H2 H3)|].
  intros a H1. apply (rbn3h_apresent_mr _ memc2 memc3 a Hm). exact (K6 a H1). }
split; [intros j r Hj; apply (rbn3h_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact (HFr j r Hj)|].
split; [apply (rbn3h_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact HFL|].
intros j Hj. rewrite Hv. exact (HSh j Hj).
Qed.
Lemma rbn3h_finQ : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 memc2 mdc2,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc2 mdc2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 40 <= a < rbn_A X + 56) ->
     aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) memc2) ->
  (forall r : bv 5, existsb (bv_eqb r) rbn3h_kl = true -> getr regs2 r = getr regs1 r) ->
  getr regs2 27 = getr regs1 27 ->
  val_mem SEGS (mrestrict (w_H W1) memc2) (rbn_A X + 40) 8 (ri_i X) ->
  val_mem SEGS (mrestrict (w_H W1) memc2) (rbn_A X + 48) 8 (ri_o X) ->
  (ri_said X = 0 \/ ri_sd X = []) ->
  rbn3_stQ B X pos regs2 lyc1 Sc1 W1 memc2 mdc2.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 memc2 mdc2 HX H3 HJ2 Hkp Hgr Hkl H27 V40 V48 Hsd.
pose proof H3 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R25 & R21 & R24 & R27 & R26 &
  R12 & R13 & R14 & R15 & RNL & HA).
destruct (rbn3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rbn3_stQ.
split; [exact (rbn3h_mid_write X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 _ HX HM
  ltac:(rewrite rbn3h_sh_len; lia) HJ2 Hkp Hgr)|].
split.
{ unfold rbn_rbase. rewrite !Hkl by (vm_compute; reflexivity).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
  split; [exact R9|]. split; [exact R19|]. split; [exact R22 | exact R23]. }
split; [rewrite Hkl by (vm_compute; reflexivity); exact R18|].
split; [rewrite H27; exact R27|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R21|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R24|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R26|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R14|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R15|].
split.
{ unfold rbn3_ion. cbn [rbn_cells]. split; [exact V40|]. split; [exact V48|]. split; [|exact I].
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [| exact RNL]. intros k Hk. apply Hkp; lia. }
split; [exact Hsd | exact HA].
Qed.
Lemma rbn3h_finT : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 memc2 mdc2,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc2 mdc2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 40 <= a < rbn_A X + 56) ->
     aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) memc2) ->
  (forall r : bv 5, existsb (bv_eqb r) rbn3h_kl = true -> getr regs2 r = getr regs1 r) ->
  getr regs2 25 = getr regs1 25 ->
  val_mem SEGS (mrestrict (w_H W1) memc2) (rbn_A X + 40) 8 (ri_i X) ->
  val_mem SEGS (mrestrict (w_H W1) memc2) (rbn_A X + 48) 8 (ri_o X) ->
  ri_said X <> 0 -> ri_sd X <> [] ->
  rbn3_stT B X pos regs2 lyc1 Sc1 W1 memc2 mdc2 (ri_said X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 memc2 mdc2 HX H3 HJ2 Hkp Hgr Hkl H25 V40 V48 Hs0 Hne.
pose proof H3 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R25 & R21 & R24 & R27 & R26 &
  R12 & R13 & R14 & R15 & RNL & HA).
destruct (rbn3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rbn3_stT.
split; [exact (rbn3h_mid_write X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 _ HX HM
  ltac:(rewrite rbn3h_sh_len; lia) HJ2 Hkp Hgr)|].
split.
{ unfold rbn_rbase. rewrite !Hkl by (vm_compute; reflexivity).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
  split; [exact R9|]. split; [exact R19|]. split; [exact R22 | exact R23]. }
split; [rewrite Hkl by (vm_compute; reflexivity); exact R18|].
split; [rewrite H25; exact R25|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R21|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R24|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R26|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R14|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R15|].
split.
{ unfold rbn3_ion. cbn [rbn_cells]. split; [exact V40|]. split; [exact V48|]. split; [|exact I].
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [| exact RNL]. intros k Hk. apply Hkp; lia. }
split; [left; split; [exact Hs0 | split; [exact Hne | reflexivity]] | exact HA].
Qed.
Lemma rbn3h_finT2 : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 memc2 mdc2 P,
  rbn3_stQ B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc2 mdc2 (ri_k X) ->
  (forall x, mrestrict (w_H W1) memc2 x = mrestrict (w_H W1) memc1 x) ->
  (forall r : bv 5, existsb (bv_eqb r) rbn3h_kl = true -> getr regs2 r = getr regs1 r) ->
  getr regs2 25 = w64 P -> rbn3_Pok X P ->
  rbn3_stT B X pos regs2 lyc1 Sc1 W1 memc2 mdc2 P.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 memc2 mdc2 P HQ HJ2 Hm Hkl G25 HP.
pose proof HQ as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R27 & R21 & R24 & R26 & R14 & R15 &
  HC & Hsd & HA).
unfold rbn3_stT.
split; [exact (rbn3h_mid_same X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 _ HM HJ2 Hm)|].
split.
{ unfold rbn_rbase. rewrite !Hkl by (vm_compute; reflexivity).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
  split; [exact R9|]. split; [exact R19|]. split; [exact R22 | exact R23]. }
split; [rewrite Hkl by (vm_compute; reflexivity); exact R18|].
split; [exact G25|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R21|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R24|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R26|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R14|].
split; [rewrite Hkl by (vm_compute; reflexivity); exact R15|].
split.
{ unfold rbn3_ion in HC |- *. cbn [rbn_cells] in HC |- *. destruct HC as (C40 & C48 & C56 & _).
  split; [exact (rbn3h_val_mem_mr _ memc1 memc2 _ _ _ Hm C40)|].
  split; [exact (rbn3h_val_mem_mr _ memc1 memc2 _ _ _ Hm C48)|].
  split; [exact (rbn3h_val_mem_mr _ memc1 memc2 _ _ _ Hm C56) | exact I]. }
split; [exact HP | exact HA].
Qed.
Ltac rbn3h_awr X B9 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X - ri_sp0 X));
        [reflexivity | cbn [ew ewset Nat.eqb]; rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
        | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
Ltac rbn3h_kw X HFr B9 K :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    let rs1 := eval vm_compute in rs in
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 40 <= a < rbn_A X + 56) ->
       aview SEGS H m2 a = aview SEGS H m1 a);
    [ apply (rbn3h_kept_frame Ex rs H m1 m2 (fun a => rbn_A X + 40 <= a < rbn_A X + 56) HFr);
      let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
      intros a (r & Hr & Hw); change (In r rs1) in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hw; rewrite ?B9 in Hw; cbv beta; lia | ]);
      destruct Hr
    | ]
  end.
Ltac rbn3h_cells X HS Ei Eo V40 V48 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    let HR := fresh "HR" in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR;
    cbn [ms_mem restrict] in HR;
    let BA := fresh "BA" in
    assert (BA : bv_unsigned (ew Ex 9%nat) = rbn_A X)
      by (cbn [ew ewset Nat.eqb]; assumption);
    assert (V40 : val_mem SEGS (mrestrict Hh (ms_mem msx)) (rbn_A X + 40) 8 (ri_i X));
    [ apply (proj1 (rbn3h_vm8_mod _ _ _));
      exact (field_of_region Ex _ 9%nat (rbn_A X) _ _ _ _ _ 40 8 (SOff 12 0) (ri_i X mod 2 ^ 64) HR BA
        ltac:(cbn [In]; tauto) (rbn3h_den_mod Ex 12 (ri_i X) Ei)
        ltac:(change (8 * Z.of_N 8) with 64; pose proof (Z.mod_pos_bound (ri_i X) (2 ^ 64) ltac:(lia)); lia)
        ltac:(cbn; lia))
    | ];
    assert (V48 : val_mem SEGS (mrestrict Hh (ms_mem msx)) (rbn_A X + 48) 8 (ri_o X));
    [ apply (proj1 (rbn3h_vm8_mod _ _ _));
      exact (field_of_region Ex _ 9%nat (rbn_A X) _ _ _ _ _ 48 8 (SOff 13 0) (ri_o X mod 2 ^ 64) HR BA
        ltac:(cbn [In]; tauto) (rbn3h_den_mod Ex 13 (ri_o X) Eo)
        ltac:(change (8 * Z.of_N 8) with 64; pose proof (Z.mod_pos_bound (ri_o X) (2 ^ 64) ltac:(lia)); lia)
        ltac:(cbn; lia))
    | ]
  end.
Ltac rbn3h_kept HS HAE rg kl Hkl :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    assert (Hkl : forall r : bv 5, existsb (bv_eqb r) kl = true -> getr (ms_regs msx) r = getr rg r);
    [ let r := fresh "r" in let Hb := fresh "Hb" in intros r Hb;
      exact (regs_kept_of_st_ok_pi Ex ssx (restrict Hh msx) rg _ kl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity) r (rbn3h_ex_in r kl Hb))
    | ]
  end.
Hypothesis SAID : rbn3_said_stmt B.
Lemma rbn3h_h1_s : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 -> ri_said X <> 0 ->
  SRr SEGS W1 (rbn_cfg X RBN_P3 regs1 memc1 mdc1) (fun W2 c2 => rbn3_atQ B X W2 c2 \/ rbn3_atT B X W2 c2).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3 Hs0.
pose proof H3 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R25 & R21 & R24 & R27 & R26 &
  R12 & R13 & R14 & R15 & RNL & HA).
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
destruct (rbn3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
destruct (SAID X pos lyc1 Sc1 W1 memc1 mdc1 HX HA Hs0 (rbn3_rel_of_mid B X pos lyc1 Sc1 W1 memc1 mdc1 _ HM))
  as [Hstr Hsep].
pose proof Hstr as (Hf & Hg & Ha0 & Ha1 & Hl & Ham & Hra & Hhv & Htl).
destruct (Hg 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vb Rb].
change (Z.of_nat 0) with 0 in Vb. rewrite Z.add_0_r in Vb.
set (b := nth 0 (ri_sd X ++ [0]) 0) in *.
assert (Hbd : b = nth 0 (ri_sd X ++ [0]) 0) by reflexivity.
clearbody b.
remember (Eimg (Ereg regs1 [Z_to_bv 64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 b]) E)
  by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (B9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 (ri_said X)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (B22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (B25 : bv_unsigned (ew E 25) = ri_said X) by (rewrite E25; apply unsigned_lit_small; lia).
assert (B32 : bv_unsigned (ew E 32) = b) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi (fx := ri_fq X) SEGS VAL E rbn3h_ss1
  (restrict (w_H W1) (mkst (fx := ri_fq X) regs1 (Z_to_bv 64 (BASE + 14516)) memc1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn3h_ss1. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn3h_rA, rbn3h_rS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply K6. lia.
    + rewrite B25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (ri_said X) 0 1 (SOff 32 0) b);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact Vb.
  - apply pairwise_disjoint_of_extents. unfold rbn3h_rA, rbn3h_rS, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B25.
    pose proof (proj1 (Hsep (ri_said X) ltac:(lia))) as Hn.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - unfold rbn3h_fa1. split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite B9, B22, B25, B32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok SEGS rbn3h_Bx rbn3h_SH1 E (mrestrict (w_H W1) memc1)).
{ unfold sh_ok, rbn3h_SH1. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) memc1 E rbn3h_Bx 25 (ri_said X) (Z.of_nat (length (ri_sd X)) + 1)
    (ri_said X) 0 1 Hra).
  - unfold rbn3h_Bx. apply (U_atom E 22 SHADOW_OFF E22). unfold SHADOW_OFF; lia.
  - apply (U_atom E 25 (ri_said X) E25). lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
clear HE.
unfold rbn_cfg, cfg_at.
replace (BASE + AF_both3_reac_box_name + RBN_P3) with (BASE + 14516)
  by (unfold AF_both3_reac_box_name, RBN_P3; lia).
change (w64 (BASE + 14516)) with (Z_to_bv 64 (BASE + 14516)).
pose (RUN := paj_run (fx := ri_fq X) B LAWS).
pose (RUNTO := paj_run_to (fx := ri_fq X) B LAWS).
pose (BR := paj_branch (fx := ri_fq X) (PI := PI)).
paj_run_tok RUN HS HJ1 SHOK rbn3h_span.
{ rbn3h_awr X B9. }
rbn3h_kw X HFr B9 KW1. clear HF HFr. rename HG into HG1. rename HJ1 into HJA. rename HEI0 into HEIA.
psrr_branch_tok RUN BR HS SHOK rbn3h_span.
- assert (Hb0 : b <> 0).
  { lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (F32 : ew Ex 32 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E32);
      rewrite branch_ne_U, (U_atom Ex 32 b F32 ltac:(lia)), U_lit in Hc by lia end.
    apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  assert (Hne : ri_sd X <> []).
  { intros Hnil. apply Hb0. rewrite Hbd, Hnil. reflexivity. }
  paj_run_to_tok RUNTO HS HJA SHOK rbn3h_span 14612.
  { rbn3h_awr X B9. }
  rbn3h_kw X HFr B9 KW2.
  pose proof (mem_grows_trans _ _ _ HG1 HG) as HGT.
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 40 <= a < rbn_A X + 56) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) memc1 a)
    by (intros a Ha Hn; rewrite (KW2 a Ha Hn); exact (KW1 a Ha Hn)).
  assert (Ei : ew E 12 = Z_to_bv 64 (ri_i X)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (Eo : ew E 13 = Z_to_bv 64 (ri_o X)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
  rbn3h_cells X HS Ei Eo V40 V48.
  rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let G25 := fresh "G25" in
    pose proof (st_ok_pi_restrict_reg (w_H W1) Ex ssx msx (25%bv : bv 5) HS) as G25;
    replace (sr_get (ss_regs ssx) (25%bv : bv 5)) with (SOff 25 0) in G25 by (vm_compute; reflexivity);
    cbn [ms_regs restrict mkst sv_denot ew ewset Nat.eqb] in G25; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in G25;
    rewrite E25 in G25 end.
  apply SRr_ret. pmkst HS. right.
  lazymatch goal with |- rbn3_atT _ _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) =>
    exists pos, rr, lyc1, Sc1, mm, dd, (ri_said X) end.
  split.
  { unfold rbn_cfg, cfg_at, w64.
    replace (BASE + AF_both3_reac_box_name + RBN_T3) with (BASE + 14612)
      by (unfold AF_both3_reac_box_name, RBN_T3; lia).
    reflexivity. }
  refine (rbn3h_finT X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX H3 HJA KW HGT Hkl _ V40 V48 Hs0 Hne).
  rewrite R25. exact G25.
- assert (Hb0 : b = 0).
  { lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (F32 : ew Ex 32 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E32);
      rewrite branch_ne_U, (U_atom Ex 32 b F32 ltac:(lia)), U_lit in Hc by lia end.
    apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  assert (Hnil : ri_sd X = []).
  { destruct (ri_sd X) as [|c l]; [reflexivity|]. exfalso.
    pose proof (Forall_inv Hf) as Hc0. cbv beta in Hc0.
    change (nth 0 ((c :: l) ++ [0]) 0) with c in Hbd. lia. }
  paj_run_to_tok RUNTO HS HJA SHOK rbn3h_span 14552.
  { rbn3h_awr X B9. }
  rbn3h_kw X HFr B9 KW2.
  pose proof (mem_grows_trans _ _ _ HG1 HG) as HGT.
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 40 <= a < rbn_A X + 56) ->
    aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) memc1 a)
    by (intros a Ha Hn; rewrite (KW2 a Ha Hn); exact (KW1 a Ha Hn)).
  assert (Ei : ew E 12 = Z_to_bv 64 (ri_i X)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (Eo : ew E 13 = Z_to_bv 64 (ri_o X)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
  rbn3h_cells X HS Ei Eo V40 V48.
  rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let G27 := fresh "G27" in
    pose proof (st_ok_pi_restrict_reg (w_H W1) Ex ssx msx (27%bv : bv 5) HS) as G27;
    replace (sr_get (ss_regs ssx) (27%bv : bv 5)) with (SOff 27 0) in G27 by (vm_compute; reflexivity);
    cbn [ms_regs restrict mkst sv_denot ew ewset Nat.eqb] in G27; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in G27;
    rewrite (EE 27%nat 27%bv eq_refl) in G27 end.
  apply SRr_ret. pmkst HS. left.
  lazymatch goal with |- rbn3_atQ _ _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) =>
    exists pos, rr, lyc1, Sc1, mm, dd end.
  split.
  { unfold rbn_cfg, cfg_at, w64.
    replace (BASE + AF_both3_reac_box_name + RBN_Q3) with (BASE + 14552)
      by (unfold AF_both3_reac_box_name, RBN_Q3; lia).
    reflexivity. }
  refine (rbn3h_finQ X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX H3 HJA KW HGT Hkl _ V40 V48 (or_intror Hnil)).
  exact G27.
Qed.
Lemma rbn3h_h1_z : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 -> ri_said X = 0 ->
  SRr SEGS W1 (rbn_cfg X RBN_P3 regs1 memc1 mdc1) (fun W2 c2 => rbn3_atQ B X W2 c2 \/ rbn3_atT B X W2 c2).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3 Hs0.
pose proof H3 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R25 & R21 & R24 & R27 & R26 &
  R12 & R13 & R14 & R15 & RNL & HA).
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
destruct (rbn3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
remember (Eimg (Ereg regs1 (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (@nil word)) E)
  by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (B9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (B22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS0 : st_ok_pi (fx := ri_fq X) SEGS VAL E rbn3h_ss0
  (restrict (w_H W1) (mkst (fx := ri_fq X) regs1 (Z_to_bv 64 (BASE + 14516)) memc1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn3h_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn3h_rA. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply K6. lia.
  - apply pairwise_disjoint_of_extents. unfold rbn3h_rA, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold rbn3h_fa0. split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite B9, B22. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; lia. }
assert (NE25 : (25%bv : bv 5) <> 0%bv)
  by (intro Hx; apply (f_equal bv_unsigned) in Hx; vm_compute in Hx; discriminate Hx).
assert (HS : st_ok_pi (fx := ri_fq X) SEGS VAL E
  (mkSS (ss_pc rbn3h_ss0) (sr_set (ss_regs rbn3h_ss0) (25%bv : bv 5) (SLit 0)) (ss_mem rbn3h_ss0)
     (ss_resv rbn3h_ss0) (ss_facts rbn3h_ss0))
  (restrict (w_H W1) (mkst (fx := ri_fq X) regs1 (Z_to_bv 64 (BASE + 14516)) memc1 (seg_rom SEGS)))).
{ apply (st_ok_pi_set_reg E rbn3h_ss0 _ (25%bv : bv 5) (SLit 0) HS0 NE25).
  cbn [ms_regs restrict mkst sv_denot]. rewrite R25, Hs0. reflexivity. }
clear HS0.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : sh_ok SEGS rbn3h_Bx (@nil shent) E (mrestrict (w_H W1) memc1)) by constructor.
clear HE.
unfold rbn_cfg, cfg_at.
replace (BASE + AF_both3_reac_box_name + RBN_P3) with (BASE + 14516)
  by (unfold AF_both3_reac_box_name, RBN_P3; lia).
change (w64 (BASE + 14516)) with (Z_to_bv 64 (BASE + 14516)).
pose (RUNTO := paj_run_to (fx := ri_fq X) B LAWS).
paj_run_to_tok RUNTO HS HJ1 SHOK rbn3h_span 14552.
{ rbn3h_awr X B9. }
rbn3h_kw X HFr B9 KW.
assert (Ei : ew E 12 = Z_to_bv 64 (ri_i X)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (Eo : ew E 13 = Z_to_bv 64 (ri_o X)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
rbn3h_cells X HS Ei Eo V40 V48.
rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let G27 := fresh "G27" in
  pose proof (st_ok_pi_restrict_reg (w_H W1) Ex ssx msx (27%bv : bv 5) HS) as G27;
  replace (sr_get (ss_regs ssx) (27%bv : bv 5)) with (SOff 27 0) in G27 by (vm_compute; reflexivity);
  cbn [ms_regs restrict mkst sv_denot ew ewset Nat.eqb] in G27; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in G27;
  rewrite (EE 27%nat 27%bv eq_refl) in G27 end.
apply SRr_ret. pmkst HS. left.
lazymatch goal with |- rbn3_atQ _ _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) =>
  exists pos, rr, lyc1, Sc1, mm, dd end.
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + RBN_Q3) with (BASE + 14552)
    by (unfold AF_both3_reac_box_name, RBN_Q3; lia).
  reflexivity. }
refine (rbn3h_finQ X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ HX H3 HJ1 KW HG Hkl _ V40 V48 (or_introl Hs0)).
exact G27.
Qed.
Theorem rbn3h_h1 : rbn3_h1_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3.
destruct (Z.eq_dec (ri_said X) 0) as [Hz | Hn];
  [exact (rbn3h_h1_z X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3 Hz)
  | exact (rbn3h_h1_s X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3 Hn)].
Qed.
Lemma rbn3h_img : forall X, rbn_cx B X -> rbn_img B (ri_W X) (ri_memc X).
Proof. intros X HX. unfold rbn_cx in HX. tauto. Qed.
Lemma rbn3h_frng : forall X, rbn_cx B X -> -2 ^ 31 <= ri_f X < 2 ^ 31.
Proof. intros X HX. unfold rbn_cx in HX. tauto. Qed.
Ltac rbn3h_nowr :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw);
  lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia | ]);
  destruct Hr.
Ltac rbn3h_g25 HS an tn Ean G25 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx (25%bv : bv 5) HS) as G25;
    replace (sr_get (ss_regs ssx) (25%bv : bv 5)) with (SOff an 0) in G25 by (vm_compute; reflexivity);
    cbn [ms_regs restrict mkst] in G25;
    rewrite (rbn3h_den_mod Ex an tn Ean) in G25
  end.
Ltac rbn3h_fin2 X pos lyc1 Sc1 W1 regs1 memc1 mdc1 HS HQ HJx HMR Hkl G25 :=
  apply SRr_ret; pmkst HS;
  lazymatch goal with |- rbn3_atT _ _ _ (mkCfg (mkst ?rr _ ?mm _) ?dd) =>
    lazymatch type of G25 with getr _ _ = _ ?Pv =>
      exists pos, rr, lyc1, Sc1, mm, dd, Pv end end;
  split;
  [ unfold rbn_cfg, cfg_at, w64;
    replace (BASE + AF_both3_reac_box_name + RBN_T3) with (BASE + 14612)
      by (unfold AF_both3_reac_box_name, RBN_T3; lia);
    reflexivity
  | refine (rbn3h_finT2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ _ _ _ HQ HJx HMR Hkl G25 _) ].
Hypothesis TAB : rbn3_tab_stmt B.
Lemma rbn3h_h2_core : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn3_stQ B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_Q3 regs1 memc1 mdc1) (rbn3_atT B X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HQ.
pose proof HQ as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R27 & R21 & R24 & R26 & R14 & R15 &
  HC & Hsd & HA).
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
destruct (rbn3h_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn3h_img X HX) as (t1 & t2 & t3 & HT8 & HTimg & _ & TM1 & TM2 & TM3 & _).
pose proof (rbn3h_frng X HX) as HFR.
destruct (TAB X pos lyc1 Sc1 W1 memc1 mdc1 HX HA (rbn3_rel_of_mid B X pos lyc1 Sc1 W1 memc1 mdc1 _ HM))
  as [TRA TV].
assert (V1 : val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 26)) 8 (t1 mod 2 ^ 64)).
{ apply (proj2 (rbn3h_vm8_mod _ _ _)).
  replace (VAL (A_OBJ 26)) with (VAL (A_OBJ 26) + 8 * 0) by lia. apply (TV 0 t1); [lia|].
  replace (VAL (A_OBJ 26) + 8 * 0) with (VAL (A_OBJ 26)) by lia. exact TM1. }
assert (V2 : val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 26) + 8) 8 (t2 mod 2 ^ 64)).
{ apply (proj2 (rbn3h_vm8_mod _ _ _)).
  replace (VAL (A_OBJ 26) + 8) with (VAL (A_OBJ 26) + 8 * 1) by lia. apply (TV 1 t2); [lia|].
  replace (VAL (A_OBJ 26) + 8 * 1) with (VAL (A_OBJ 26) + 8) by lia. exact TM2. }
assert (V3 : val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 26) + 16) 8 (t3 mod 2 ^ 64)).
{ apply (proj2 (rbn3h_vm8_mod _ _ _)).
  replace (VAL (A_OBJ 26) + 16) with (VAL (A_OBJ 26) + 8 * 2) by lia. apply (TV 2 t3); [lia|].
  replace (VAL (A_OBJ 26) + 8 * 2) with (VAL (A_OBJ 26) + 16) by lia. exact TM3. }
assert (P1 : val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26)) 8 (t1 mod 2 ^ 64))
  by (apply (proj2 (rbn3h_vm8_mod _ _ _)); exact TM1).
assert (P2 : val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 8) 8 (t2 mod 2 ^ 64))
  by (apply (proj2 (rbn3h_vm8_mod _ _ _)); exact TM2).
assert (P3 : val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 16) 8 (t3 mod 2 ^ 64))
  by (apply (proj2 (rbn3h_vm8_mod _ _ _)); exact TM3).
pose proof (pa_segs_low (VAL (A_OBJ 26)) (HTimg (VAL (A_OBJ 26)) ltac:(lia))) as HL0.
pose proof (pa_segs_low (VAL (A_OBJ 26) + 23) (HTimg (VAL (A_OBJ 26) + 23) ltac:(lia))) as HL23.
pose proof (pa_img_range (VAL (A_OBJ 26)) (HTimg (VAL (A_OBJ 26)) ltac:(lia))) as HI0.
pose proof (pa_img_range (VAL (A_OBJ 26) + 23) (HTimg (VAL (A_OBJ 26) + 23) ltac:(lia))) as HI23.
remember (Eimg (Ereg regs1 (map (Z_to_bv 64) [t1; t2; t3]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (map (Z_to_bv 64) [t1; t2; t3])) E)
  by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 t1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 t2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 t3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E26 : ew E (A_OBJ 26) = Z_to_bv 64 (VAL (A_OBJ 26)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E27o : ew E (A_OBJ 27) = Z_to_bv 64 (VAL (A_OBJ 27)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (B26 : bv_unsigned (ew E (A_OBJ 26)) = VAL (A_OBJ 26))
  by (rewrite E26; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 26)); lia).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (B22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E27 : ew E 27 = Z_to_bv 64 (ri_f X)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (HS0 : st_ok_pi (fx := ri_fq X) SEGS VAL E rbn3h_ss2
  (restrict (w_H W1) (mkst (fx := ri_fq X) regs1 (Z_to_bv 64 (BASE + 14552)) memc1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn3h_ss2. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn3h_rT. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B26. split; [lia|]. split; [unfold YImgTop.IMG_TOP in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 26)) 0 8 (SOff 32 0) (t1 mod 2 ^ 64));
      [ exact (rbn3h_den_mod E 32 t1 E32)
      | change (8 * Z.of_N 8) with 64; pose proof (Z.mod_pos_bound t1 (2 ^ 64) ltac:(lia)); lia
      | zside |].
      change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact V1.
    + apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 26)) 8 8 (SOff 33 0) (t2 mod 2 ^ 64));
      [ exact (rbn3h_den_mod E 33 t2 E33)
      | change (8 * Z.of_N 8) with 64; pose proof (Z.mod_pos_bound t2 (2 ^ 64) ltac:(lia)); lia
      | zside |].
      change (N.to_nat 8) with 8%nat. exact V2.
    + apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 26)) 16 8 (SOff 34 0) (t3 mod 2 ^ 64));
      [ exact (rbn3h_den_mod E 34 t3 E34)
      | change (8 * Z.of_N 8) with 64; pose proof (Z.mod_pos_bound t3 (2 ^ 64) ltac:(lia)); lia
      | zside |].
      change (N.to_nat 8) with 8%nat. exact V3.
  - apply pairwise_disjoint_of_extents. unfold rbn3h_rT, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold rbn3h_fa2. split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite B22, B26. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok SEGS rbn3h_Bx rbn3h_SH2 E (mrestrict (w_H W1) memc1)).
{ unfold sh_ok, rbn3h_SH2. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) memc1 E rbn3h_Bx (A_OBJ 26) (VAL (A_OBJ 26)) 24
    (VAL (A_OBJ 26)) 0 24 TRA).
  - unfold rbn3h_Bx. apply (U_atom E 22 SHADOW_OFF E22). unfold SHADOW_OFF; lia.
  - apply (U_atom E (A_OBJ 26) (VAL (A_OBJ 26)) E26). pose proof (pa_val_range (A_OBJ 26)); lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia. }
clear HE.
unfold rbn_cfg, cfg_at.
replace (BASE + AF_both3_reac_box_name + RBN_Q3) with (BASE + 14552)
  by (unfold AF_both3_reac_box_name, RBN_Q3; lia).
change (w64 (BASE + 14552)) with (Z_to_bv 64 (BASE + 14552)).
pose (RUN := paj_run (fx := ri_fq X) B LAWS).
pose (RUNTO := paj_run_to (fx := ri_fq X) B LAWS).
pose (BR := paj_branch (fx := ri_fq X) (PI := PI)).
assert (NE27 : (27%bv : bv 5) <> 0%bv)
  by (intro Hx; apply (f_equal bv_unsigned) in Hx; vm_compute in Hx; discriminate Hx).
assert (Hcase : ri_f X = 1 \/ ri_f X = 2 \/ ri_f X = 3 \/ (ri_f X <> 1 /\ ri_f X <> 2 /\ ri_f X <> 3)) by lia.
destruct Hcase as [Hf1 | [Hf2 | [Hf3 | (N1 & N2 & N3)]]].
- pose proof (st_ok_pi_set_reg E rbn3h_ss2 _ (27%bv : bv 5) (SLit 1) HS0 NE27
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R27, Hf1; reflexivity)) as HS. clear HS0.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  paj_run_to_tok RUNTO HS HJ1 SHOK rbn3h_span 14612.
  { rbn3h_awr X B26. }
  assert (HMR : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) memc1 x)
    by (intros x; apply HFr; rbn3h_nowr).
  rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
  rbn3h_g25 HS 32%nat t1 E32 G25.
  rbn3h_fin2 X pos lyc1 Sc1 W1 regs1 memc1 mdc1 HS HQ HJ1 HMR Hkl G25.
  right. split; [exact Hsd|]. left.
  split; [exact Hf1|]. split; [pose proof (Z.mod_pos_bound t1 (2 ^ 64) ltac:(lia)); lia|]. exact P1.
- pose proof (st_ok_pi_set_reg E rbn3h_ss2 _ (27%bv : bv 5) (SLit 2) HS0 NE27
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R27, Hf2; reflexivity)) as HS. clear HS0.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  paj_run_to_tok RUNTO HS HJ1 SHOK rbn3h_span 14612.
  { rbn3h_awr X B26. }
  assert (HMR : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) memc1 x)
    by (intros x; apply HFr; rbn3h_nowr).
  rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
  rbn3h_g25 HS 33%nat t2 E33 G25.
  rbn3h_fin2 X pos lyc1 Sc1 W1 regs1 memc1 mdc1 HS HQ HJ1 HMR Hkl G25.
  right. split; [exact Hsd|]. right; left.
  split; [exact Hf2|]. split; [pose proof (Z.mod_pos_bound t2 (2 ^ 64) ltac:(lia)); lia|]. exact P2.
- pose proof (st_ok_pi_set_reg E rbn3h_ss2 _ (27%bv : bv 5) (SLit 3) HS0 NE27
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R27, Hf3; reflexivity)) as HS. clear HS0.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  paj_run_to_tok RUNTO HS HJ1 SHOK rbn3h_span 14612.
  { rbn3h_awr X B26. }
  assert (HMR : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) memc1 x)
    by (intros x; apply HFr; rbn3h_nowr).
  rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
  rbn3h_g25 HS 34%nat t3 E34 G25.
  rbn3h_fin2 X pos lyc1 Sc1 W1 regs1 memc1 mdc1 HS HQ HJ1 HMR Hkl G25.
  right. split; [exact Hsd|]. right; right; left.
  split; [exact Hf3|]. split; [pose proof (Z.mod_pos_bound t3 (2 ^ 64) ltac:(lia)); lia|]. exact P3.
- paj_run_tok RUN HS0 HJ1 SHOK rbn3h_span.
  { rbn3h_awr X B26. }
  rename HFr into HFrA. rename HS0 into HS. clear HF HG.
  psrr_branch_tok RUN BR HS SHOK rbn3h_span.
  + paj_run_to_tok RUNTO HS HJ1 SHOK rbn3h_span 14612.
    { rbn3h_awr X B26. }
    assert (HMR : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) memc1 x)
      by (intros x; rewrite (HFr x ltac:(rbn3h_nowr)); apply HFrA; rbn3h_nowr).
    rbn3h_kept HS HAE regs1 rbn3h_kl Hkl.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
      let G25 := fresh "G25" in
      pose proof (st_ok_pi_restrict_reg (w_H W1) Ex ssx msx (25%bv : bv 5) HS) as G25;
      replace (sr_get (ss_regs ssx) (25%bv : bv 5)) with (SOff (A_OBJ 27) 0) in G25
        by (vm_compute; reflexivity);
      cbn [ms_regs restrict mkst] in G25;
      rewrite (rbn3h_den_mod Ex (A_OBJ 27) (VAL (A_OBJ 27)) E27o) in G25;
      rewrite (Z.mod_small (VAL (A_OBJ 27)) (2 ^ 64)) in G25
        by (pose proof (pa_val_range (A_OBJ 27)); lia);
      rbn3h_fin2 X pos lyc1 Sc1 W1 regs1 memc1 mdc1 HS HQ HJ1 HMR Hkl G25 end.
    right. split; [exact Hsd|]. right; right; right.
    split; [exact N1|]. split; [exact N2|]. split; [exact N3 | reflexivity].
  + exfalso. lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ex _) = _ =>
      assert (F27 : ew Ex 27 = Z_to_bv 64 (ri_f X)) by (cbn [ew ewset Nat.eqb]; exact E27);
      destruct (rbn3h_bad Ex (ri_f X) F27 ltac:(lia) Hc) as [Q | [Q | Q]]; lia end.
Qed.
Theorem rbn3h_h2 : rbn3_h2_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HQ.
exact (rbn3h_h2_core X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HQ).
Qed.
End h.
End f.
End d.
