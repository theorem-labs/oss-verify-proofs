(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACgc.v:176-178;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjv.v:45-51, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:154-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg3.v, with its numbers changed; 298 of its 407 lines of code are new or changed and 2431 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn4_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn4_keep_get : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  rbn_keep_regs regs regs2 cl -> existsb (Z.eqb (bv_unsigned r)) cl = false -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r HK Hb.
pose proof (u5_range r) as Hr.
assert (Hn : ~ In (bv_unsigned r) cl).
{ intros Hin. assert (E : existsb (Z.eqb (bv_unsigned r)) cl = true)
    by (apply existsb_exists; exists (bv_unsigned r); split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in Hb. discriminate. }
pose proof (HK _ Hr Hn) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn4_out_get : forall (regs2 : bvmap 5 word) (r : bv 5) v,
  getr regs2 (Z_to_bv 5 (bv_unsigned r)) = v -> getr regs2 r = v.
Proof. intros regs2 r v H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn4_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
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
Lemma rbn4_amem_shadow : forall x a n, amem_range a n -> 0 <= a -> a <= x < a + n ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg.
Proof.
intros x a n Ham Ha Hx. unfold shadow_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn4_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn4_locs4_rng : forall X pos a n v, In (a, n, v) (rbn_locs4 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 180.
Proof.
intros X pos a n v H. unfold rbn_locs4 in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn4_w4_len : forall X, rbm_args X -> length (rbm_w4 X) = 4%nat.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
exact (bn_w4_length _ _ Hi Ho).
Qed.
Lemma rbn4_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn4_cstr_fw : forall (W : world SEGS) (m m' : word -> option byte) a s F,
  rbn_cstr W m a s -> F mod 8 = 0 ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> ~ (F <= x < F + 512)) ->
  (forall x, F <= x < F + 512 -> x < kLowShadowBeg \/ kHighMemBeg <= x) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (F <= x < F + 512) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  rbn_cstr W m' a s.
Proof.
intros W m m' a s F (Hf & Hlen & Ha0 & Ham & Hg & Hra & Hhv & Htl) HF8 Hdis Happ HE.
assert (Hub : a + Z.of_nat (length s) + 8 <= 2 ^ 47)
  by (clear - Ham; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
assert (Hsb : forall x, a <= x < a + Z.of_nat (length s) + 1 ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg)
  by (intros x Hx; exact (rbn4_amem_shadow x a _ Ham ltac:(lia) ltac:(lia))).
assert (Hout : forall y, kLowShadowBeg <= y < kHighMemBeg -> 0 <= y < 2 ^ 64 /\ ~ (F <= y < F + 512)).
{ intros y Hy. split; [unfold kLowShadowBeg, kHighMemBeg in Hy; lia|]. intros Hy'.
  destruct (Happ y Hy'); lia. }
split; [exact Hf|]. split; [exact Hlen|]. split; [exact Ha0|]. split; [exact Ham|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HE; [lia|]. apply Hdis. lia. }
split.
{ intros x Hx. destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs.
  destruct (Hsb x ltac:(lia)) as [S1 S2].
  assert (Hq : kLowShadowBeg <= shadow_addr x < kHighMemBeg) by (unfold kLowShadowBeg, SHADOW_OFF in *; lia).
  destruct (Hout _ Hq) as [O1 O2].
  rewrite (HE _ O1 O2). exact Hs. }
split.
{ intros sx Hsx. destruct (Hsb a ltac:(lia)) as [S1 _].
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Hsx by lia.
  destruct (Hsb (a + Z.of_nat (length s)) ltac:(lia)) as [_ S2].
  pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (shadow_addr (a + Z.of_nat (length s))) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (shadow_addr (a + Z.of_nat (length s))) 8 ltac:(lia)) as M2.
  assert (Hq : kLowShadowBeg <= sx < kHighMemBeg) by (unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia).
  destruct (Hout _ Hq) as [O1 O2].
  rewrite (HE _ O1 O2). apply Hhv.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) by lia. exact Hsx. }
intros x Hx.
pose proof (Z.div_mod (a + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Hdis (a + Z.of_nat (length s)) ltac:(lia)) as Hy.
assert (O2 : ~ (F <= x < F + 512)) by lia.
rewrite (HE x ltac:(lia) O2). exact (Htl x Hx).
Qed.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn4_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM c p.
destruct HM as (_ & (_ & L1 & _) & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F1. reflexivity.
Qed.
Lemma rbn4_A_rng : forall X, rbn_cx B G X ->
  alloc_ceiling + 8496 <= rbn_SP X /\ rbn_SP X - 319 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X <= 2 ^ 47.
Proof.
intros X HX. destruct HX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
lia.
Qed.
Lemma rbn4_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
pose proof (rbn4_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM 3 pos) as FA.
destruct HM as (_ & HJ1 & _). pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
Qed.
Lemma rbn4_mid_fw : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 sh D n,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  Z.of_nat (length sh) <= 64 ->
  rbn_F X pos <= D -> 0 <= n -> D + n <= rbn_F X pos + 504 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D <= a < D + n) -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 sh D n HX HM HJ2 Hsh HD0 Hn HDn HEQ.
pose proof (rbn4_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as FA.
destruct (rbn4_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn4_A_rng X HX) as (AR1 & AR2 & AR3 & AR4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HFrm : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) by (intros a Ha Hf; apply HEQ; lia).
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof HM as (HW1 & HJ1 & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
unfold rbn_mid. split; [exact HW1|]. split; [exact HJ2|]. split; [exact Hperm|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (HFrm a) by (try lia; intros Hf; exact (proj2 (HFpr a Hf) Hia)). exact (Hro a Hro0 Ho He). }
split.
{ unfold rbn_kept in HK |- *. intros a Hfp (q & N & Hq & Hqa) He.
  assert (Hq1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hq).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hq1) as (_ & Hb4 & Hbc & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hq1 Hin3) as Hd.
  rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hj : q <= a < q + req_size N) by (clear - Hqa; unfold req_size; destruct (Z.eqb_spec N 0); lia).
  rewrite (HFrm a) by lia. exact (HK a Hfp (ex_intro _ q (ex_intro _ N (conj Hq Hqa))) He). }
split.
{ unfold rbn_frame in Hfr |- *. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact (Hfr j r Hj)].
  intros k Hk. apply HFrm; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact Hfl].
  intros k Hk. apply HEQ; lia. }
unfold rbn_shadow_at in Hsh0 |- *. intros j Hj.
pose proof (rbn4_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
rewrite (HFrm (shadow_addr (rbn_F X pos) + j))
  by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ _ Hf); lia]).
exact (Hsh0 j Hj).
Qed.
Lemma rbn4_lbuf_fr : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh j c,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  0 <= j -> 0 <= c -> j + c <= Z.of_nat (length sh) -> j + c <= 64 ->
  (forall i, j <= i < j + c -> nth (Z.to_nat i) sh 0 = 0) ->
  rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1 memc1
    (rbn_F X pos + 8 * j) (8 * c).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh j c HM Hj Hc Hl H64 Hz.
pose proof (rbn4_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM 3 pos) as FA.
destruct (rbn4_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
split; [lia|]. split; [lia|]. split.
{ apply (in_app_sub _ _ _ _ HFapp); lia. }
split.
{ apply zero_shadow_range.
  - replace (rbn_F X pos + 8 * j) with (rbn_F X pos + j * 8) by lia. rewrite Z.mod_add by lia. exact HF8.
  - replace (8 * c) with (c * 8) by lia. apply Z.mod_mul. lia.
  - intros i Hi. replace (8 * c / 8) with c in Hi by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    rewrite shadow_of_addr_add8. change (shadow_of_addr SHADOW_OFF (rbn_F X pos)) with (rbn_SH X pos).
    replace (rbn_SH X pos + j + i) with (rbn_SH X pos + (j + i)) by lia.
    rewrite (Hsh0 (j + i)) by lia. rewrite (Hz (j + i)) by lia. reflexivity. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rbn4_hi_kept : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh (mem2 : word -> option byte),
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  forall l, (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> rbn_A X + 8 <= a + k < rbn_A X + 180) ->
  rbn_cells (mrestrict (w_H W1) memc1) l -> rbn_cells (mrestrict (w_H W1) mem2) l.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh mem2 HX HM HE l Hl.
destruct (rbn4_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM) as (HF4096 & HFceil & _).
destruct (rbn4_A_rng X HX) as (AR1 & AR2 & AR3 & AR4).
apply rbn4_cells_kept. intros a n v k Hin Hk. pose proof (Hl a n v k Hin Hk). apply HE; lia.
Qed.
Hypothesis L1F : rbn_L1_fits B.
Hypothesis L1O : rbn_L1_ovf B.
Lemma rbn4_post : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs2 mem2 md2,
  rbn_cx B G X -> rbn_st4 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  rbn_keep_regs regs1 regs2 [5; 10; 11; 13; 15; 16; 17; 24; 30] ->
  getr regs2 (Z_to_bv 5 24) = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
  getr regs2 (Z_to_bv 5 30) = w64 (rbm_ovf 23 (rbm_stem X)) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 64 + Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  garr8 SEGS (mrestrict (w_H W1) mem2) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) ->
  rbn_st5 B X pos regs2 lyc1 Sc1 W1 mem2 md2 P.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs2 mem2 md2 HX H4 HJ2 HK O24 O30 HEQ HG.
destruct H4 as (HM & HRB & R18 & R26 & R20 & R23 & R25 & R27 & R24 & R30 & R15 & R13 & R10 & R14 & R12 &
  HC & HW4 & HSTP & HA).
destruct (rbn4_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
assert (Hl23 : Z.of_nat (length (firstn 23 (rbm_stem X))) <= 23)
  by (pose proof (firstn_le_length 23 (rbm_stem X)); lia).
assert (HFrm : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) by (intros a Ha Hf; apply HEQ; lia).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof (rbn4_w4_len X HA) as Hw4.
assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [5; 10; 11; 13; 15; 16; 17; 24; 30] = false ->
  getr regs2 r = getr regs1 r) by (intros r Hr; exact (rbn4_keep_get regs1 regs2 _ r HK Hr)).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
unfold rbn_st5. split.
{ apply (rbn4_mid_fw X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 _ (rbn_F X pos + 64)
    (Z.of_nat (length (firstn 23 (rbm_stem X)))) HX HM HJ2);
  [rewrite rbn4_sh_len; lia | lia | lia | lia | exact HEQ]. }
split.
{ unfold rbn_rbase.
  split; [rewrite KG by reflexivity; exact B2|]. split; [rewrite KG by reflexivity; exact B3|].
  split; [rewrite KG by reflexivity; exact B4|]. split; [rewrite KG by reflexivity; exact B8|].
  split; [rewrite KG by reflexivity; exact B9|]. split; [rewrite KG by reflexivity; exact B19|].
  rewrite KG by reflexivity; exact B22. }
split; [rewrite KG by reflexivity; exact R18|]. split; [rewrite KG by reflexivity; exact R26|].
split; [rewrite KG by reflexivity; exact R20|]. split; [rewrite KG by reflexivity; exact R23|].
split; [rewrite KG by reflexivity; exact R25|]. split; [rewrite KG by reflexivity; exact R27|].
split; [apply rbn4_out_get; exact O24|]. split; [apply rbn4_out_get; exact O30|].
split; [rewrite KG by reflexivity; exact R12|].
split.
{ apply (rbn4_hi_kept X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem2 HX HM HFrm); [|exact HC].
  intros a n0 v k Hin Hk. pose proof (rbn4_locs4_rng X pos a n0 v Hin). lia. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HW4|]. intros x Hx.
  rewrite length_app, Hw4 in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HEQ; lia. }
split; [exact HG|].
split; [|exact HA].
unfold rbn_stp in HSTP |- *. destruct HSTP as [Hstr Hdis]. split; [|exact Hdis].
apply (rbn4_cstr_fw W1 memc1 mem2 _ _ (rbn_F X pos) Hstr HF8); [| exact Happ | exact HFrm].
intros x Hx. exact (proj2 (Hdis x Hx)).
Qed.
Theorem rbn_seg4 : rbn_seg4_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H4.
pose proof H4 as (HM & HRB & R18 & R26 & R20 & R23 & R25 & R27 & R24 & R30 & R15 & R13 & R10 & R14 & R12 &
  HC & HW4 & HSTP & HA).
destruct (rbn4_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
unfold rbn_stp, rbn_cstr in HSTP. destruct HSTP as ((Hfs & Hlen & HP0 & Ham & Hgs & HPra & _) & Hdis).
pose proof (rbn4_stem_ne X) as Hne.
set (s := rbm_stem X) in *.
assert (Hub : P + Z.of_nat (length s) + 8 <= 2 ^ 47)
  by (clear - Ham; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (Hsrc : rbn_lsrc W1 memc1 P (s ++ [0])).
{ split; [exact Hgs|]. split; [lia|]. rewrite length_app. cbn [length].
  replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. split; [lia|].
  split; [lia|]. exact HPra. }
assert (Hbuf : rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1
  memc1 (rbn_F X pos + 64) 24).
{ exact (rbn4_lbuf_fr X pos lyc1 Sc1 W1 memc1 mdc1 _ _ 8 3 HM ltac:(lia) ltac:(lia)
    ltac:(rewrite rbn4_sh_len; lia) ltac:(lia)
    ltac:(intros i Hi; assert (i = 8 \/ i = 9 \/ i = 10) as [-> | [-> | ->]] by lia; reflexivity)). }
assert (Hsep : P + Z.of_nat (length s) + 1 <= rbn_F X pos + 64 \/ rbn_F X pos + 64 + 24 <= P).
{ destruct (Z_lt_le_dec P (rbn_F X pos)) as [Hlt | Hge].
  - left. destruct (Z_lt_le_dec (P + Z.of_nat (length s)) (rbn_F X pos)) as [Hl | Hl]; [lia|].
    exfalso. apply (proj2 (Hdis (rbn_F X pos) ltac:(lia))). lia.
  - right. destruct (Z_lt_le_dec P (rbn_F X pos + 512)) as [Hl | Hl]; [|lia].
    exfalso. apply (proj2 (Hdis P ltac:(lia))). lia. }
pose proof HM as (_ & HJ1 & _).
change RBN_P4 with RBN_L1.
assert (POST : forall nF ovF wr W2 c2, rbn_lpost B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X)
    (ri_W X) (ri_memc X) (ri_mdc X) [(3, pos)] lyc1 Sc1 W1 memc1 0 regs1 RBN_L1X
    [5; 10; 11; 13; 15; 16; 17; 24; 30] (rbn_F X pos + 64) 0 wr [(24, nF); (30, ovF)] W2 c2 ->
  nF = Z.of_nat (length (firstn 23 s)) -> ovF = rbm_ovf 23 s -> wr = firstn 23 s -> rbn_at5 B X W2 c2).
{ intros nF ovF wr W2 c2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HK & HO & HEQ & HG) -> -> ->.
  pose proof (Forall_inv HO) as O24. pose proof (Forall_inv (Forall_inv_tail HO)) as O30.
  cbn [fst snd] in O24, O30. rewrite Z.add_0_r in HEQ, HG.
  exists pos, regs2, lyc1, Sc1, mem2, md2, P. split; [reflexivity|].
  exact (rbn4_post X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs2 mem2 md2 HX H4 HJ2 HK O24 O30 HEQ HG). }
destruct (Z_le_gt_dec (Z.of_nat (length s)) 23) as [Hf | Ho].
- pose proof (L1F REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 mdc1 0 regs1 P (rbn_F X pos + 64) 0 0 s ltac:(lia)) as R.
  unfold rbn_L1_run in R.
  eapply SRr_mono; [apply R; first [exact HJ1 | exact Hne | exact Hfs | exact Hsrc | exact Hbuf | exact Hsep
    | lia | left; reflexivity | assumption] |].
  intros W2 c2 _ Hp. apply (POST _ _ _ _ _ Hp).
  + rewrite firstn_all2 by lia. lia.
  + unfold rbm_ovf. replace (23 <? Z.of_nat (length s)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + rewrite firstn_all2 by lia. reflexivity.
- pose proof (L1O REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 mdc1 0 regs1 P (rbn_F X pos + 64) 0 0 s ltac:(lia)) as R.
  unfold rbn_L1_run in R.
  eapply SRr_mono; [apply R; first [exact HJ1 | exact Hne | exact Hfs | exact Hsrc | exact Hbuf | exact Hsep
    | lia | left; reflexivity | assumption] |].
  intros W2 c2 _ Hp. apply (POST _ _ _ _ _ Hp).
  + rewrite firstn_length_le by lia. lia.
  + unfold rbm_ovf. replace (23 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  + reflexivity.
Qed.
End h.
End f.
End d.
