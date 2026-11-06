(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_rgb_fuzzer/lib/YC07.v, with its module paths and module names changed; 421 of its 455 lines of code are new or changed and 223 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC1g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition rbn6_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 22; 24; 27; 29; 30].
Ltac rbn6_rget HR r H :=
  pose proof (HR r) as H;
  lazymatch type of H with _ = sv_denot ?E (sr_get ?s ?r') =>
    let e := eval vm_compute in (sr_get s r') in change (sr_get s r') with e in H end.
Ltac rbn6_runh pc stop H :=
  let r := eval vm_compute in (sym_run_toN_pi pl_tpi FUEL stop (mkSS pc sr_atoms [] None (mkFacts [] [] []))) in
  lazymatch r with (?ss', ?st) =>
    assert (H : sym_run_toN_pi pl_tpi FUEL stop (mkSS pc sr_atoms [] None (mkFacts [] [] [])) = (ss', st))
      by (vm_compute; reflexivity) end.
Lemma rbn6_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn6_out_get : forall (regs2 : bvmap 5 word) (r : bv 5) v,
  getr regs2 (Z_to_bv 5 (bv_unsigned r)) = v -> getr regs2 r = v.
Proof. intros regs2 r v H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma rbn6_sltu1 : forall E v, sv_denot E (SOff 13 0) = w64 v -> (v = 0 \/ v = 1) ->
  sv_denot E (SAlu Instr.ALU_SLTU (SOff 13 0) (SLit 1)) = w64 (1 - v).
Proof.
intros E v H [-> | ->];
change (sv_denot E (SAlu Instr.ALU_SLTU (SOff 13 0) (SLit 1)))
  with (alu64 Instr.ALU_SLTU (sv_denot E (SOff 13 0)) (Z_to_bv 64 1)); rewrite H; vm_compute; reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma rbn6_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
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
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn6_sv_off : forall (regs : bvmap 5 word) n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (Eimg (Ereg regs [])) (SOff n 0) = getr regs r.
Proof.
intros regs n r Hn. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Eimg_Ereg_nat. exact Hn.
Qed.
Lemma rbn6_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn6_locs4_rng : forall X pos a n v, In (a, n, v) (rbn_locs4 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 180.
Proof.
intros X pos a n v H. unfold rbn_locs4 in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn6_locs6_rng : forall X pos a n v, In (a, n, v) (rbn_locs6 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 180.
Proof.
intros X pos a n v H. unfold rbn_locs6 in H. apply in_app_or in H. destruct H as [H | H];
[exact (rbn6_locs4_rng X pos a n v H)|]. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn6_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn6_NB_ne : forall X, (1 <= length (rbm_NB X))%nat.
Proof.
intros X. assert (H : rbm_NM X <> []).
{ unfold rbm_NM, bn_NM. cbv zeta. pose proof (rbn6_stem_ne X) as Hne. unfold rbm_stem in Hne.
  match goal with |- (if ?b then _ else _) <> [] => destruct b end; [exact Hne|].
  destruct (bn_stem (ri_f X) (ri_sd X)); discriminate. }
unfold rbm_NB. destruct (rbm_NM X) as [|c l]; [exfalso; exact (H eq_refl)|]. cbn [firstn length]. lia.
Qed.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn6_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM c p.
destruct HM as (_ & (_ & L1 & _) & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F1. reflexivity.
Qed.
Lemma rbn6_A_rng : forall X, rbn_cx B G X ->
  alloc_ceiling + 8496 <= rbn_SP X /\ rbn_SP X - 319 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X <= 2 ^ 47.
Proof.
intros X HX. destruct HX as ((_ & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
lia.
Qed.
Lemma rbn6_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
pose proof (rbn6_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM 3 pos) as FA.
destruct HM as (_ & HJ1 & _). pose proof HJ1 as (HAR1 & _ & _ & _ & _ & Hfrs & _).
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
Lemma rbn6_mid_fw : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 sh D n,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  Z.of_nat (length sh) <= 64 ->
  rbn_F X pos <= D -> 0 <= n -> D + n <= rbn_F X pos + 504 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D <= a < D + n) -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 sh D n HX HM HJ2 Hsh HD0 Hn HDn HEQ.
pose proof (rbn6_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as FA.
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HFrm : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha Hf; apply HEQ; [exact Ha | clear - Hf HD0 HDn; lia]).
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. clear - Ha HFapp. lia. }
pose proof HM as (HW & HJ1 & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof HJ1 as (HAR1 & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
unfold rbn_mid. split; [exact HW|]. split; [exact HJ2|]. split; [exact Hperm|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (HFrm a); [exact (Hro a Hro0 Ho He) | clear - Hlow; lia |].
  intros Hf. exact (proj2 (HFpr a Hf) Hia). }
split.
{ intros a Hfp Hblk He. pose proof Hblk as (q & N & Hq & Hqa).
  assert (Hq1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hq).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hq1) as (_ & Hb4 & Hbc & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hq1 Hin3) as Hd.
  rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (HrN : N <= req_size N) by (unfold req_size; destruct (N =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
  rewrite (HFrm a); [exact (HK a Hfp Hblk He) | clear - Hqa Hb4 Hbc HrN C1; lia |].
  clear - Hqa HrN Hd. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact (Hfr j r Hj)].
  intros k Hk. apply HFrm; clear - Hk Hj13 AR1 AR4 HFceil C1; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact Hfl].
  intros k Hk. apply HEQ; clear - Hk HD0 HDn HFceil C1 HF4096; lia. }
unfold rbn_shadow_at. intros j Hj.
pose proof (rbn6_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
rewrite (HFrm (shadow_addr (rbn_F X pos) + j)).
- exact (Hsh0 j Hj).
- unfold kLowShadowBeg, kHighMemBeg in *. clear - Hb. lia.
- intros Hf. destruct (Happ _ Hf); unfold kLowShadowBeg, kHighMemBeg in *; clear - Hb H; lia.
Qed.
Lemma rbn6_lbuf_fr : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh j c,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  0 <= j -> 0 <= c -> j + c <= Z.of_nat (length sh) -> j + c <= 64 ->
  (forall i, j <= i < j + c -> nth (Z.to_nat i) sh 0 = 0) ->
  rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1 memc1
    (rbn_F X pos + 8 * j) (8 * c).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh j c HM Hj Hc Hl H64 Hz.
pose proof (rbn6_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM 3 pos) as FA.
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
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
Lemma rbn6_hi_kept : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh (mem2 : word -> option byte),
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  forall l, (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> rbn_A X + 8 <= a + k < rbn_A X + 180) ->
  rbn_cells (mrestrict (w_H W1) memc1) l -> rbn_cells (mrestrict (w_H W1) mem2) l.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh mem2 HX HM HE l Hl.
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM) as (HF4096 & HFceil & _).
destruct (rbn6_A_rng X HX) as (AR1 & AR2 & AR3 & AR4).
pose proof asan_consts as (C1 & _).
apply rbn6_cells_kept. intros a n v k Hin Hk. pose proof (Hl a n v k Hin Hk). apply HE; lia.
Qed.
Lemma rbn6_plain : forall (W : world SEGS) regs memc mdc pc0 n stop ss' st
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sym_run_toN_pi pl_tpi n stop (mkSS pc0 sr_atoms [] None (mkFacts [] [] [])) = (ss', st) ->
  pi_plain_stop st -> ss_resv ss' = None ->
  (forall regs' mat',
     (forall r, getr regs' r = sv_denot (Eimg (Ereg regs [])) (sr_get (ss_regs ss') r)) ->
     (forall r : bv 5, sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0) = true ->
        getr regs' r = getr regs r) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     SRr SEGS W (cfg_at SEGS (BASE + ss_pc ss') regs' memc (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + pc0) regs memc mdc) Q.
Proof.
intros W regs memc mdc pc0 n stop ss' st STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q HJ Hrun Hst Hrv HK.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (HA : env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])))
  by (split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc0 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc0)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat split. }
unfold cfg_at. change (w64 (BASE + pc0)) with (Z_to_bv 64 (BASE + pc0)).
eapply (SRr_run_to_pi_AJ B LAWS W n stop _ _ ss' st _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k Q
  HEI HS Hrun Hst HJ).
- apply awr_ok_nil.
- intros ms' mat' HS' HJ' HF _ _.
  assert (Hm : ms_mem ms' = memc) by exact (frame_of_read_only _ [] _ _ eq_refl HF).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv).
  rewrite Hm in HJ' |- *.
  apply (HK (ms_regs ms') mat'); [| |exact HJ'].
  + intros r. exact (st_ok_pi_restrict_reg _ _ _ _ r HS').
  + intros r Hr. apply (regs_kept_of_st_ok_pi _ _ _ regs [] [r] HS' HA); [|left; reflexivity].
    cbn [forallb]. rewrite Hr. reflexivity.
Qed.
Lemma rbn6_post : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs3 mem2 md3,
  rbn_cx B G X -> rbn_st6 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md3 0 ->
  (forall r, In r rbn6_keep -> getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  getr regs3 26 = w64 (Z.of_nat (length (rbm_TB X))) ->
  getr regs3 21 = w64 (rbm_tok X) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (rbn_F X pos + 128 <= a < rbn_F X pos + 128 + Z.of_nat (length (rbm_TB X))) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  garr8 SEGS (mrestrict (w_H W1) mem2) (rbn_F X pos + 128) (rbm_TB X) ->
  rbn_st7 B X pos regs3 lyc1 Sc1 W1 mem2 md3.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs3 mem2 md3 HX H6 HJ3 KK G26 G21 HEQ HG.
destruct H6 as (HM & HRB & R18 & R27 & R24 & R30 & R29 & HC & HNB & HA).
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
assert (HTB : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
assert (HFrm : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos <= a < rbn_F X pos + 512) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha Hf; apply HEQ; [exact Ha | clear - Hf HTB; lia]).
assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) rbn6_keep = true -> getr regs3 r = getr regs1 r).
{ intros r Hr. apply existsb_exists in Hr. destruct Hr as (x & Hx & Hxe). apply Z.eqb_eq in Hxe.
  rewrite <- Hxe in Hx. pose proof (KK _ Hx) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. }
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
unfold rbn_st7. split.
{ apply (rbn6_mid_fw X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md3 _ (rbn_F X pos + 128)
    (Z.of_nat (length (rbm_TB X))) HX HM HJ3); [rewrite rbn6_sh_len; lia | lia | lia | lia | exact HEQ]. }
split.
{ unfold rbn_rbase.
  split; [rewrite KG by reflexivity; exact B2|]. split; [rewrite KG by reflexivity; exact B3|].
  split; [rewrite KG by reflexivity; exact B4|]. split; [rewrite KG by reflexivity; exact B8|].
  split; [rewrite KG by reflexivity; exact B9|]. split; [rewrite KG by reflexivity; exact B19|].
  rewrite KG by reflexivity; exact B22. }
split; [rewrite KG by reflexivity; exact R18|]. split; [rewrite KG by reflexivity; exact R27|].
split; [rewrite KG by reflexivity; exact R24|]. split; [rewrite KG by reflexivity; exact R30|].
split; [rewrite KG by reflexivity; exact R29|].
split; [exact G26|]. split; [exact G21|].
split.
{ apply (rbn6_hi_kept X pos lyc1 Sc1 W1 memc1 mdc1 _ _ mem2 HX HM HFrm); [|exact HC].
  intros a n0 v k Hin Hk. pose proof (rbn6_locs6_rng X pos a n0 v Hin). lia. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HNB|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HEQ; lia. }
split; [exact HG | exact HA].
Qed.
Lemma rbn6_tail : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' nF ovF wr W2 c2,
  rbn_cx B G X -> rbn_st6 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall r, In r rbn6_keep -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  rbn_lpost B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 0 regs' RBN_L3X [5; 6; 7; 10; 11; 12; 13; 16; 17; 26; 28]
    (rbn_F X pos + 128) 0 wr [(26, nF); (13, ovF)] W2 c2 ->
  nF = Z.of_nat (length (rbm_TB X)) -> (ovF = 0 \/ ovF = 1) -> 1 - ovF = rbm_tok X -> wr = rbm_TB X ->
  SRr SEGS W2 c2 (rbn_at7 B X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' nF ovF wr W2 c2 HX H6 KK1
  (-> & regs2 & mem2 & md2 & -> & HJ2 & HK2 & HO & HEQ & HG) -> Hov Htok ->.
pose proof (Forall_inv HO) as O26. pose proof (Forall_inv (Forall_inv_tail HO)) as O13.
cbn [fst snd] in O26, O13. rewrite Z.add_0_r in HEQ, HG.
unfold rbn_cfg.
replace (BASE + AF_reac_box_name + RBN_L3X) with (BASE + 10368) by (unfold AF_reac_box_name, RBN_L3X; lia).
rbn6_runh 10368 10372 Hrun.
apply (rbn6_plain W1 regs2 mem2 md2 10368 FUEL 10372 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Hrun I eq_refl).
intros regs3 mat3 HR3 KP3 HJ3.
apply SRr_ret.
exists pos, regs3, lyc1, Sc1, mem2, (with_vm_backing (m_vm_lazy md2) mat3 md2). split.
{ unfold rbn_cfg. cbn [ss_pc].
  replace (BASE + AF_reac_box_name + RBN_P7) with (BASE + 10372) by (unfold AF_reac_box_name, RBN_P7; lia).
  reflexivity. }
assert (KK2 : forall r, In r rbn6_keep -> getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  apply HK2; [clear - Hr; lia|]. cbn [In]. clear - Hr. lia. }
assert (KK3 : forall r, In r rbn6_keep -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply KP3; vm_compute; reflexivity|]). destruct Hr. }
assert (H13 : sv_denot (Eimg (Ereg regs2 [])) (SOff 13 0) = w64 ovF).
{ rewrite (rbn6_sv_off regs2 13 13%bv eq_refl). apply rbn6_out_get. exact O13. }
rbn6_rget HR3 (21%bv : bv 5) G21. rewrite (rbn6_sltu1 _ ovF H13 Hov), Htok in G21.
assert (G26 : getr regs3 26 = w64 (Z.of_nat (length (rbm_TB X)))).
{ rewrite (KP3 26%bv) by (vm_compute; reflexivity). apply rbn6_out_get. exact O26. }
apply (rbn6_post X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs3 mem2 _ HX H6 HJ3); [| exact G26 | exact G21 | exact HEQ | exact HG].
intros r Hr. rewrite (KK3 r Hr), (KK2 r Hr). exact (KK1 r Hr).
Qed.
Hypothesis L3F : rbn_L3_fits B.
Hypothesis L3O : rbn_L3_ovf B.
Lemma rbn_seg6 : rbn_seg6_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H6.
pose proof H6 as (HM & HRB & R18 & R27 & R24 & R30 & R29 & HC & HNB & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn6_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
pose proof (rbn6_NB_ne X) as Hne.
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
destruct (proj1 (garr8_app SEGS _ _ _ _) HNB) as [HNBg _].
pose proof (garr8_bytes_ok SEGS _ _ _ HNBg) as Hby.
pose proof (rbn6_lbuf_fr X pos lyc1 Sc1 W1 memc1 mdc1 _ _ 8 3 HM ltac:(lia) ltac:(lia)
  ltac:(rewrite rbn6_sh_len; lia) ltac:(lia)
  ltac:(intros i Hi; assert (i = 8 \/ i = 9 \/ i = 10) as [-> | [-> | ->]] by lia; reflexivity)) as Hb64.
destruct Hb64 as (_ & _ & _ & Hra64 & _).
assert (Hsrc : rbn_lsrc W1 memc1 (rbn_F X pos + 64) (rbm_NB X)).
{ split; [exact HNBg|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply (range_addressable_sub _ _ (rbn_F X pos + 8 * 8) (8 * 3)); [exact Hra64 | lia | lia]. }
assert (Hbuf : rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1
  memc1 (rbn_F X pos + 128) 24).
{ exact (rbn6_lbuf_fr X pos lyc1 Sc1 W1 memc1 mdc1 _ _ 16 3 HM ltac:(lia) ltac:(lia)
    ltac:(rewrite rbn6_sh_len; lia) ltac:(lia)
    ltac:(intros i Hi; assert (i = 16 \/ i = 17 \/ i = 18) as [-> | [-> | ->]] by lia; reflexivity)). }
assert (Hsep : rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) <= rbn_F X pos + 128 \/
  rbn_F X pos + 128 + 24 <= rbn_F X pos + 64) by lia.
pose proof HM as (_ & HJ1 & _).
unfold rbn_cfg.
replace (BASE + AF_reac_box_name + RBN_P6) with (BASE + 10192) by (unfold AF_reac_box_name, RBN_P6; lia).
rbn6_runh 10192 10224 Hrun.
apply (rbn6_plain W1 regs1 memc1 mdc1 10192 FUEL 10224 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 Hrun I eq_refl).
intros regs' mat' HR KP HJ'.
cbn [ss_pc].
replace (BASE + 10224) with (BASE + AF_reac_box_name + RBN_L3) by (unfold AF_reac_box_name, RBN_L3; lia).
fold (rbn_cfg RBN_L3 regs' memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1)).
assert (KK1 : forall r, In r rbn6_keep -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. unfold rbn6_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply KP; vm_compute; reflexivity|]). destruct Hr. }
rbn6_rget HR (12%bv : bv 5) G12. rbn6_rget HR (26%bv : bv 5) G26. rbn6_rget HR (13%bv : bv 5) G13. rbn6_rget HR (14%bv : bv 5) G14.
rbn6_rget HR (15%bv : bv 5) G15. rbn6_rget HR (16%bv : bv 5) G16. rbn6_rget HR (10%bv : bv 5) G10. rbn6_rget HR (17%bv : bv 5) G17.
rewrite (rbn6_sv_off regs1 27 27%bv eq_refl), R27 in G16, G10.
rewrite (rbn6_sv_off regs1 24 24%bv eq_refl), R24 in G17.
assert (G29 : getr regs' 29 = w64 (rbn_F X pos + 128)) by (rewrite (KP 29%bv) by (vm_compute; reflexivity); exact R29).
assert (G22 : getr regs' 22 = w64 SHADOW_OFF) by (rewrite (KP 22%bv) by (vm_compute; reflexivity); exact B22).
destruct (Z_le_gt_dec (Z.of_nat (length (bn_TK (rbm_NB X)))) 23) as [Hf | Ho].
- pose proof (L3F REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) 0 regs' (rbn_F X pos + 64)
    (rbn_F X pos + 128) (rbm_NB X) Hf) as R.
  unfold rbn_L3_run in R.
  eapply SRr_bind; [apply R; first [exact HJ' | exact Hne | exact Hby | exact Hsrc | exact Hbuf | exact Hsep
    | assumption] |].
  intros W2 c2 _ Hp. apply (rbn6_tail X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' _ _ _ W2 c2 HX H6 KK1 Hp).
  + unfold rbm_TB. rewrite firstn_all2 by lia. reflexivity.
  + left; reflexivity.
  + unfold rbm_tok, rbm_ovf. replace (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))) with false
      by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + unfold rbm_TB. rewrite firstn_all2 by lia. reflexivity.
- pose proof (L3O REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 (with_vm_backing (m_vm_lazy mdc1) mat' mdc1) 0 regs' (rbn_F X pos + 64)
    (rbn_F X pos + 128) (rbm_NB X) ltac:(lia)) as R.
  unfold rbn_L3_run in R.
  eapply SRr_bind; [apply R; first [exact HJ' | exact Hne | exact Hby | exact Hsrc | exact Hbuf | exact Hsep
    | assumption] |].
  intros W2 c2 _ Hp. apply (rbn6_tail X pos regs1 lyc1 Sc1 W1 memc1 mdc1 regs' _ _ _ W2 c2 HX H6 KK1 Hp).
  + unfold rbm_TB. rewrite firstn_length_le by lia. reflexivity.
  + right; reflexivity.
  + unfold rbm_tok, rbm_ovf. replace (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))) with true
      by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  + reflexivity.
Qed.
End h.
End f.
End d.
