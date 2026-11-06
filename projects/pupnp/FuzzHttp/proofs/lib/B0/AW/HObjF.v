(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HttpRepA AWKit HObjA HObjK.
Import ListNotations.
Open Scope Z_scope.

Lemma SB_mod8 : forall k, SB_of k mod 8 = 0.
Proof.
  intros k. unfold SB_of. destruct k as [|p|p]; [reflexivity| |reflexivity].
  do 4 (try destruct p as [p|p|]); reflexivity.
Qed.

Section W.
Context {HC : HasCeiling}.
  Variable FI : fs_if.
  Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

  #[using="Type"] Lemma fsw_FSIV : forall W, app_ivs W -> Forall (fsw_iv FI) (FSIV W).
  Proof.
    intros W AW. pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4 & F5).
    constructor; [left; unfold app_iv, SH_HI; cbn [fst snd]; lia|].
    constructor; [right; cbn [fst snd]; lia|].
    eapply Forall_impl; [| exact AW]. intros iv H. left. exact H.
  Qed.
  #[using="Type"] Lemma fsw_cons_app : forall iv W, app_iv iv -> Forall (fsw_iv FI) W -> Forall (fsw_iv FI) (iv :: W).
  Proof. intros iv W H HW. constructor; [left; exact H| exact HW]. Qed.

  #[using="Type"] Lemma shw_fkeep : forall W st m m' X n,
    shw m X n -> fkeep FI W st m m' -> RFAKE FI st m -> lb (fs_live FI st) X n ->
    (forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside W a) -> shw m' X n.
  Proof.
    intros W st m m' X n SW FK RF (g & Hg & G1 & G2) OUT.
    pose proof (live_num FI st m RF) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4 & F5).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (SB_mod8 (ff_class g)) as S8. change (SB_of (ff_class g)) with (ff_shsize g) in S8.
    assert (ESG : sh (ff_addr g) = ff_addr g / 8 + 2147450880) by reflexivity.
    eapply (shw_band_eq m m' X n (sh (ff_addr g)) (sh (ff_addr g) + ff_shsize g) SW).
    - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (FK a _ _ _) Hv).
      + rewrite ESG in Ha. clear - Ha L1 L2 L6 F1 F2 ACR L7. Z.div_mod_to_equations. lia.
      + exists g. split; [exact Hg|]. right; left. exact Ha.
      + apply OUT. lia.
    - rewrite ESG. clear - L1 F1. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L1 L2 L6 L7 F1 F2 ACR. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L3. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L3 S8. Z.div_mod_to_equations. lia.
    - apply sh_mono. exact G1.
    - intros Hn. rewrite ESG. unfold sh, SHADOW_OFF. clear - G1 G2 L3 L6 Hn. Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma shw_fkeep0 : forall st m m' X n,
    shw m X n -> fkeep FI [] st m m' -> RFAKE FI st m -> lb (fs_live FI st) X n -> shw m' X n.
  Proof. intros st m m' X n SW FK RF LB. eapply shw_fkeep; eauto. intros a _. exact I. Qed.

  #[using="Type"] Lemma shz_frame_fs : forall W m m' lo hi,
    shz m lo hi -> SH_LO <= lo -> hi <= SH_HI -> munch W m m' -> Forall (fsw_iv FI) W ->
    (hi <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= lo) -> shz m' lo hi.
  Proof.
    intros W m m' lo hi Z H1 H2 MU HW OUT a Ha.
    assert (B : shband a) by (unfold shband; lia).
    rewrite (mrd_munch W m m' a MU (fsw_outside FI W a HW B ltac:(lia)) (shband_range a B)). apply Z. exact Ha.
  Qed.
  #[using="Type"] Lemma shr_frame_fs : forall W m m' lo hi,
    shr m lo hi -> SH_LO <= lo -> hi <= SH_HI -> munch W m m' -> Forall (fsw_iv FI) W ->
    (hi <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= lo) -> shr m' lo hi.
  Proof.
    intros W m m' lo hi R H1 H2 MU HW OUT a Ha.
    assert (B : shband a) by (unfold shband; lia).
    rewrite (mrd_munch W m m' a MU (fsw_outside FI W a HW B ltac:(lia)) (shband_range a B)). apply R. exact Ha.
  Qed.

  #[using="Type"] Lemma stack_window_lo : forall lo, alloc_ceiling <= lo ->
    SH_LO <= sh lo - sh lo mod 8 /\ sh (FSB FI) + A0_FS_SHSIZE <= sh lo - sh lo mod 8.
  Proof.
    intros lo H1. pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4 & F5).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold SH_LO, sh, SHADOW_OFF. clear F3 F5. split; Z.div_mod_to_equations; lia.
  Qed.
  #[using="Type"] Lemma stack_lo_ok : forall lo, sh lo - sh lo mod 8 <= sh lo.
  Proof. intros lo. pose proof (Z.mod_pos_bound (sh lo) 8 ltac:(lia)). lia. Qed.
  #[using="Type"] Lemma sh_hi_ok : forall q, q <= 2^47 -> sh q <= SH_HI.
  Proof. intros q H. unfold SH_HI, sh, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.
  #[using="Type"] Lemma sh_hi_ok8 : forall q, q <= 2^47 - 64 -> sh q + 8 <= SH_HI.
  Proof. intros q H. unfold SH_HI, sh, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

  #[using="Type"] Lemma shz_stack_fs : forall W m m' lo A B,
    shz m A B -> alloc_ceiling <= lo -> sh lo - sh lo mod 8 <= A -> B <= SH_HI -> munch W m m' -> Forall (fsw_iv FI) W -> shz m' A B.
  Proof.
    intros W m m' lo A B Z H1 H2 H3 MU HW. destruct (stack_window_lo lo H1) as (S1 & S2).
    eapply shz_frame_fs; [exact Z| lia| lia| exact MU| exact HW| right; lia].
  Qed.
  #[using="Type"] Lemma shr_stack_fs : forall W m m' lo A B,
    shr m A B -> alloc_ceiling <= lo -> sh lo - sh lo mod 8 <= A -> B <= SH_HI -> munch W m m' -> Forall (fsw_iv FI) W -> shr m' A B.
  Proof.
    intros W m m' lo A B Z H1 H2 H3 MU HW. destruct (stack_window_lo lo H1) as (S1 & S2).
    eapply shr_frame_fs; [exact Z| lia| lia| exact MU| exact HW| right; lia].
  Qed.

  #[using="Type"] Lemma lb_apart_new : forall st k m F SF FL X n, RFAKE FI st m -> 0 <= k <= 10 ->
    F = fs_F FI st k -> SF = sh F -> FL = fs_FL FI st k -> lb (fs_live FI st) X n ->
    X + n <= F \/ F + FB_of k <= X.
  Proof.
    intros st k m F SF FL X n RF Hk EF ES EL (g & Hg & G1 & G2).
    destruct (new_frame_facts FI st k m F SF FL RF Hk EF ES EL) as (_ & _ & _ & _ & _ & _ & AP).
    pose proof (proj1 (Forall_forall _ _) AP g Hg) as (P1 & _). lia.
  Qed.

  Variable AI : am_if FI.
  #[using="Type"] Lemma stack_hi_ok : forall q, q + 16 <= am_stack_top FI AI -> q <= 2^47.
  Proof. intros q H. pose proof (am_stack_ok FI AI) as (_ & _ & T3 & _). lia. Qed.
End W.
