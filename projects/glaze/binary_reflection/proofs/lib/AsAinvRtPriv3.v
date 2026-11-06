(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section RtPriv.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.     (* [comment removed for export] *)
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.

  (* [comment removed for export] *)
  Theorem rt_priv_space : forall a, SBEG <= a < SBEG + KSPACE + PG ->
    (forall p n, In (p, n) Lc -> is_primary n = true -> ~ (p - rz n <= a < p - rz n + csize (blk_class n))) ->
    rt_priv IA Lc FF a.
  Proof using W qg qt st.
    intros a Ha NL.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). pose proof (img_lits bt st Lc FF W) as [I1 I2].
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
    split; [ulia|]. split; [ulia|].
    destruct (heap_not_shadowish bt st Lc FF W Lc a ltac:(intros p n H; exact H) ltac:(right; ulia)) as (N1 & N2 & N3 & N4).
    intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
    - destruct V as (p & n & Hin & Hpa).
      destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
      pose proof (up8_facts n ltac:(lia)) as (U1 & _).
      destruct E as [(HP & -> & -> & _) | (HP & sc & Hs & Eu & En & -> & ->)].
      + apply (NL p n Hin HP). lia.
      + destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
    - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
      destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)); ulia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_prim_chunk : forall p n, In (p, n) Lc -> is_primary n = true ->
    1 <= blk_class n <= 30 /\ carved bt st (blk_class n) (p - rz n) /\ in_live_c Lc (blk_class n) (p - rz n).
  Proof using W qg qt FF RUN.
    intros p n Hin HP. pose proof (live_chunk bt st Lc FF W p n Hin HP) as H. cbn zeta in H. unfold prim_alloc_beg in H.
    destruct H as (C1 & C2 & C3 & _). split; [exact C1|]. split; [exact C2 | exact C3].
  Qed.

  Theorem rt_priv_reginfo : forall c a, 1 <= c <= 30 -> reginfo bt c <= a < reginfo bt c + 128 -> rt_priv IA Lc FF a.
  Proof using W qg qt st.
    intros c a Hc Ha. unfold reginfo in Ha. apply rt_priv_space; [unfold KSPACE, PG in *; lia|].
    intros p n Hin HP Hr. destruct (live_prim_chunk p n Hin HP) as (C1 & C2 & _).
    destruct (carved_range bt st Lc FF W _ _ C1 C2) as (_ & _ & _ & A4 & _). unfold KSPACE in *. lia.
  Qed.

  Theorem rt_priv_fa : forall c a, 1 <= c <= 30 -> fa_beg SBEG c <= a < fa_beg SBEG c + 2 ^ 29 -> rt_priv IA Lc FF a.
  Proof using W qg qt st.
    intros c a Hc Ha. unfold fa_beg, region_beg, KREGION, KFAOFF in Ha. apply rt_priv_space; [unfold KSPACE, PG in *; lia|].
    intros p n Hin HP Hr. destruct (live_prim_chunk p n Hin HP) as (C1 & C2 & _). set (c' := blk_class n) in *.
    destruct (carved_range bt st Lc FF W _ _ C1 C2) as (A1 & A2 & _).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c' C1) as (((B0 & B1) & _) & _ & MUX & _).
    unfold region_beg, KREGION, KREGION_EXHAUST, KUSERMAP in *.
    assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E | [E | E]] by lia; [rewrite E in * | |]; lia.
  Qed.

  Theorem rt_priv_uslot : forall c a, 1 <= c <= 30 -> uslot bt st c a -> rt_priv IA Lc FF a.
  Proof using W qg qt.
    intros c a Hc Ha. unfold uslot in Ha.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (((B0c & B1c) & _) & _ & MUXc & _).
    apply rt_priv_space; [unfold region_beg, KREGION, KREGION_EXHAUST, KUSERMAP, KSPACE, PG in *; lia|].
    intros p n Hin HP Hr. destruct (live_prim_chunk p n Hin HP) as (C1 & C2 & _). set (c' := blk_class n) in *.
    destruct (carved_range bt st Lc FF W _ _ C1 C2) as (A1 & A2 & _).
    destruct (WR1 c' C1) as (((B0 & B1) & _) & _ & MUX & _).
    unfold region_beg, KREGION, KREGION_EXHAUST, KUSERMAP in *.
    assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E | [E | E]] by lia; [rewrite E in * | |]; lia.
  Qed.

  Theorem rt_priv_fslot : forall c a, 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> fslot bt st c a -> rt_priv IA Lc FF a.
  Proof using W qg qt.
    intros c a Hc FR Ha. unfold fslot in Ha. pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & MF0 & _).
    apply (rt_priv_fa c a Hc). unfold KFAMAP in *. lia.
  Qed.




  (* [comment removed for export] *)
  Theorem rt_priv_shadow_of : forall lo L z, lo mod 8 = 0 -> L mod 8 = 0 -> AS_HEAPLO <= lo -> lo + L <= CEIL ->
    (forall a, lo <= a < lo + L -> ~ app_visible IA Lc FF a) ->
    sh_lo lo <= z < sh_lo lo + L / 8 -> rt_priv IA Lc FF z.
  Proof using W qg qt st.
    intros lo L z Hlo HL HLO HHI NV Hz. pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof ceil_rng as CR.
    unfold sh_lo in Hz.
    pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo. rewrite Hlo in Dlo. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL in DL.
    set (g := z - SB) in *. assert (Eg : z = SB + g) by ((lazymatch goal with |- ?G => let G' := eval unfold g in G in change_no_check G' end); lia).
    assert (G8 : lo <= 8 * g < lo + L) by lia.
    split; [ulia|]. split; [ulia|].
    intros [V | [V | [V | [V | [V | V]]]]].
    - (* [comment removed for export] *) destruct V as (p & n & Hin & Hr).
      pose proof W as (_ & _ & _ & _ & (WL & _) & _). destruct (WL p n Hin) as (_ & _ & (B1 & B2 & B3 & B4) & _). ulia.
    - destruct V as (f & k & Hf & Hr). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & INFS & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((D1 & D2 & D3 & D4 & D5) & _). ulia.
    - destruct V as (p & n & Hin & Hr). unfold sh_lo, sh_hi in Hr.
      destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4).
      apply (NV (8 * g) G8). left. exists p, n. split; [exact Hin|].
      pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. assert (P8 : p mod 8 = 0) by (clear -L4; Z.div_mod_to_equations; lia). rewrite P8 in Dp.
      assert (g < (p + n + 7) / 8) by lia. assert (p / 8 <= g) by lia.
      assert (8 * g + 8 <= p + n + 7) by (clear -H; Z.div_mod_to_equations; lia). lia.
    - destruct V as (f & k & Hf & Hr). unfold sh_lo, sh_hi in Hr.
      destruct (frame_gran bt st Lc FF W f k Hf) as [F8 K8].
      apply (NV (8 * g) G8). right; left. exists f, k. split; [exact Hf|].
      pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite F8 in Df.
      assert (g < (f + FS k + 7) / 8) by lia. assert (f / 8 <= g) by lia.
      assert (8 * g + 8 <= f + FS k + 7) by (clear -H; Z.div_mod_to_equations; lia). lia.
    - unfold in_stack_shadow, sh_lo in V. pose proof ceil_pg as CP.
      assert (CEIL / 8 <= g) by lia. assert (CEIL <= 8 * g) by (clear -H CP; Z.div_mod_to_equations; lia). lia.
    - unfold in_image_shadow, sh_lo, sh_hi in V.
      assert (g < (ia_img_lo IA + (ia_img_hi IA - ia_img_lo IA) + 7) / 8) by lia.
      assert (8 * g + 8 <= ia_img_hi IA + 7) by (clear -H; Z.div_mod_to_equations; lia). ulia.
  Qed.

  (* [comment removed for export] *)
  Lemma slot_mod8 : forall lo, (lo - SBEG) mod KUSERMAP = 0 -> lo mod 8 = 0.
  Proof using W qg qt FF Lc st RUN.
    intros lo H. pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB16).
    unfold KUSERMAP in H. pose proof (Z.div_mod (lo - SBEG) (2 ^ 18) ltac:(lia)) as D1. rewrite H in D1.
    pose proof (Z.div_mod SBEG (2 ^ 16) ltac:(lia)) as D2. rewrite SB16 in D2.
    replace lo with ((32768 * ((lo - SBEG) / 2 ^ 18) + 8192 * (SBEG / 2 ^ 16)) * 8) by lia. apply Z_mod_mult.
  Qed.
  Theorem rt_priv_uslot_shadow : forall c z, 1 <= c <= 30 ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    sh_lo lo <= z < sh_lo lo + KUSERMAP / 8 -> rt_priv IA Lc FF z.
  Proof using W qg qt.
    intros c z Hc lo Hz. pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (((B0 & B1) & _) & MUK & MUX & _).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X15 & _).
    destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & _ & SPH).
    assert (S2 : AS_HEAPLO <= lo) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, region_beg, KREGION in G in change_no_check G' end); lia).
    assert (S3 : lo + KUSERMAP <= CEIL) by (unfold lo, region_beg, KREGION, KREGION_EXHAUST, KUSERMAP, KSPACE, PG in *; lia).
    apply (rt_priv_shadow_of lo KUSERMAP z); [apply slot_mod8; exact (AsAinvEntry3.AsAinvLedger.user_slot_aligned bt c _ MUK) | reflexivity | exact S2 | exact S3 | | exact Hz].
    intros a Ha. exact (proj2 (proj2 (rt_priv_uslot c a Hc Ha))).
  Qed.
  Theorem rt_priv_fslot_shadow : forall c z, 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    sh_lo lo <= z < sh_lo lo + KFAMAP / 8 -> rt_priv IA Lc FF z.
  Proof using W qg qt.
    intros c z Hc FR lo Hz. pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & MF0 & MFK & _).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X15 & _).
    destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & _ & SPH).
    assert (S2 : AS_HEAPLO <= lo) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); lia).
    assert (S3 : lo + KFAMAP <= CEIL) by (unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KSPACE, PG in *; lia).
    apply (rt_priv_shadow_of lo KFAMAP z); [apply slot_mod8; exact (AsAinvEntry3.AsAinvLedger.fa_slot_aligned bt c _ MFK) | reflexivity | exact S2 | exact S3 | | exact Hz].
    intros a Ha. exact (proj2 (proj2 (rt_priv_fslot c a Hc FR Ha))).
  Qed.

End RtPriv.
