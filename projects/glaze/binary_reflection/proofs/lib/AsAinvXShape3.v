(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section XShape.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Definition xshape (z : Z) : Prop :=
    CEIL <= z \/ (T + 2768 <= z < T + 3168) \/ exists p n, In (p, n) Lc /\ (z = p - 16 \/ p <= z < p + 8 \/ sh_lo p <= z < sh_hi p n).

  (* [comment removed for export] *)
  Lemma carved_vs_fa : forall c' a' c0, 1 <= c' <= 30 -> carved bt st c' a' -> 1 <= c0 <= 30 -> a' + csize c' <= fa_beg SBEG c0 \/ fa_beg SBEG c0 + 2 ^ 29 <= a'.
  Proof.
    intros c' a' c0 Hc' CVa Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1' & E2' & E3' & E4' & E5' & _).
    destruct (carved_range bt st Lc FF W c' a' Hc' CVa) as (D1 & D2 & _).
    pose proof (region_facts bt st Lc FF W c' Hc') as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
    pose proof W as ((WR1 & _) & _).
    unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
    destruct (Z.lt_trichotomy c0 c') as [LT|[->|GT]]; [| left; clear -D1 D2 F2 F3; lia |].
    * right. assert (c0 * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H D1 D2 F2 F3. lia.
    * left. assert (c' * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c' * 2 ^ 32 + 2 ^ 32) with ((c' + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
      destruct (WR1 c' Hc') as (R1' & _ & R3' & _). unfold KREGION_EXHAUST, KUSERMAP in R3'. clear -H D1 D2 F2 F3 R1' R3'. lia.
  Qed.

  Lemma pair_eq_dec : forall (a b : Z), {(a, b) = (T, T + PG)} + {(a, b) <> (T, T + PG)}.
  Proof. intros a b. destruct (Z.eq_dec a T) as [-> | N1]; [destruct (Z.eq_dec b (T + PG)) as [-> | N2]; [left; reflexivity | right; intros E; injection E as E; exact (N2 E)] | right; intros E; injection E as E _; exact (N1 E)]. Qed.

  Section One.
    Variables (c z : Z).
    Hypothesis Hc : 1 <= c <= 30.
    Hypothesis HX : xshape z.
    #[local] Notation ulo := (region_beg SBEG c + r_mapped_user (a_reg st c)).
    #[local] Notation flo := (fa_beg SBEG c + r_mapped_fa (a_reg st c)).

    (* [comment removed for export] *)
    Lemma xshape_cases :
      CEIL <= z
      \/ (T <= z < T + PG /\ T + 2768 <= z)
      \/ (exists p n lo hi, In (p, n) Lc /\ ext bt st Lc p n lo hi /\ lo <= z < hi)
      \/ (exists p n, In (p, n) Lc /\ sh_lo p <= z < sh_hi p n).
    Proof.
      destruct HX as [H | [H | (p & n & Hin & [H | [H | H]])]]; [left; exact H | right; left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | | | right; right; right; exists p, n; exact (conj Hin H)];
        right; right; left; destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & EX & L1 & L2 & _ & _ & _ & _ & _ & (RZ1 & _) & _ & (N1 & _) & _);
        pose proof (up8_facts n N1) as (U1 & U2 & _); exists p, n, lo, hi; (split; [exact Hin|]); (split; [exact EX|]); lia.
    Qed.

    (* [comment removed for export] *)
    Lemma ext_off_space_zone : forall p n lo hi (Zn : Z -> Prop), In (p, n) Lc -> ext bt st Lc p n lo hi -> lo <= z < hi ->
      (forall a, Zn a -> SBEG <= a < SBEG + KSPACE + PG) ->
      (forall c' a' a, 1 <= c' <= 30 -> carved bt st c' a' -> a' <= a < a' + csize c' -> Zn a -> False) -> ~ Zn z.
    Proof.
      intros p n lo hi Zn Hin EX Hz ZS ZC HZ. destruct EX as [(HP & -> & -> & CV & Hc' & _) | (HP & sc & Hsc & _ & _ & -> & ->)].
      - exact (ZC _ _ z Hc' CV Hz HZ).
      - pose proof (ZS z HZ) as S. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hsc)) as [D | D]; unfold PG in *; lia.
    Qed.

    Lemma xshape_off_uslot : ~ (ulo <= z < ulo + KUSERMAP).
    Proof.
      intros HZ. assert (US : uslot bt st c z) by exact HZ. destruct (uslot_in_space bt st Lc FF c qt qg W Hc z US) as (S1 & S2 & S3 & S4 & S5).
      destruct xshape_cases as [H | [[H _] | [(p & n & lo & hi & Hin & EX & Hz) | (p & n & Hin & Hz)]]].
      - lia.
      - destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as [D | D]; unfold PG in *; lia.
      - apply (ext_off_space_zone p n lo hi (uslot bt st c) Hin EX Hz); [| | exact US].
        + intros a Ha. destruct (uslot_in_space bt st Lc FF c qt qg W Hc a Ha) as (A1 & _). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia.
        + intros c' a' a Hc' CV Ha Hs. exact (uslot_vs_carved bt st Lc FF c qt qg W Hc c' a' a Hc' CV Ha Hs).
      - destruct (rt_priv_uslot bt st Lc FF W c z Hc US) as (_ & _ & NV). apply NV. right; right; left. exists p, n. exact (conj Hin Hz).
    Qed.

    Lemma xshape_off_fa : ~ (fa_beg SBEG c <= z < fa_beg SBEG c + 2 ^ 29).
    Proof.
      intros HZ. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & _ & E8 & _).
      destruct xshape_cases as [H | [[H _] | [(p & n & lo & hi & Hin & EX & Hz) | (p & n & Hin & Hz)]]].
      - destruct (rt_priv_fa bt st Lc FF W c z Hc HZ) as (LT & _). lia.
      - destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as [D | D]; unfold PG in *; lia.
      - apply (ext_off_space_zone p n lo hi (fun a => fa_beg SBEG c <= a < fa_beg SBEG c + 2 ^ 29) Hin EX Hz); [| | exact HZ].
        + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia.
        + intros c' a' a Hc' CV Ha Hs. destruct (carved_vs_fa c' a' c Hc' CV Hc); lia.
      - destruct (rt_priv_fa bt st Lc FF W c z Hc HZ) as (_ & _ & NV). apply NV. right; right; left. exists p, n. exact (conj Hin Hz).
    Qed.

    Lemma xshape_off_reginfo : ~ (reginfo bt c <= z < reginfo bt c + 128).
    Proof.
      intros HZ. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & E9 & E10 & _).
      destruct xshape_cases as [H | [[H _] | [(p & n & lo & hi & Hin & EX & Hz) | (p & n & Hin & Hz)]]].
      - destruct (rt_priv_reginfo bt st Lc FF W c z Hc HZ) as (LT & _). lia.
      - destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as [D | D]; unfold PG, KSPACE in *; lia.
      - apply (ext_off_space_zone p n lo hi (fun a => reginfo bt c <= a < reginfo bt c + 128) Hin EX Hz); [| | exact HZ].
        + intros a Ha. cbv beta in Ha. unfold KSPACE, PG in *. lia.
        + intros c' a' a Hc' CV Ha Hs. cbv beta in Hs. destruct (carved_range bt st Lc FF W c' a' Hc' CV) as (_ & _ & _ & D4 & _). clear - Hs Ha D4 E9. lia.
      - destruct (rt_priv_reginfo bt st Lc FF W c z Hc HZ) as (_ & _ & NV). apply NV. right; right; left. exists p, n. exact (conj Hin Hz).
    Qed.

    (* [comment removed for export] *)
    Lemma live_shadow_band : forall p n, In (p, n) Lc -> sh_lo p <= z < sh_hi p n -> SB <= z < AS_HEAPLO.
    Proof.
      intros p n Hin Hz. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & _). pose proof (band_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & B6 & _).
      unfold sh_lo, sh_hi, PTRLO in *. clear - Hz A1 A2 A3 B6. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma xshape_off_band_priv : forall (Zn : Z -> Prop), Zn z -> (forall a, Zn a -> SB <= a < AS_HEAPLO) -> (forall a, Zn a -> rt_priv IA Lc FF a) -> False.
    Proof.
      intros Zn HZ ZB ZP. pose proof (ZB z HZ) as Bz. destruct (ZP z HZ) as (LT & _ & NV).
      destruct xshape_cases as [H | [[H _] | [(p & n & lo & hi & Hin & EX & Hz) | (p & n & Hin & Hz)]]].
      - lia.
      - destruct (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & TPB). unfold SB, AS_LO, PG in *. lia.
      - destruct EX as [(HP & -> & -> & CV & Hc' & _ & S1 & S2) | (HP & sc & Hsc & _ & _ & -> & ->)].
        + pose proof (band_facts bt st Lc FF W) as (_ & _ & B3 & _). unfold SB in *. lia.
        + pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
          destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hsc))) as ((_ & _ & _ & _ & D5) & _). unfold SB, AS_LO, PG in *. lia.
      - apply NV. right; right; left. exists p, n. exact (conj Hin Hz).
    Qed.

    Lemma xshape_off_uslot_sh : ~ (sh_lo ulo <= z < sh_lo ulo + KUSERMAP / 8).
    Proof.
      intros HZ. apply (xshape_off_band_priv (fun a => sh_lo ulo <= a < sh_lo ulo + KUSERMAP / 8) HZ).
      - intros a Ha. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & _ & _ & E5 & _ & _ & E8 & _).
        pose proof (band_facts bt st Lc FF W) as (_ & _ & B3 & B4 & B5 & B6 & _). pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & MUX & _).
        unfold sh_lo, KUSERMAP, KREGION_EXHAUST, KSPACE, PG in *. clear - Ha E1 E2 E5 E8 B3 B4 B5 B6 MUX. Z.div_mod_to_equations. lia.
      - intros a Ha. exact (rt_priv_uslot_shadow bt st Lc FF W c a Hc Ha).
    Qed.

    Lemma xshape_off_fslot_sh : r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> ~ (sh_lo flo <= z < sh_lo flo + KFAMAP / 8).
    Proof.
      intros FR HZ. apply (xshape_off_band_priv (fun a => sh_lo flo <= a < sh_lo flo + KFAMAP / 8) HZ).
      - intros a Ha. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & _ & _ & E5 & E6 & _ & E8 & _).
        pose proof (band_facts bt st Lc FF W) as (_ & _ & B3 & B4 & B5 & B6 & _).
        unfold sh_lo, KFAMAP, KSPACE, PG in *. clear - Ha E1 E2 E5 E6 E8 B3 B4 B5 B6 FR. Z.div_mod_to_equations. lia.
      - intros a Ha. exact (rt_priv_fslot_shadow bt st Lc FF W c a Hc FR Ha).
    Qed.

    (* [comment removed for export] *)
    Lemma xshape_off_img : ~ (ia_img_lo IA <= z < ia_img_hi IA).
    Proof.
      intros HZ. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      destruct xshape_cases as [H | [[H _] | [(p & n & lo & hi & Hin & EX & Hz) | (p & n & Hin & Hz)]]].
      - unfold AS_LO, AS_HEAPLO in *. lia.
      - destruct (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & _). lia.
      - destruct EX as [(HP & -> & -> & CV & Hc' & _ & S1 & S2) | (HP & sc & Hsc & _ & _ & -> & ->)].
        + unfold AS_LO, AS_HEAPLO in *. lia.
        + pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
          destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hsc))) as ((_ & _ & _ & D4 & _) & _). unfold PG in *. lia.
      - pose proof (live_shadow_band p n Hin Hz). unfold SB, AS_LO in *. lia.
    Qed.

    Lemma xshape_off_fixed : forall flo' fhi', In (flo', fhi') (bt_fixed bt) -> fhi' - flo' < KSPACE -> flo' <= z < fhi' ->
      ((flo', fhi') = (T, T + PG) -> z < T + 2768) -> False.
    Proof.
      intros flo' fhi' Hin Hlen HZ HT. destruct (fixed_range bt st Lc FF W flo' fhi' Hin) as ((D1 & D2 & D3 & D4 & D5) & _).
      destruct xshape_cases as [H | [[H H'] | [(p & n & lo & hi & Hin' & EX & Hz) | (p & n & Hin' & Hz)]]].
      - lia.
      - destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        destruct (pair_eq_dec flo' fhi') as [E | NE]; [specialize (HT E); lia|].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INT) NE) as D. hnf in D. cbn in D. lia.
      - destruct (live_ext_vs_fixed bt st Lc FF W p n lo hi flo' fhi' Hin' EX Hin Hlen); lia.
      - pose proof (live_shadow_band p n Hin' Hz). unfold SB, AS_LO in *. lia.
    Qed.
  End One.

  (* [comment removed for export] *)
  Lemma xshape_off_tctx : forall z, xshape z -> ~ (bt_tctx bt + 152 <= z < bt_tctx bt + 160).
  Proof.
    intros z HX HZ. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & INC).
    apply (xshape_off_fixed z HX _ _ INC); [(lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia | lia |]. intros E. injection E as E1 E2. unfold PG in *. lia.
  Qed.
  Lemma xshape_off_thread_lo : forall z, xshape z -> ~ (T <= z < T + 2768).
  Proof.
    intros z HX HZ. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
    apply (xshape_off_fixed z HX _ _ INT); [(lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | intros _; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem xshape_off_t : forall c z, 1 <= c <= 30 -> xshape z ->
    let ulo := region_beg SBEG c + r_mapped_user (a_reg st c) in let flo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    ~ (ulo <= z < ulo + KUSERMAP) /\ ~ (sh_lo ulo <= z < sh_lo ulo + KUSERMAP / 8) /\ ~ (fa_beg SBEG c <= z < flo)
    /\ (r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> ~ (flo <= z < flo + KFAMAP) /\ ~ (sh_lo flo <= z < sh_lo flo + KFAMAP / 8))
    /\ ~ (ia_img_lo IA <= z < ia_img_hi IA) /\ ~ (bt_tctx bt + 152 <= z < bt_tctx bt + 160) /\ ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (T <= z < T + 2768).
  Proof.
    intros c z Hc HX. cbn zeta. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & E6 & _).
    pose proof (xshape_off_fa c z Hc HX) as NFA.
    split; [exact (xshape_off_uslot c z Hc HX)|]. split; [exact (xshape_off_uslot_sh c z Hc HX)|].
    split; [intros H; apply NFA; lia|].
    split; [intros FR; split; [intros H; apply NFA; unfold KFAMAP in *; lia | exact (xshape_off_fslot_sh c z Hc HX FR)]|].
    split; [exact (xshape_off_img z HX)|]. split; [exact (xshape_off_tctx z HX)|]. split; [exact (xshape_off_reginfo c z Hc HX) | exact (xshape_off_thread_lo z HX)].
  Qed.

End XShape.
