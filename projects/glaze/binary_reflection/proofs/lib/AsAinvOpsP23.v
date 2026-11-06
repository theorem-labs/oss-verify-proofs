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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

Section P2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section FaZone.
    Variables (st : ast) (Lc FF : list (Z * Z)) (c : Z).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.
    Hypothesis Hc : 1 <= c <= 30.
    #[local] Notation FB := (fa_beg SBEG c).
    Definition fazone (i : Z) : Prop := FB + 4 * Z.of_nat (length (r_free (a_reg st c))) <= i < FB + 2 ^ 29.

    Lemma fazone_span : forall i, fazone i ->
      SBEG <= region_beg SBEG c /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= FB /\ FB <= i < FB + 2 ^ 29
      /\ FB + 2 ^ 29 <= SBEG + KSPACE /\ region_beg SBEG c + 2 ^ 32 = FB + 2 ^ 29 /\ FB + 4 * Z.of_nat (length (r_free (a_reg st c))) <= i.
    Proof using Hc W qg qt FF Lc RUN.
      intros i Hi. unfold fazone in Hi. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      unfold fa_beg, region_beg, KFAOFF, KREGION in *. repeat split; lia.
    Qed.
    Lemma fazone_other : forall c0 i, 1 <= c0 <= 30 -> c0 <> c -> region_beg SBEG c0 <= i < region_beg SBEG c0 + 2 ^ 32 -> fazone i -> False.
    Proof using Hc W qg qt FF Lc RUN.
      intros c0 i Hc0 NE Hi Hs. destruct (fazone_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
      unfold fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 c) as [LT|[EQ|GT]]; [| exact (NE EQ) |].
      - assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        clear -Hi S3 HM. lia.
      - assert (HM : c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        clear -Hi S3 S5 HM. lia.
    Qed.
    Lemma fazone_vs_carved : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> a <= i < a + csize c0 -> fazone i -> False.
    Proof using Hc W qg qt FF Lc RUN.
      intros c0 a i Hc0 CV Hi Hs. destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (C1 & C2 & C3 & C4 & C5).
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      destruct (Z.eq_dec c0 c) as [-> | NE].
      - destruct (fazone_span i Hs) as (S1 & S2 & S3 & _). lia.
      - apply (fazone_other c0 i Hc0 NE); [| exact Hs]. unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia.
    Qed.

    Theorem fazone_not_cells : forall i, fazone i -> rep_cells bt st Lc FF i -> False.
    Proof using Hc W qg qt RUN.
      intros i Hs HC. destruct (fazone_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
      pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
      pose proof (img_lits bt st Lc FF W) as [I1 I2].
      assert (Z1 : SBEG <= i < SBEG + KSPACE) by lia.
      assert (Z5 : ~ (ia_img_lo IA <= i < ia_img_hi IA)) by (clear -Z1 I2 SP7 SPH; ulia).
      pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
      assert (FIXoff : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> lo <= i < hi -> False).
      { intros lo hi Hin Hlen Hi. destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen); clear -H Hi Z1 S3 S4; ulia. }
      assert (DYNoff : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= i < hi -> False).
      { intros lo hi Hin Hi. destruct (space_vs_dyn bt st Lc FF W lo hi Hin); clear -H Hi Z1 S3 S4; ulia. }
      assert (IMGoff : img_kind bt i -> False) by (intros [Hh _]; exact (Z5 Hh)).
      assert (BANDoff : forall lo, SB <= lo -> lo <= i -> i < AS_HEAPLO -> False) by (intros lo A B C0; clear -A B C0 Z1 SP7 SPH; ulia).
      assert (REGINFOoff : SBEG + KSPACE <= i -> False) by (clear -Z1; lia).
      assert (FAoff : forall c0, 1 <= c0 <= 30 -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 4 * Z.of_nat (length (r_free (a_reg st c0))) -> False).
      { intros c0 Hc0 Hi. destruct (Z.eq_dec c0 c) as [-> | NE]; [clear -Hi S6; lia|].
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
        apply (fazone_other c0 i Hc0 NE); [| exact Hs]. unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia. }
      assert (BLKoff : forall p n, In (p, n) Lc \/ In (p - 16, n) (quar st) -> foot_hdr p n i -> False).
      { intros p n Hown Hf.
        destruct (hdr_zone bt st Lc FF W p n i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
        - apply (fazone_vs_carved _ _ i HC' CV'); [| exact Hs]. pose proof (rz_range n). unfold prim_alloc_beg in *. lia.
        - apply (DYNoff _ _ (sec_dyn st sc' Hs')). destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
          rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
      unfold rep_cells in HC.
      destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
      + exact (IMGoff (img_kinds bt st Lc FF W i (or_introl K))).
      + destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN|NI].
        * apply (FIXoff _ _ IN8); [ulia | clear -IN SS1 SS3; lia].
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact K | exact NI]))).
      + unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
        destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIXoff _ _ INT); [ulia | clear -K; ulia] | apply (FIXoff _ _ INC); [ulia | clear -K; lia]].
      + destruct K as (c0 & Hc0 & K). unfold foot_region in K.
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        destruct K as [[K _]|K]; [apply REGINFOoff; lia | apply (FAoff c0 Hc0); exact K].
      + destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (fazone_vs_carved BATCHCLASS (ba_addr b) i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| exact Hs]. change (csize BATCHCLASS) with 8192. unfold BATCHCAP in *. lia.
      + destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)). unfold sc_mapsz in *. ulia.
      + destruct K as (p & n & Hown & K). exact (BLKoff p n Hown K).
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; right; left; exact K))).
      + destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
        pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
        destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
      + unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
        1-3: apply (FIXoff _ _ INFS); ulia.
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact K))).
        * apply (FIXoff _ _ (dtls_member bt st Lc FF W)); ulia.
      + destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
        apply (FIXoff _ _ INFS); ulia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact K))).
      + destruct K as (c0 & Hc0 & K). unfold foot_shreg, sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
        destruct K as [[K _]|K]; (apply (BANDoff SB); [lia | clear -K Q1 Q2 Q8 X14; Zlia | clear -K Q1 Q2 Q5 Q6 Q8 X15; Zlia]).
      + destruct K as (sc & Hs' & K). unfold foot_shsec, sh_lo in K. destruct K as [K _]. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 5 right; exact K))).
    Qed.
  End FaZone.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac frc E9 X14 E10 X15 CR AGc H := eapply (cellZ_frame _ _ _ _ _ _ H);
    [clear -E9 X14; lia | clear -E10 X15 CR; lia | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply AGc; [clear -Hi; cbn in Hi; lia | clear -Hi; cbn in Hi; lia]].
  Theorem OPS_REP_carve_pf : OPS_REP_carve bt.
  Proof using.
    intros st Lc FF M M' mdl mdl' c W R Hc. cbn zeta. intros ROOM AGR CFA C16 C32 C68 SBM MI.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof (csize_pos c Hc) as [CS1 CS2].
    set (N := carve_n (a_reg st c) c) in *.
    assert (N0 : 0 <= N /\ N * csize c <= r_mapped_user (a_reg st c) - r_alloc_user (a_reg st c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold N, carve_n in G in change_no_check G' end). split; [apply Z.div_pos; lia | rewrite Z.mul_comm; apply Z.mul_div_le; lia]. }
    destruct N0 as [N0 N1].
    (* [comment removed for export] *)
    set (PIN := fun i : Z => (reginfo bt c + 16 <= i < reginfo bt c + 24) \/ (reginfo bt c + 32 <= i < reginfo bt c + 40) \/ i = reginfo bt c + 68).
    set (Mmid := fun a : word => if decide (PIN (u a)) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R). intros a NEa. unfold Mmid in NEa |- *.
      destruct (decide (PIN (u a))) as [IN|NI]; [exfalso; exact (NEa eq_refl)|].
      destruct (AGR a NEa) as [Hf Hd]. split; [| exact Hd].
      intros HC. unfold foot_carve in Hf. cbn zeta in Hf. fold N in Hf. unfold PIN in NI.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]]].
      - apply (fazone_not_cells st Lc FF c W Hc (u a)); [| exact HC]. (lazymatch goal with |- ?G => let G' := eval unfold fazone in G in change_no_check G' end). clear -Hf ROOM Y8 N0. lia.
      - apply NI. left. exact Hf.
      - apply NI. right; left. exact Hf.
      - apply NI. right; right. exact Hf.
      - exact (rijunk_not_cells bt st Lc FF W c (u a) Hc Hf HC).
      - exact (stats_not_cells bt st Lc FF W (u a) ltac:(unfold T_UNW in Hf; exact Hf) HC).
      - exact (ceil_not_cells bt st Lc FF W (u a) Hf HC). }
    (* [comment removed for export] *)
    assert (AG : forall i, ~ PIN i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (decide (PIN i)) as [IN|NI]; [exfalso; exact (Hi IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NEa. unfold Mmid in NEa. destruct (decide (PIN (u a))) as [IN|NI]; [| exfalso; exact (NEa eq_refl)]. exact (proj2 (AGR a NEa)). }
    assert (OUTRI : forall i, ~ (SBEG + KSPACE <= i < SBEG + KSPACE + PG) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). clear -Hi E9 E10. intros [X|[X|X]]; lia. }
    assert (IMGR : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi. apply OUTRI; [clear -Hi I2 SBH; ulia | clear -Hi I1 I2; ulia]. }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGR i Hi). }
    assert (FIXR : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE ->
                   forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin Hlen i Hi Hr. apply OUTRI; [| exact Hr]. destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen); clear -H Hi; ulia. }
    assert (DYNR : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi Hr. apply OUTRI; [| exact Hr]. destruct (space_vs_dyn bt st Lc FF W lo hi Hin); clear -H Hi; ulia. }
    assert (SPCR : forall i, SBEG <= i < SBEG + KSPACE -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply OUTRI; [clear -Hi; lia | exact Hr]. }
    assert (BANDR : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros i Hi Hr. apply OUTRI; [clear -Hi SBH; ulia | exact Hr]. }
    assert (HDRR : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
      - apply SPCR; [clear -W1 W2 W3 W4 N1'; ulia | exact Hr].
      - apply (DYNR _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        rewrite Eu', En' in *. clear -W1 A5 A6 N1'. ulia. }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. ulia. }
    assert (BA : forall q, (forall b0, In b0 q -> In b0 (a_tq st ++ a_gq st)) -> rep_batches bt Mmid q -> rep_batches bt M' q).
    { intros q SUB RB. eapply rep_batches_frame; [exact DEF | exact RB | intros b0 Hb0; exact (BR b0 (SUB b0 Hb0)) |].
      intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 (SUB b0 Hb0)) as (_ & BL1 & BL2 & BL3).
      apply SPCR; [clear -Hi BL1 BL2 BL3; ulia | exact Hr]. }
    clear WR2 WQ S2 S4 S5 S6 S7 S8 LV1 LV3 WK WD WM' RNG PW' R6a R6b IN6 G.
    set (st' := op_carve SBEG st c).
    destruct (carve_fields SBEG st c c) as (RMUc & RAUc & RFAc & RFRc & RUHc & RFHc). rewrite Z.eqb_refl in RAUc, RFRc. fold N in RAUc, RFRc. fold st' in RMUc, RAUc, RFAc, RFRc, RUHc, RFHc.
    assert (RMU : forall c0, r_mapped_user (a_reg st' c0) = r_mapped_user (a_reg st c0)) by (intros c0; exact (proj1 (carve_fields SBEG st c c0))).
    assert (RFA : forall c0, r_mapped_fa (a_reg st' c0) = r_mapped_fa (a_reg st c0)) by (intros c0; exact (proj1 (proj2 (proj2 (carve_fields SBEG st c c0))))).
    assert (RUH : forall c0, r_uhole (a_reg st' c0) = r_uhole (a_reg st c0)) by (intros c0; exact (proj1 (proj2 (proj2 (proj2 (proj2 (carve_fields SBEG st c c0))))))).
    assert (RFH : forall c0, r_fhole (a_reg st' c0) = r_fhole (a_reg st c0)) by (intros c0; exact (proj2 (proj2 (proj2 (proj2 (proj2 (carve_fields SBEG st c c0))))))).
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in YC. destruct (YC c0 Hc0).
             exact (IMGK i (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) ltac:(lia)). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact P2 | uilia | uilia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXR _ _ IN8); [ulia | clear -IN S1 S3; lia | exact Hr].
             - exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) Hr). }
    (* [comment removed for export] *)
    split. { change (rep_thread bt st' M') with (rep_thread bt st M'). eapply rep_thread_frame; [exact DEF | exact P3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. destruct (thread_cells_where bt i Hi) as [A|A].
             - apply (FIXR _ _ INT); [ulia | clear -A; unfold T_UNW, PG in *; lia | exact Hr].
             - apply (FIXR _ _ INC); [ulia | clear -A; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (Z.eq_dec c0 c) as [-> | NE].
             - destruct (P4 c Hc) as [(G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GW) (F1 & F2 & F3)].
               assert (AGc : forall i, reginfo bt c <= i < reginfo bt c + 128 ->
                              ~ ((reginfo bt c + 16 <= i < reginfo bt c + 24) \/ (reginfo bt c + 32 <= i < reginfo bt c + 40) \/ i = reginfo bt c + 68) ->
                              M' (Z_to_bv 64 i) = Mmid (Z_to_bv 64 i)).
               { intros i Hi Hn. apply AG; [exact Hn | clear -Hi E9 E10 X14 X15; ulia]. }
               unfold KSPACE, PG in E9, E10, X15. pose proof ceil_rng as CR.
               split.
               + (lazymatch goal with |- ?G => let G' := eval unfold rep_reginfo in G in change_no_check G' end). rewrite RMUc, RAUc, RFAc, RFRc. rewrite length_app, Nat2Z.inj_add, (carve_list_length bt c _ N N0).
                 split; [frc E9 X14 E10 X15 CR AGc G1|]. split; [frc E9 X14 E10 X15 CR AGc G2|]. split; [exact C16|]. split; [frc E9 X14 E10 X15 CR AGc G4|].
                 split; [exact C32|]. split; [frc E9 X14 E10 X15 CR AGc G6|]. split; [frc E9 X14 E10 X15 CR AGc G7|]. split; [frc E9 X14 E10 X15 CR AGc G8|].
                 split; [exact C68 | exact (writableZ_keep _ _ _ _ _ DEF GW)].
               + (lazymatch goal with |- ?G => let G' := eval unfold rep_freearray in G in change_no_check G' end). rewrite RMUc, RFAc, RFRc. split; [| split; [frW DEF F2 | frW DEF F3]].
                 intros i k Hk. destruct (Nat.lt_ge_cases i (length (r_free (a_reg st c)))) as [LT | GE].
                 * rewrite nth_error_app1 in Hk by exact LT. pose proof (F1 i k Hk) as C0.
                   eapply (cellZ_frame _ _ _ _ _ _ C0); [clear -E1 E2 E8 X14; ulia | clear -LT Y7 E5 E6 X15 CR; ulia |].
                   intros j Hj. apply SPCR; [clear -Hj LT Y7 E1 E2 E5 E6 E8; cbn in Hj; ulia | clear -Hj LT Y7 E1 E2 E5 E6 E8 X14 X15 CR; cbn in Hj; ulia].
                 * rewrite nth_error_app2 in Hk by exact GE. pose proof (CFA (i - length (r_free (a_reg st c)))%nat k Hk) as C0.
                   replace (fa_beg SBEG c + 4 * (Z.of_nat (length (r_free (a_reg st c))) + Z.of_nat (i - length (r_free (a_reg st c))))) with (fa_beg SBEG c + 4 * Z.of_nat i) in C0 by lia.
                   exact C0.
             - destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
               destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _).
               assert (ER : a_reg st' c0 = a_reg st c0).
               { (lazymatch goal with |- ?G => let G' := eval unfold st', op_carve, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [E|_]; [exfalso; exact (NE E) | reflexivity]. }
               rewrite ER.
               eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | clear -D9 X14; ulia | clear -D10 X15; ulia | clear -D1 D2 D8 X14; ulia | clear -D2 D5 D6 D8 X15; ulia | exact D7 |].
               intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi].
               + apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). unfold reginfo in *. clear -Hi Hc Hc0 NE. nia.
               + apply SPCR; [clear -Hi D1 D2 D5 D6 D7 D8; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split; [change (a_tq st') with (a_tq st); apply BA; [intros b0 Hb0; apply in_app_iff; left; exact Hb0 | exact P5]|].
    split; [change (a_gq st') with (a_gq st); apply BA; [intros b0 Hb0; apply in_app_iff; right; exact Hb0 | exact P6]|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact P7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A5 A6 A7. ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNR _ _ (sec_dyn st sc Hs)); [| exact Hr]. pose proof (rz_range (sc_n sc)). clear -Hi A5 A6 A7 H. ulia. }
    (* [comment removed for export] *)
    split. { change (rep_headers bt st' Lc M') with (rep_headers bt st Lc M'). destruct P8 as [HLh HQh]. split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros i Hi Hr. exact (HDRR p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRR (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear -Hi Hbk Eb; rewrite Eb; lia | exact Hr].
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hi Hbk; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear -Hi; ulia | exact Hr].
               + exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) Hr).
               + apply (FIXR _ _ (dtls_member bt st Lc FF W)); [clear; ulia | clear -Hi; ulia | exact Hr].
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear -Hi A1 A2 A4; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_sec st') with (a_sec st). change (quar st') with (quar st).
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1 B6 B7. Zlia. }
             split. { intros c0 g Hc0 Hg NL'. rewrite RMU in Hg. pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. rewrite RFA in Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros sc g Hs HQ HU. pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | lia]]. }
             split. { intros c0 g Hc0 Hg. rewrite RMU in Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep Mmid M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { pose proof (rep_ledger_sbm bt st mdl mdl' SBM P13) as (L1 & L2 & L3 & L4 & L5). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (dyn_maps st') with (dyn_maps st). change (a_dep st') with (a_dep st).
             assert (COMM : forall a, committed bt st' a <-> committed bt st a).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_nres st') with (a_nres st). split.
               - intros [(c1 & Hc1 & X) | X]; [left; exists c1; rewrite RMU, RFA in X; exact (conj Hc1 X) | right; exact X].
               - intros [(c1 & Hc1 & X) | X]; [left; exists c1; rewrite RMU, RFA; exact (conj Hc1 X) | right; exact X]. }
             assert (HOL : forall a, holes bt st' a <-> holes bt st a).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end). split.
               - intros (c1 & Hc1 & X). exists c1. rewrite RMU, RFA, RUH, RFH in X. exact (conj Hc1 X).
               - intros (c1 & Hc1 & X). exists c1. rewrite RMU, RFA, RUH, RFH. exact (conj Hc1 X). }
             split. { destruct L1 as (F6 & Q1 & Q2 & Q3 & Q4). exists F6. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
                      intros a Ha. rewrite (HOL a). exact (Q4 a Ha). }
             split; [intros a; rewrite (COMM a), (HOL a); exact (L2 a)|]. split; [intros a; rewrite (COMM a), (HOL a); exact (L3 a)|].
             split; [exact L4 | exact L5]. }
    (* [comment removed for export] *)
    split. { destruct P14 as (BU1 & BU2 & BU3 & BU4 & BU5 & BU6 & BU7 & BU8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3').
             split; [exact BU1|]. split; [exact MI|]. split; [exact BU3|]. split; [exact BU4|].
             split. { intros c0 Hc0. rewrite RMU, RFA. exact (BU5 c0 Hc0). }
             split; [exact BU6|]. split; [exact BU7|].
             rewrite E3'. change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st).
             assert (PC : prim_charge st' = prim_charge st).
             { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end).
               assert (EQ : forall k, sum_classes (fun c0 : Z => r_mapped_user (a_reg st' c0) + r_mapped_user (a_reg st' c0) / 8 + r_mapped_fa (a_reg st' c0) + r_mapped_fa (a_reg st' c0) / 8) k
                                  = sum_classes (fun c0 : Z => r_mapped_user (a_reg st c0) + r_mapped_user (a_reg st c0) / 8 + r_mapped_fa (a_reg st c0) + r_mapped_fa (a_reg st c0) / 8) k).
               { induction k as [|k IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH, RMU, RFA. reflexivity. }
               apply EQ. }
             rewrite PC. exact BU8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [V1 V2]. split; [frW DEF V1 | frW DEF V2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia)) ltac:(ulia))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia)) ltac:(ulia))] |].
    exact (rep_last_keep bt _ _ Mmid M' DEF P19 (fun H => H)).
  Qed.
End P2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FShadow.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (c : Z).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis FR : r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Theorem fshadow_not_cells : forall i,
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    sh_lo lo <= i < sh_lo lo + KFAMAP / 8 -> rep_cells bt st Lc FF i -> False.
  Proof using FR Hc W qg qt RUN.
    intros i lo Hi.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X16).
    assert (Elo : lo = fa_beg SBEG c + r_mapped_fa (a_reg st c)) by reflexivity.
    assert (AL : lo mod 8 = 0 /\ fa_beg SBEG c <= lo /\ lo + KFAMAP <= fa_beg SBEG c + 2 ^ 29 /\ fa_beg SBEG c + 2 ^ 29 <= SBEG + KSPACE /\ fa_beg SBEG c mod 8 = 0
                 /\ region_beg SBEG c + 2 ^ 32 = fa_beg SBEG c + 2 ^ 29).
    { rewrite Elo. unfold fa_beg, region_beg, KFAOFF, KREGION, KFAMAP in *. clear -Y5 Y6 FR Q1 Q5 X16 Hc. Z.div_mod_to_equations. lia. }
    destruct AL as (AL1 & AL2 & AL3 & AL4 & AL5 & AL6). clearbody lo.
    apply (bandz_not_cells bt st Lc FF W (fun i => sh_lo lo <= i < sh_lo lo + KFAMAP / 8)); [| | | exact Hi].
    - intros j Hj. unfold in_band, sh_lo, KFAMAP in *. clear -Hj B3 B4 B6 AL2 AL3 AL4 Q1 Q2 Q8. Zlia.
    - intros c0 j Hc0 Hj K. unfold sh_lo, KFAMAP in *.
      destruct (Z.eq_dec c0 c) as [-> | NE].
      + (* [comment removed for export] *)
        clear -Hj K AL1 AL2 AL5 Elo Q2 Q8. Zlia.
      + pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        pose proof W as ((WR1' & _) & _). destruct (WR1' c0 Hc0) as (_ & _ & Z3 & _ & _ & _ & _ & Z8 & _).
        unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP in *.
        destruct (Z.lt_trichotomy c0 c) as [LT|[EQ|GT]]; [| exact (NE EQ) |].
        * assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (clear -LT; nia). clear -Hj K HM AL2 AL3 AL6 Z3 Z8 P6 P8 X16 B5. Zlia.
        * assert (HM : c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (clear -GT; nia). clear -Hj K HM AL2 AL3 AL6 Z3 Z8 P6 P8 X16 B5. Zlia.
    - intros sc j Hs Hj K. unfold sh_lo, KFAMAP in *.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & _).
      destruct (fixed_members bt st Lc FF W) as (IN6 & _). destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & SP8 & _).
      pose proof (fixed_dyn_sep bt st Lc FF W _ _ _ _ IN6 (sec_dyn st sc Hs)) as D.
      clear -Hj K A3 A4 D SP7 SP8 AL1 AL2 AL3 AL4 Q1 Q2 Q8. Zlia.
  Qed.
End FShadow.
