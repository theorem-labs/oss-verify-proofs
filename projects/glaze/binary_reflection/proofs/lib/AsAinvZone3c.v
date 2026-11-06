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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section ZoneC.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac uall := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *.

  Definition instjunk (i : Z) : Prop := (IB bt + 128 <= i < IB bt + 680) \/ (IB bt + 681 <= i < IB bt + 728).

  (* [comment removed for export] *)
  Lemma instjunk_img : forall i, instjunk i -> ia_img_lo IA <= i < ia_img_hi IA.
  Proof using W qg qt FF Lc st RUN.
    intros i Hi. unfold instjunk, IB in Hi.
    pose proof (bt_ok_W bt st Lc FF W) as (I1 & I2 & PR & QI1 & _).
    destruct QI1 as (plo & phi & Hin & P1 & P2). destruct (PR plo phi (or_introl Hin)) as [P3 P4]. lia.
  Qed.

  Theorem instjunk_not_cells : forall i, instjunk i -> rep_cells bt st Lc FF i -> False.
  Proof using W qg qt RUN.
    intros i Hz HC. pose proof (instjunk_img i Hz) as HI. unfold instjunk in Hz.
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PWS & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (img_lits bt st Lc FF W) as [L1 L2].
    pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (img_pw bt st Lc FF W) as IPW. unfold img_ranges in IPW. cbn [PW seps fst snd] in IPW.
    destruct IPW as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & _) & _).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _).
    (* [comment removed for export] *)
    assert (FIXoff : forall lo hi, In (lo, hi) (bt_fixed bt) -> lo <= i < hi -> False).
    { intros lo hi Hin Hlo. destruct (fixed_range bt st Lc FF W lo hi Hin) as ((_ & _ & _ & D4 & _) & _). lia. }
    assert (DYNoff : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= i < hi -> False).
    { intros lo hi Hin Hlo. destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((_ & _ & _ & D4 & _) & _). lia. }
    assert (SPACEoff : SBEG <= i -> False) by (intros HS; clear -HS HI L2 B3; ulia).
    assert (BANDoff : in_band i -> False) by (intros HB; unfold in_band in HB; clear -HB HI L2; ulia).
    unfold rep_cells in HC. unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST in *.
    destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
    - (* [comment removed for export] *) destruct K as (c & Hc & Hin). rewrite Forall_forall in DC.
      apply (DC c Hc i Hin). (lazymatch goal with |- ?G => let G' := eval unfold img_dyn in G in change_no_check G' end). left. lia.
    - unfold instance_cells, IB in K. cbn zeta in K.
      destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; try lia. exact (FIXoff _ _ IN8 ltac:(clear -K SS1 SS3; lia)).
    - destruct (thread_cells_where bt i K) as [A|A]; [exact (FIXoff _ _ INT ltac:(unfold T_UNW, PG in *; lia)) | exact (FIXoff _ _ INC ltac:(lia))].
    - destruct K as (c0 & Hc0 & K). unfold foot_region in K.
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
      apply SPACEoff. unfold fa_beg, KFAOFF in *. clear -K Q1 Q7 Q9 R6a. destruct K as [[K _]|K]; ulia.
    - destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & BB1 & BB2). apply SPACEoff. lia.
    - destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (rz_range (sc_n sc)). clear -K A5 A6 A7 H. ulia.
    - destruct K as (p & n & Hown & K).
      destruct (hdr_zone bt st Lc FF W p n i Hown K) as [(HP & Hi & S1 & S2 & CV & Hc1 & N1 & S3) | (HP & sc & Hsc & Eu & En & Hi & N1)].
      + apply SPACEoff. lia.
      + destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). rewrite Eu, En in *. clear -Hi A5 A6 N1. ulia.
    - unfold foot_depot_static in K. uall. clear -K Hz J1 J2. lia.
    - destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
      pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
      destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); rewrite Eb; lia | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
    - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: apply (FIXoff _ _ INFS); ulia.
      + clear -K Hz J5. lia.
      + apply (FIXoff _ _ (dtls_member bt st Lc FF W)); ulia.
    - destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
      apply (FIXoff _ _ INFS). ulia.
    - unfold ialloc_cells in K. uall. clear -K Hz J3 J4. lia.
    - destruct K as (c0 & Hc0 & K). unfold foot_shreg in K. apply BANDoff. apply (shreg_in_band bt st Lc FF W c0 i Hc0). destruct K as [[K _]|K]; [left; exact K | right; exact K].
    - destruct K as (sc & Hs' & K). unfold foot_shsec in K. destruct K as [K _]. apply BANDoff. exact (shsec_in_band bt st Lc FF W sc i Hs' K).
    - unfold rtc_cells in K. uall. clear -K Hz J6 J7. lia.
  Qed.
End ZoneC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Apart.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Variables lo hi : Z.
  Hypothesis DOK : dyn_ok IA lo hi.
  Hypothesis AP : forall lo' hi', In (lo', hi') (all_ranges bt st) -> hi <= lo' \/ hi' <= lo.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Theorem apart_not_supp : forall i, lo <= i < hi -> rep_supp bt st Lc FF i -> False.
  Proof using AP DOK W qg qt RUN.
    intros i Hi Hsupp. destruct DOK as (D1 & D2 & D3 & D4 & D5).
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    assert (FIXoff : forall lo' hi', In (lo', hi') (bt_fixed bt) -> lo' <= i < hi' -> False).
    { intros lo' hi' Hin Hi'. destruct (AP _ _ (all_ranges_fixed bt st _ Hin)); lia. }
    assert (DYNoff : forall lo' hi', In (lo', hi') (dyn_ranges st) -> lo' <= i < hi' -> False).
    { intros lo' hi' Hin Hi'. destruct (AP _ _ (all_ranges_dyn bt st _ Hin)); lia. }
    assert (IMGoff : img_kind bt i -> False) by (intros [Hh _]; clear -Hh Hi D4; lia).
    assert (BANDoff : forall lo0, SB <= lo0 -> lo0 <= i -> i < AS_HEAPLO -> False) by (intros lo0 A B C0; clear -A B C0 Hi D5; ulia).
    assert (SPCoff : SBEG <= i < SBEG + KSPACE + PG -> False) by (intros HS; apply (FIXoff _ _ IN6); clear -HS R6a R6b; lia).
    assert (CHKoff : forall c0 a, 1 <= c0 <= 30 -> carved bt st c0 a -> a <= i < a + csize c0 -> False).
    { intros c0 a Hc0 CV Ha. destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (C1 & C2 & C3 & C4 & C5). apply SPCoff. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (BLKoff : forall p n, In (p, n) Lc \/ In (p - 16, n) (quar st) -> p - rz n <= i < p + rounded n -> False).
    { intros p n Hown Hi0. pose proof (rz_range n) as RZ. pose proof (rounded_ge n) as (RG1 & RG2 & RG3 & RG4).
      assert (N1 : 1 <= n <= NMAX).
      { destruct Hown as [HL|HQ]; [destruct (live_range bt st Lc FF W p n HL); lia | destruct (quar_item_range bt st Lc FF W (p - 16) n HQ); lia]. }
      destruct (is_primary n) eqn:HP.
      - assert (K : carved bt st (blk_class n) (prim_alloc_beg p n) /\ 1 <= blk_class n <= 30 /\ p + n <= prim_alloc_beg p n + csize (blk_class n)).
        { destruct Hown as [HL|HQ].
          - pose proof (live_chunk bt st Lc FF W p n HL HP) as G'. cbn zeta in G'. destruct G' as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || lia.
          - pose proof (quar_chunk bt st Lc FF W (p - 16) n HQ HP) as G'. cbn zeta in G'. replace (p - 16 + 16) with p in G' by lia.
            destruct G' as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || lia. }
        destruct K as (K1 & K2 & K3). unfold prim_alloc_beg in *.
        pose proof (csize_class_of (needed n)) as CC. unfold blk_class in *.
        assert (NB : 1 <= needed n <= 65536) by (pose proof HP as HP2; unfold is_primary in HP2; apply Z.leb_le in HP2; unfold needed in *; lia).
        specialize (CC NB). assert (EN : needed n = rounded n + rz n) by reflexivity.
        apply (CHKoff (class_of (needed n)) (p - rz n) K2 K1). clear -Hi0 CC EN. lia.
      - assert (K : exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n).
        { destruct Hown as [HL|HQ]; [exact (live_sec bt st Lc FF W p n HL HP)|].
          destruct (quar_sec bt st Lc FF W (p - 16) n HQ HP) as (sc & A & B & C0). exists sc. repeat split; try assumption. lia. }
        destruct K as (sc & Hsc & Eu & En). destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). subst p n. unfold sc_mapsz in *.
        pose proof (RoundUp_ge (sec_needed (sc_n sc)) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as RU. unfold sec_map_size, sec_needed, sc_user, sec_user_off in *.
        clear -Hi0 A1 A2 RU RG1 RG2 RZ. ulia. }
    destruct Hsupp as [HC | HW].
    - (* [comment removed for export] *)
      unfold rep_cells in HC.
      destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
      + exact (IMGoff (img_kinds bt st Lc FF W i (or_introl K))).
      + destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN|NI].
        * apply (FIXoff _ _ IN8); clear -IN SS1 SS3; lia.
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact K | exact NI]))).
      + unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
        destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIXoff _ _ INT); clear -K; ulia | apply (FIXoff _ _ INC); clear -K; lia].
      + destruct K as (c0 & Hc0 & K). unfold foot_region in K.
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        apply SPCoff. unfold fa_beg, KFAOFF in *. destruct K as [[K _]|K]; clear -K Q1 Q2 Q5 Q6 Q7 Q9 Q10; ulia.
      + destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (CHKoff BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb). change (csize BATCHCLASS) with 8192. unfold BATCHCAP in *. lia.
      + destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)). unfold sc_mapsz in *. ulia.
      + destruct K as (p & n & Hown & K). unfold foot_hdr in K. pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        apply (BLKoff p n Hown). lia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; right; left; exact K))).
      + destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
        pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
        destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); rewrite Eb; lia | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
      + unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
        1-3: apply (FIXoff _ _ INFS); clear -K; ulia.
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact K))).
        * apply (FIXoff _ _ (dtls_member bt st Lc FF W)); clear -K; ulia.
      + destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
        apply (FIXoff _ _ INFS); ulia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact K))).
      + destruct K as (c0 & Hc0 & K). unfold foot_shreg, sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
        destruct K as [[K _]|K]; (apply (BANDoff SB); [lia | clear -K Q1 Q2 Q8 X14; Zlia | clear -K Q1 Q2 Q5 Q6 Q8 X15; Zlia]).
      + destruct K as (sc & Hs' & K). unfold foot_shsec, sh_lo in K. destruct K as [K _]. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 5 right; exact K))).
    - (* [comment removed for export] *)
      unfold rep_wr in HW.
      destruct HW as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]].
      + apply (FIXoff _ _ IN8); clear -K SS1 SS3; lia.
      + apply (FIXoff _ _ INT); ulia.
      + destruct K as (c0 & Hc0 & K). pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        apply SPCoff. unfold fa_beg, KFAOFF in *. destruct K as [K|[K|K]]; clear -K Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q9 Q10; ulia.
      + destruct K as (b & Hb & K). destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (CHKoff BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb). change (csize BATCHCLASS) with 8192. unfold BATCHSZ in *. lia.
      + destruct K as (sc & Hs' & K). apply (DYNoff _ _ (sec_dyn st sc Hs')). exact K.
      + destruct K as (p & n & Hin & K). pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        destruct K as [K|K]; [apply (BLKoff p n (or_introl Hin)); lia|].
        destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). unfold sh_lo, sh_hi in K.
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + destruct K as (m & n & Hq & K). pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        apply (BLKoff (m + 16) n); [right; replace (m + 16 - 16) with m by lia; exact Hq | lia].
      + destruct K as (b & Hb & K). destruct Hb as [Eb | Hnb]; [apply (FIXoff _ _ INN); rewrite Eb; lia | apply (DYNoff _ _ (node_dyn st b Hnb)); lia].
      + destruct K as (b & Hb & K). destruct Hb as [Eb | Hsb]; [apply (FIXoff _ _ INS); rewrite Eb; lia | apply (DYNoff _ _ (store_dyn st b Hsb)); lia].
      + apply (FIXoff _ _ INFS); ulia.
      + destruct K as (f & k & Hf & K). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _). unfold sh_lo, sh_hi in K.
        apply (BANDoff SB); [lia | clear -K A1 X5; Zlia | clear -K A2 X6; Zlia].
      + destruct K as (c0 & Hc0 & K). unfold sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). apply (BANDoff SB); [lia | clear -K Q1 X14; Zlia | clear -K Q1 Q2 Q5 X15; Zlia].
      + destruct K as (sc & Hs' & K). unfold sh_lo in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + unfold shmaps, AS_GAPLO, AS_GAPHI in K. apply (BANDoff AS_LO); ulia.
  Qed.
End Apart.
