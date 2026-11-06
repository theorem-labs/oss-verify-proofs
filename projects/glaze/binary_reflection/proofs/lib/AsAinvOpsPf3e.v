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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
#[local] Ltac lia ::= am_lia.

Section Pf.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma flags_disj : forall k k', 0 <= k <= 10 -> 0 <= k' <= 10 -> k < k' -> fake_flags_off k + FCAP k <= fake_flags_off k'.
  Proof using.
    intros k k' Hk Hk' LT. (lazymatch goal with |- ?G => let G' := eval unfold fake_flags_off, FCAP in G in change_no_check G' end).
    assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
    assert (K' : k' = 0 \/ k' = 1 \/ k' = 2 \/ k' = 3 \/ k' = 4 \/ k' = 5 \/ k' = 6 \/ k' = 7 \/ k' = 8 \/ k' = 9 \/ k' = 10) by lia.
    destruct K as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]];
    destruct K' as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
  Qed.

  Lemma flag_addr_inj : forall fs k pos k' pos', 0 <= k <= 10 -> 0 <= pos < FCAP k -> 0 <= k' <= 10 -> 0 <= pos' < FCAP k' ->
    fake_flag_addr fs k pos = fake_flag_addr fs k' pos' -> k = k' /\ pos = pos'.
  Proof using.
    intros fs k pos k' pos' Hk Hp Hk' Hp' E. unfold fake_flag_addr in E.
    destruct (Z.lt_trichotomy k k') as [LT|[EQ|GT]].
    - pose proof (flags_disj k k' Hk Hk' LT). lia.
    - subst k'. lia.
    - pose proof (flags_disj k' k Hk' Hk GT). lia.
  Qed.

  Lemma ffa_inj_pos : forall fs k pos pos', 0 <= k -> fake_frame_addr fs k pos = fake_frame_addr fs k pos' -> pos = pos'.
  Proof using.
    intros fs k pos pos' Hk E. unfold fake_frame_addr, FS in E. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia.
  Qed.

  Theorem OPS_REP_fake_release_pf : OPS_REP_fake_release bt.
  Proof using.
    intros st Lc FF F1 F2 M M' mdl f k W R HFF AGR BZ. (lazymatch goal with |- ?G => let G' := eval unfold op_fake_release in G in change_no_check G' end).
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & (LV1 & LV2 & LV3) & (K1 & K2 & K3) & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    assert (Hf : In (f, k) FF) by (rewrite HFF; apply in_app_iff; right; left; reflexivity).
    destruct (fake_frame_facts bt st Lc FF W f k Hf) as (Q1 & Q2 & Q3 & Q4 & F5 & F6 & F7). clear Q3.
    set (flag := fake_flag_addr (bt_fs bt) k (fpos bt f k)) in *.
    pose proof (flag_addr_range (bt_fs bt) k (fpos bt f k) ltac:(unfold KMAXCLASS in F5; lia) F6) as FR. fold flag in FR.
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF. cbn beta in AGF.
    assert (NDF : List.NoDup (F1 ++ (f, k) :: F2)) by (rewrite <- HFF; exact K2).
    assert (INF : forall x, In x (F1 ++ F2) -> In x FF /\ x <> (f, k)) by (intros x Hx; rewrite HFF; apply (in_remove_mid F1 F2 (f, k) x NDF); exact Hx).
    (* [comment removed for export] *)
    assert (AGZ : forall i, 0 <= i < 2 ^ 64 -> ~ (bt_fs bt + 0x1000 <= i < bt_fs bt + 0x9000) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr Ni. apply AGF; [| exact Hr]. intros ->. exact (Ni FR). }
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
    destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((FD1 & FD2 & FD3 & _ & FD5) & _). box FD5.
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [ulia|]. intros X.
      destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_fixed bt st _ _ i INFS ltac:(ulia))) as (_ & _ & NH & _). exact (NH Hi). }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGfree i Hi). }
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> FAKE_SIZE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen i Hi Hr. destruct (fs_vs_fixed bt st Lc FF W lo hi Hlo Hlen); apply AGZ; ulia. }
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo i Hi Hr. destruct (fs_vs_dyn bt st Lc FF W lo hi Hlo); apply AGZ; ulia. }
    pose proof (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)) as FSP.
    assert (SPCfree : forall i, SBEG <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) by (intros i Hi; apply AGZ; ulia).
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hfh Hr.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hfh) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')]; [apply SPCfree; ulia|].
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply (DYNfree _ _ (sec_dyn st sc' Hs')); ulia. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in YC. destruct (YC c0 Hc0).
             exact (IMGK i (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) ltac:(lia)). }
    split. { pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _).
             eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXfree _ _ IN8); ulia.
             - exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) Hr). }
    split. { eapply rep_thread_frame; [exact DEF | exact R3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in Hi.
             destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]]; first [apply (FIXfree _ _ INT); ulia | apply (FIXfree _ _ INC); ulia]. }
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. apply SPCfree. ulia. }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). ulia. }
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> foot_batch b0 i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3). apply SPCfree. ulia. }
    split. { eapply rep_batches_frame; [exact DEF | exact R5 | intros b0 Hb0; apply BR; apply in_app_iff; left; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; left; exact Hb0 | exact Hi | exact Hr]. }
    split. { eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | exact Hi | exact Hr]. }
    split. { eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNfree _ _ (sec_dyn st sc Hs)); ulia. }
    split. { eapply rep_headers_frame; [exact DEF | exact R8 | | |].
             - intros p' n' Hin. destruct (live_range bt st Lc FF W p' n' Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n'). ulia.
             - intros m n' Hin. destruct (quar_item_range bt st Lc FF W m n' Hin) as (A1 & A2 & A3). pose proof (rz_range n'). ulia.
             - exact HDRfree. }
    split. { eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { destruct R10 as (KH & KG & KF & KW & KWR & KT & KS & KD1 & KD2). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. (lazymatch goal with |- ?G => let G' := eval unfold rep_fake in G in change_no_check G' end). change (a_hint (op_fake_release st)) with (a_hint st).
             split. { intros k0 Hk0. pose proof (KH k0 Hk0) as C. eapply (cellZ_frame _ _ _ _ _ _ C); [ulia | ulia | intros i Hi; apply AGZ; ulia]. }
             split. { eapply (byteZ_frame _ _ _ _ _ KG); [ulia | ulia | apply AGZ; ulia]. }
             split. { intros k' pos' Hk' Hp'. pose proof (flag_addr_range (bt_fs bt) k' pos' Hk' Hp') as FR'.
                      destruct (Z.eq_dec (fake_flag_addr (bt_fs bt) k' pos') flag) as [EQ | NE].
                      - (* [comment removed for export] *)
                        destruct (flag_addr_inj (bt_fs bt) k' pos' k (fpos bt f k) Hk' Hp' ltac:(unfold KMAXCLASS in F5; lia) F6 EQ) as [-> ->].
                        rewrite EQ. replace (existsb _ (F1 ++ F2)) with false; [exact BZ|].
                        symmetry. apply Bool.not_true_iff_false. intros EX. apply existsb_exists in EX. destruct EX as ([f2 k2] & Hin2 & P2).
                        cbn [fst snd] in P2. apply andb_prop in P2. destruct P2 as [P2a P2b]. apply Z.eqb_eq in P2a. apply Z.eqb_eq in P2b. subst k2.
                        rewrite <- F7 in P2a. subst f2. exact (proj2 (INF _ Hin2) eq_refl).
                      - pose proof (KF k' pos' Hk' Hp') as C.
                        replace (existsb _ (F1 ++ F2)) with (existsb (fun fk : Z * Z => (fst fk =? fake_frame_addr (bt_fs bt) k' pos') && (snd fk =? k')) FF).
                        + eapply (byteZ_frame _ _ _ _ _ C); [ulia | ulia |]. apply AGF; [| ulia]. intros E. exact (NE E).
                        + rewrite HFF. rewrite existsb_app_mid. replace ((fst (f, k) =? fake_frame_addr (bt_fs bt) k' pos') && (snd (f, k) =? k')) with false; [reflexivity|].
                          (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). symmetry. apply Bool.not_true_iff_false. intros P. apply andb_prop in P. destruct P as [Pa Pb].
                          apply Z.eqb_eq in Pa. apply Z.eqb_eq in Pb. subst k'. apply NE. (lazymatch goal with |- ?G => let G' := eval unfold flag in G in change_no_check G' end). f_equal.
                          rewrite F7 in Pa. symmetry. exact (ffa_inj_pos (bt_fs bt) k (fpos bt f k) pos' ltac:(unfold KMAXCLASS in F5; lia) Pa). }
             split. { intros f' k' Hin'. destruct (INF _ Hin') as [Hin2 NE2]. pose proof (KW f' k' Hin2) as C.
                      destruct (fake_frame_facts bt st Lc FF W f' k' Hin2) as (G1 & G2 & G3 & G4 & _).
                      eapply (cellZ_frame _ _ _ _ _ _ C); [ulia | ulia | intros i Hi; apply AGZ; ulia]. }
             split; [frW DEF KWR|]. split; [eapply (cellZ_frame _ _ _ _ _ _ KT); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; cbn in Hi; lia)) ltac:(ulia))]|].
             split; [eapply (cellZ_frame _ _ _ _ _ _ KS); [ulia | ulia | intros i Hi; apply AGZ; ulia]|].
             split; [eapply (cellZ_frame _ _ _ _ _ _ KD1); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; cbn in Hi; lia)) ltac:(ulia))]|].
             eapply (cellZ_frame _ _ _ _ _ _ KD2); [ulia | ulia | intros i Hi; apply (FIXfree _ _ (dtls_member bt st Lc FF W)); [(lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, PG in G in change_no_check G' end); lia | cbn in Hi; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | ulia]]. }
    split. { eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    split. { eapply (rep_shadow_frame_grow bt st Lc Lc); [exact DEF | exact R12 | intros g Hg; exact Hg | | | |].
             - intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _). ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A3 A4 A5 A6 A7. try ceil; unfold PG, AS_HEAPLO, NMAX in *. Ztac.
             - intros c0 i Hc0 Hi Hr. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
               unfold foot_shreg, sh_lo in Hi. apply AGZ; [exact Hr|]. clear -Hi E1 E2 E5 E6 E8 X5 X6 FD5 SBH X15. Zlia.
             - intros sc i Hs Hi Hr. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). unfold foot_shsec, sh_lo in Hi. apply AGZ; [exact Hr|].
               clear -Hi A1 A2 X5 X6 FD5. Zlia. }
    split; [exact R13|]. split; [exact R14|].
    split. { intros p' n' Hin'. destruct (R15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f' k' Hin'. destruct (INF _ Hin') as [Hin2 _]. frW DEF (R16 f' k' Hin2). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia)) ltac:(ulia))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia)) ltac:(ulia))] |].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.

  Theorem OPS_REP_fake_alloc_pf : OPS_REP_fake_alloc bt.
  Proof using.
    intros st Lc FF M M' mdl mdl' k pos newhint W R Hk Hpos Hnh. cbn zeta. intros NI AGR CH BF FLG CW SHD SBM MI.
    set (f := fake_frame_addr (bt_fs bt) k pos) in *.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & (LV1 & LV2 & LV3) & (K1 & K2 & K3) & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (WF_fake_alloc bt st Lc FF k pos newhint W Hk Hpos ltac:(lia) NI) as W'. fold f in W'.
    pose proof (frame_geom k pos (bt_fs bt) Hk Hpos X7) as FG. cbn zeta in FG. fold f in FG. destruct FG as (FG1 & FG2 & FG3 & FG4 & FG5 & FG6).
    pose proof (flag_addr_range (bt_fs bt) k pos ltac:(unfold KMAXCLASS in Hk; lia) Hpos) as FR.
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    (* [comment removed for export] *)
    assert (AGZ : forall i, 0 <= i < 2 ^ 64 -> ~ (bt_fs bt <= i < bt_fs bt + FAKE_SIZE) -> ~ (SB <= i < AS_HEAPLO) -> i < CEIL -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr N1 N2 N3. apply AGF; [| exact Hr]. intros Hf. unfold foot_fake_alloc, sh_lo, sh_hi in Hf. clear -Hf N1 N2 N3 Hk FG1 FG2 X5 X6 Hr. unfold KMAXCLASS in Hk. Zlia. }
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
    destruct (RNG _ _ (all_ranges_fixed bt st _ INFS)) as ((FD1 & FD2 & FD3 & _ & FD5) & _). box FD5.
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [ulia| | ulia | ulia]. intros X.
      destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_fixed bt st _ _ i INFS X)) as (_ & _ & NH & _). exact (NH Hi). }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGfree i Hi). }
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> FAKE_SIZE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _). clear A4.
      destruct (fs_vs_fixed bt st Lc FF W lo hi Hlo Hlen); destruct A5; apply AGZ; ulia. }
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _). clear A4.
      destruct (fs_vs_dyn bt st Lc FF W lo hi Hlo); destruct A5; apply AGZ; ulia. }
    pose proof (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)) as FSP.
    assert (SPCfree : forall i, SBEG <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) by (intros i Hi; apply AGZ; ulia).
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hfh Hr.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hfh) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')]; [apply SPCfree; ulia|].
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply (DYNfree _ _ (sec_dyn st sc' Hs')); ulia. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    (lazymatch goal with |- ?G => let G' := eval unfold op_fake_alloc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in YC. destruct (YC c0 Hc0).
             exact (IMGK i (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) ltac:(lia)). }
    split. { change (rep_instance bt st M'). pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _).
             eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI8].
             - apply (FIXfree _ _ IN8); ulia.
             - exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI8])) Hr). }
    split. { change (rep_thread bt st M'). eapply rep_thread_frame; [exact DEF | exact R3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in Hi.
             destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]]; first [apply (FIXfree _ _ INT); ulia | apply (FIXfree _ _ INC); ulia]. }
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg (set_hint st k newhint) c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. apply SPCfree. ulia. }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). ulia. }
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> foot_batch b0 i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3). apply SPCfree. ulia. }
    split. { change (a_tq (set_hint st k newhint)) with (a_tq st). eapply rep_batches_frame; [exact DEF | exact R5 | intros b0 Hb0; apply BR; apply in_app_iff; left; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; left; exact Hb0 | exact Hi | exact Hr]. }
    split. { change (a_gq (set_hint st k newhint)) with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | exact Hi | exact Hr]. }
    split. { change (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNfree _ _ (sec_dyn st sc Hs)); ulia. }
    split. { change (rep_headers bt st Lc M'). eapply rep_headers_frame; [exact DEF | exact R8 | | |].
             - intros p' n' Hin. destruct (live_range bt st Lc FF W p' n' Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n'). ulia.
             - intros m n' Hin. destruct (quar_item_range bt st Lc FF W m n' Hin) as (A1 & A2 & A3). pose proof (rz_range n'). ulia.
             - exact HDRfree. }
    split. { change (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { destruct R10 as (KH & KG & KF & KW & KWR & KT & KS & KD1 & KD2). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. (lazymatch goal with |- ?G => let G' := eval unfold rep_fake in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_hint set_hint] in G in change_no_check G' end).
             split. { intros k0 Hk0. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec k0 k) as [-> | NE]; [exact CH|].
                      pose proof (KH k0 Hk0) as C. eapply (cellZ_frame _ _ _ _ _ _ C); [ulia | ulia |]. intros i Hi. apply AGF; [| ulia].
                      intros Hf. unfold foot_fake_alloc, sh_lo, sh_hi in Hf. clear -Hf Hi NE Hk Hk0 FG1 FG2 X5 X6 FD5. unfold KMAXCLASS in Hk. Zlia. }
             split. { eapply (byteZ_frame _ _ _ _ _ KG); [ulia | ulia |]. apply AGF; [| ulia].
                      intros Hf. unfold foot_fake_alloc, sh_lo, sh_hi in Hf. clear -Hf Hk FG1 FG2 X5 X6 FD5. unfold KMAXCLASS in Hk. Zlia. }
             split. { intros k' pos' Hk' Hp'. (lazymatch goal with |- ?G => let G' := eval cbn [existsb fst snd] in G in change_no_check G' end). pose proof (flag_addr_range (bt_fs bt) k' pos' Hk' Hp') as FR'.
                      destruct (Z.eq_dec k' k) as [-> | NK].
                      - destruct (Z.eq_dec pos' pos) as [-> | NP].
                        + replace ((f =? fake_frame_addr (bt_fs bt) k pos) && (k =? k)) with true by ((lazymatch goal with |- ?G => let G' := eval unfold f in G in change_no_check G' end); rewrite !Z.eqb_refl; reflexivity). (lazymatch goal with |- ?G => let G' := eval cbn [orb] in G in change_no_check G' end). exact BF.
                        + replace ((f =? fake_frame_addr (bt_fs bt) k pos') && (k =? k)) with false.
                          * (lazymatch goal with |- ?G => let G' := eval cbn [orb] in G in change_no_check G' end). pose proof (KF k pos' Hk' Hp') as C. eapply (byteZ_frame _ _ _ _ _ C); [ulia | ulia |]. apply FLG; [exact Hk' | exact Hp' | congruence].
                          * symmetry. apply Bool.andb_false_iff. left. apply Z.eqb_neq. intros E. apply NP. symmetry. exact (ffa_inj_pos (bt_fs bt) k pos pos' ltac:(lia) E).
                      - replace ((f =? fake_frame_addr (bt_fs bt) k' pos') && (k =? k')) with false.
                        + (lazymatch goal with |- ?G => let G' := eval cbn [orb] in G in change_no_check G' end). pose proof (KF k' pos' Hk' Hp') as C. eapply (byteZ_frame _ _ _ _ _ C); [ulia | ulia |]. apply FLG; [exact Hk' | exact Hp' | congruence].
                        + symmetry. apply Bool.andb_false_iff. right. apply Z.eqb_neq. congruence. }
             split. { intros f' k' [E | Hin'].
                      - injection E as <- <-. replace (fpos bt f k) with pos; [exact CW|].
                        (lazymatch goal with |- ?G => let G' := eval unfold fpos, f, fake_frame_addr in G in change_no_check G' end). replace (bt_fs bt + 0x9000 + k * 2 ^ 20 + FS k * pos - (bt_fs bt + 0x9000 + k * 2 ^ 20)) with (pos * FS k) by lia.
                        symmetry. apply Z.div_mul. (lazymatch goal with |- ?G => let G' := eval unfold FS in G in change_no_check G' end). assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia.
                      - pose proof (KW f' k' Hin') as C. destruct (fake_frame_facts bt st Lc FF W f' k' Hin') as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
                        assert (NEQ : (k', fpos bt f' k') <> (k, pos)).
                        { intros E. injection E as E1 E2. apply NI. (lazymatch goal with |- ?G => let G' := eval unfold f in G in change_no_check G' end). rewrite <- E1, <- E2, <- G7. exact Hin'. }
                        pose proof (frames_apart (bt_fs bt) k' (fpos bt f' k') k pos X7 G5 G6 Hk Hpos NEQ) as FA. rewrite <- G7 in FA. fold f in FA.
                        eapply (cellZ_frame _ _ _ _ _ _ C); [ulia | ulia |]. intros i Hi. apply AGF; [| ulia].
                        intros Hf. unfold foot_fake_alloc, sh_lo, sh_hi in Hf. clear -Hf Hi FA G1 G2 G4 Hk FG1 FG2 FG4 X5 X6 FD5. unfold KMAXCLASS in Hk. Zlia. }
             split; [frW DEF KWR|]. split; [eapply (cellZ_frame _ _ _ _ _ _ KT); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; cbn in Hi; lia)) ltac:(ulia))]|].
             split. { eapply (cellZ_frame _ _ _ _ _ _ KS); [ulia | ulia |]. intros i Hi. apply AGF; [| ulia].
                      intros Hf. unfold foot_fake_alloc, sh_lo, sh_hi in Hf. clear -Hf Hi Hk FG1 FG2 X5 X6 FD5. unfold KMAXCLASS in Hk. Zlia. }
             split; [eapply (cellZ_frame _ _ _ _ _ _ KD1); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; cbn in Hi; lia)) ltac:(ulia))]|].
             eapply (cellZ_frame _ _ _ _ _ _ KD2); [ulia | ulia | intros i Hi; apply (FIXfree _ _ (dtls_member bt st Lc FF W)); [(lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, PG in G in change_no_check G' end); lia | cbn in Hi; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | ulia]]. }
    split. { change (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    split. { change (rep_shadow bt st Lc M'). eapply (rep_shadow_frame_grow bt st Lc Lc); [exact DEF | exact R12 | intros g Hg; exact Hg | | | |].
             - intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _). ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A3 A4 A5 A6 A7. try ceil; unfold PG, AS_HEAPLO, NMAX in *. Ztac.
             - intros c0 i Hc0 Hi Hr. apply AGF; [| exact Hr]. intros Hf.
               pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
               unfold foot_fake_alloc in Hf. destruct Hf as [Z|[Z|[Z|[Z|Z]]]].
               4: exact (fsh_vs_rep bt (set_hint st k newhint) Lc ((f, k) :: FF) W' f k i ltac:(left; reflexivity) Z
                          ltac:(do 12 right; left; exists c0; split; [exact Hc0 | exact Hi])).
               all: unfold foot_shreg, sh_lo in Hi; clear -Z Hi Hk FG1 FG2 E1 E2 E5 E6 E8 X5 X6 FD5 SBH X15; unfold KMAXCLASS in Hk; Zlia.
             - intros sc i Hs Hi Hr. apply AGF; [| exact Hr]. intros Hf. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
               unfold foot_fake_alloc in Hf. destruct Hf as [Z|[Z|[Z|[Z|Z]]]].
               4: exact (fsh_vs_rep bt (set_hint st k newhint) Lc ((f, k) :: FF) W' f k i ltac:(left; reflexivity) Z
                          ltac:(do 13 right; left; exists sc; split; [exact Hs | exact Hi])).
               all: unfold foot_shsec, sh_lo in Hi; clear -Z Hi Hk FG1 FG2 A1 A2 X5 X6 FD5; unfold KMAXCLASS in Hk; Zlia. }
    split. { change (rep_ledger bt st mdl'). exact (rep_ledger_sbm bt st mdl mdl' SBM R13). }
    split. { destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa a_reg a_sec a_dep a_shsec set_hint] in G in change_no_check G' end).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
             split; [exact B1|]. split; [exact MI|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|]. split; [exact B7|].
             rewrite E3. change (prim_charge (set_hint st k newhint)) with (prim_charge st). change (sec_charge (set_hint st k newhint)) with (sec_charge st).
             change (depot_charge (set_hint st k newhint)) with (depot_charge st). exact B8. }
    split. { intros p' n' Hin'. destruct (R15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f' k' [E | Hin']; [| frW DEF (R16 f' k' Hin')]. injection E as <- <-. apply writableZ_of_def. exact SHD. }
    split; [eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia)) ltac:(ulia))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia)) ltac:(ulia))] |].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.


  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.

End Pf.
