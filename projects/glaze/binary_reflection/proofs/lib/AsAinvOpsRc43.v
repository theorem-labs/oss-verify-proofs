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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section DT.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Definition foot_drain_top (st : ast) (c m : Z) (a : Z) : Prop :=
    (reginfo bt c <= a < reginfo bt c + 8) \/ (reginfo bt c + 16 <= a < reginfo bt c + 24) \/ (reginfo bt c + 72 <= a < reginfo bt c + 128)
    \/ (T + T_PC + PC_SZ * c <= a < T + T_PC + PC_SZ * c + 4)
    \/ (fa_beg SBEG c + 4 * Z.of_nat (length (r_free (a_reg st c))) <= a < fa_beg SBEG c + 4 * (Z.of_nat (length (r_free (a_reg st c))) + m))
    \/ (T + 2768 <= a < T + 3168) \/ CEIL <= a.

  Definition OPS_REP_drain_top : Prop := forall st Lc FF (M M' : mem) mdl mdl' c m (qt qg : Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> 0 <= m <= Z.of_nat (length (a_cache st c)) ->
    4 * (Z.of_nat (length (r_free (a_reg st c))) + m) <= r_mapped_fa (a_reg st c) ->
    let nf := Z.of_nat (length (r_free (a_reg st c))) in
    let moved := skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - m)) (a_cache st c) in
    agrees_off (foot_drain_top st c m) M M' ->
    cellZ SG M' (reginfo bt c) 8 0 ->
    cellZ SG M' (reginfo bt c + 16) 8 (nf + m) ->
    cellZ SG M' (T + T_PC + PC_SZ * c) 4 (Z.of_nat (length (a_cache st c)) - m) ->
    (forall i k, nth_error moved i = Some k -> cellZ SG M' (fa_beg SBEG c + 4 * (nf + Z.of_nat i)) 4 k) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_drain_top st c m) Lc FF M' mdl'.

  Theorem OPS_REP_drain_top_pf : OPS_REP_drain_top.
  Proof using.
    intros st Lc FF M M' mdl mdl' c m qt qg W R Hc Hm0 Hfa. cbn zeta. intros AGR CMU CNF CCNT CFA SBM MI.
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    pose proof (cache_len bt st Lc FF W c Hc) as CL16.
    assert (Hm16 : m <= 16) by lia.
    pose proof (AsAinvOpsR3.split_keep_taken (a_cache st c) m Hm0) as SPL. cbn zeta in SPL.
    set (j := Z.to_nat (Z.of_nat (length (a_cache st c)) - m)) in *.
    set (keep := firstn j (a_cache st c)) in *. set (moved := skipn j (a_cache st c)) in *.
    destruct SPL as (EL & LK & LTk & NK & NT).
    set (nf := Z.of_nat (length (r_free (a_reg st c)))) in *.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf in E7.
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (first [clear - SPH R6a | idtac]; lia).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((TD1 & TD2 & TD3 & TD4 & TD5) & _). box TD4. box TD5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    (* [comment removed for export] *)
    set (RZc := fun i => reginfo bt c <= i < reginfo bt c + 128).
    set (Tz := fun i => (T + T_PC + PC_SZ * c <= i < T + T_PC + PC_SZ * c + 80) \/ (T + 2768 <= i < T + 3168)).
    set (FAz := fun i => fa_beg SBEG c + 4 * nf <= i < fa_beg SBEG c + 4 * (nf + m)).
    assert (FAS : forall i, FAz i -> SBEG <= i < SBEG + KSPACE /\ fa_beg SBEG c <= i < fa_beg SBEG c + r_mapped_fa (a_reg st c)).
    { intros i Hi. unfold FAz in Hi. clear -Hi Hfa E1 E2 E3 E4 E5 E6 E7 Hm0. fold nf in Hfa. ulia. }
    assert (FZ : forall i, foot_drain_top st c m i -> RZc i \/ Tz i \/ FAz i \/ CEIL <= i).
    { intros i Hf. unfold foot_drain_top in Hf. fold nf in Hf. (lazymatch goal with |- ?G => let G' := eval unfold RZc, Tz, FAz in G in change_no_check G' end). destruct Hf as [A|[A|[A|[A|[A|[A|A]]]]]]; clear -A; lia. }
    assert (AGZ : forall i, 0 <= i -> i < CEIL -> ~ RZc i -> ~ Tz i -> ~ FAz i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i H0 H1 N1 N2 N3. apply AGF; [| clear -H0 H1; ulia]. intros Hf. destruct (FZ i Hf) as [A|[A|[A|A]]]; [exact (N1 A) | exact (N2 A) | exact (N3 A) | clear -A H1; ulia]. }
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [clear -Hi I1; ulia | clear -Hi I2; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi I2 E9 SBH; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TD4 Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); Zlia |].
      intros A. destruct (FAS i A) as [A1 _]. clear -A1 Hi I2 SBH. ulia. }
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hlo) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; (first [clear - H0 H Hlen | idtac]; ulia))) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP];
        (apply AGZ; [clear -Hi A1; ulia | clear -Hi A2 A3; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi SP E9 E10; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi D Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | intros A; destruct (FAS i A) as [Q1 _]; clear -Q1 Hi SP; ulia]). }
    assert (FIXfreeT : forall lo hi, In (lo, hi) (bt_fixed bt) -> (hi <= T \/ T + PG <= lo) -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof Hlen as D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP];
        (apply AGZ; [clear -Hi A1; ulia | clear -Hi A2 A3; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi SP E9 E10; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi D Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | intros A; destruct (FAS i A) as [Q1 _]; clear -Q1 Hi SP; ulia]). }
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hlo) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hlo) as [SP|SP];
        (apply AGZ; [clear -Hi A1; ulia | clear -Hi A2 A3; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi SP E9 E10; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi D Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | intros A; destruct (FAS i A) as [Q1 _]; clear -Q1 Hi SP; ulia]). }
    assert (SPCfree : forall i, SBEG <= i < SBEG + KSPACE -> ~ FAz i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi NFA Hr. apply AGZ; [clear -Hi X14; ulia | clear -Hi X15; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi E9; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TPG Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact NFA]. }
    assert (RIfree : forall c', 1 <= c' <= 30 -> c' <> c -> forall i, reginfo bt c' <= i < reginfo bt c' + 128 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c' Hc' NE i Hi Hr. unfold reginfo in *. apply AGZ; [clear -Hi Hc' X14; ulia | clear -Hi Hc' X15; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold reginfo in G in change_no_check G' end); clear -Hi Hc' Hc NE; lia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TPG Hc Hc'; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia |].
      intros A. destruct (FAS i A) as [Q1 _]. clear -Q1 Hi Hc'. ulia. }
    (* [comment removed for export] *)
    assert (CHKfree : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' -> forall i, a' <= i < a' + csize c' -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c' a' Hc' CVa i Hi Hr. destruct (carved_range bt st Lc FF W c' a' Hc' CVa) as (D1 & D2 & D3 & D4 & _).
      apply SPCfree; [clear -Hi D3 D4; lia | | exact Hr]. intros A. destruct (FAS i A) as [_ Q2].
      pose proof (region_facts bt st Lc FF W c' Hc') as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c c') as [LT|[EQ|GT]].
      * assert (c * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H Hi Q2 D1 D2 E6. lia.
      * subst c'. clear -Hi Q2 D1 D2 F2 F3. lia.
      * assert (c' * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c' * 2 ^ 32 + 2 ^ 32) with ((c' + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        destruct (WR1 c' Hc') as (R1' & _ & R3' & _). unfold KREGION_EXHAUST, KUSERMAP in R3'. clear -H Hi Q2 D1 D2 F2 F3 R1' R3'. lia. }
    assert (FAother : forall c0, 1 <= c0 <= 30 -> c0 <> c -> forall i, fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c0 Hc0 NE i Hi Hr. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & F6 & _).
      apply SPCfree; [clear -Hi F1 F2 F3 F4 F5 F6; ulia | | exact Hr]. intros A. destruct (FAS i A) as [_ Q2].
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c c0) as [LT|[EQ|GT]]; [| exact (NE (eq_sym EQ)) |].
      * assert (c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H Hi Q2 E6 F6. lia.
      * assert (c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H Hi Q2 E6 F6. lia. }
    (* [comment removed for export] *)
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    pose proof ceil_rng as CR. pose proof ceil_pg as CP. unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold op_drain_top in G in change_no_check G' end). cbn zeta. fold j. fold keep. fold moved.
    (lazymatch goal with |- ?G => let G' := eval unfold set_cache, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end).
    set (r' := REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c)) (r_free (a_reg st c) ++ moved) (r_uhole (a_reg st c)) (r_fhole (a_reg st c))).
    set (st' := AST (fupdZ (a_reg st) c r') (a_cinit st) (fupdZ (a_cache st) c keep) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st)
                    (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st)).
    assert (RMU : forall c0, r_mapped_user (a_reg st' c0) = r_mapped_user (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    assert (RFA : forall c0, r_mapped_fa (a_reg st' c0) = r_mapped_fa (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    assert (RUH : forall c0, r_uhole (a_reg st' c0) = r_uhole (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    assert (RFH : forall c0, r_fhole (a_reg st' c0) = r_fhole (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi.
             destruct (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) as [LT _]. exact (IMGfree i LT). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXfree _ _ IN8); [ulia | ulia | clear -IN S1 S3; ulia | exact Hr].
             - destruct (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) as [LT _]. exact (IMGfree i LT). }
    (* [comment removed for export] *)
    split. { destruct R3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st). change (a_cinit st') with (a_cinit st). change (a_cache st') with (fupdZ (a_cache st) c keep).
             assert (AGT : forall i, ((T <= i < T + T_PC + PC_SZ * c \/ T + T_PC + PC_SZ * c + 4 <= i < T + 2768 \/ T + 3168 <= i < T + PG)
                                     \/ (bt_tctx bt <= i < bt_tctx bt + 160)) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. destruct Hi as [Hi | Hi].
               - apply AGF; [| exact Hr]. intros Hf. unfold foot_drain_top in Hf. fold nf in Hf. unfold reginfo, T_PC, PC_SZ in *.
                 destruct Hf as [A|[A|[A|[A|[A|[A|A]]]]]]; try (clear -A Hi Hc TPG E9 X1 X2; ulia).
                 assert (FA' : FAz i) by exact A. destruct (FAS i FA') as [Q1 _]. clear -Q1 Hi Hc TPG X1 X2. ulia.
               - apply (FIXfree _ _ INC); [ulia | ulia | clear -Hi; lia | exact Hr]. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { eapply rep_list_frame; [exact TL | ulia | ulia |]. intros i Hi Hr. apply AGT; [| exact Hr]. left. clear -Hi Hc. lia. }
             split. { intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
                      - destruct (TP c Hc) as (Q1 & Q2 & Q3 & Q4). (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass in G in change_no_check G' end). unfold T_PC, PC_SZ in *.
                        split; [rewrite LK; exact CCNT|].
                        split. { eapply (cellZ_frame _ _ _ _ _ _ Q2); [clear -X1 Hc; ulia | clear -X2 Hc; ulia |]. intros i Hi. cbn in Hi. apply AGT; [left; right; left; clear -Hi Hc; lia | clear -Hi X1 X2 Hc; ulia]. }
                        split. { eapply (cellZ_frame _ _ _ _ _ _ Q3); [clear -X1 Hc; ulia | clear -X2 Hc; ulia |]. intros i Hi. cbn in Hi. apply AGT; [left; right; left; clear -Hi Hc; lia | clear -Hi X1 X2 Hc; ulia]. }
                        intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. rewrite (NK i Hl) in Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl2.
                        eapply (cellZ_frame _ _ _ _ _ _ (Q4 i k Hk)); [clear -X1 Hc; ulia | clear -X2 Hc Hl2 CL16; ulia |]. intros i0 Hi0. cbn in Hi0.
                        apply AGT; [left; right; left; clear -Hi0 Hc Hl2 CL16; lia | clear -Hi0 X1 X2 Hc Hl2 CL16; ulia].
                      - pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                        eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -Hc' X1; ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -Hc' X2; ulia | exact CL' |].
                        (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros i Hi Hr. apply AGT; [| exact Hr]. left. clear -Hi Hc' Hc NE. lia. }
             split; [frW DEF TW|]. split; [frZ AGT TC1|]. split; [frZ AGT TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. change (a_reg st') with (fupdZ (a_reg st) c r'). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [-> | NE].
             - destruct (R4 c Hc) as [G0 F0]. destruct G0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). destruct F0 as (F1 & F2 & F3). (lazymatch goal with |- ?G => let G' := eval unfold r' in G in change_no_check G' end).
               assert (AGR' : forall i, (reginfo bt c + 8 <= i < reginfo bt c + 16 \/ reginfo bt c + 24 <= i < reginfo bt c + 72) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
               { intros i Hi Hr. apply AGF; [| exact Hr]. intros Hf. unfold foot_drain_top in Hf. fold nf in Hf. unfold reginfo, T_PC, PC_SZ in *.
                 destruct Hf as [A|[A|[A|[A|[A|[A|A]]]]]]; try (clear -A Hi Hc TPG E9 E10 X1 X2 X15; ulia).
                 assert (FA' : FAz i) by exact A. destruct (FAS i FA') as [Q1 _]. clear -Q1 Hi Hc. ulia. }
               split.
               + unfold rep_reginfo in *. cbn zeta in *. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_alloc_user r_mapped_user] in G in change_no_check G' end). unfold KSPACE, PG in E9, E10.
                 split; [exact CMU|]. split; [frZ AGR' G2|]. split; [rewrite length_app, Nat2Z.inj_add, LTk; exact CNF|]. split; [frZ AGR' G4|]. split; [frZ AGR' G5|].
                 split; [frZ AGR' G6|]. split; [frZ AGR' G7|]. split; [frZ AGR' G8|]. destruct G9 as [G9a G9b]. split; [frB AGR' G9a | frW DEF G9b].
               + (lazymatch goal with |- ?G => let G' := eval unfold rep_freearray in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_mapped_user] in G in change_no_check G' end). split; [| split; [frW DEF F2 | frW DEF F3]].
                 intros i k Hk. destruct (Nat.lt_ge_cases i (length (r_free (a_reg st c)))) as [LT | GE].
                 * rewrite nth_error_app1 in Hk by exact LT. pose proof (F1 i k Hk) as C.
                   eapply (cellZ_frame _ _ _ _ _ _ C); [clear -E1 E2 E3 E4 X14; ulia | clear -LT E5 E6 E7 X15; unfold nf in *; ulia |].
                   intros i0 Hi0. cbn in Hi0. apply SPCfree; [clear -Hi0 LT E1 E2 E3 E4 E5 E6 E7; unfold nf in *; ulia | (lazymatch goal with |- ?G => let G' := eval unfold FAz, nf in G in change_no_check G' end); clear -Hi0 LT; lia | clear -Hi0 LT E1 E2 E3 E4 E5 E6 E7 X14 X15; unfold nf in *; ulia].
                 * rewrite nth_error_app2 in Hk by exact GE. pose proof (CFA _ k Hk) as C.
                   replace (fa_beg SBEG c + 4 * Z.of_nat i) with (fa_beg SBEG c + 4 * (nf + Z.of_nat (i - length (r_free (a_reg st c))))) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); (first [clear - GE | idtac]; lia)). exact C.
             - destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
               destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _).
               eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | (first [clear - D9 X14 | idtac]; ulia) | (first [clear - D10 X15 | idtac]; ulia) | (first [clear - D4 D3 D2 D1 X14 | idtac]; ulia) | (first [clear - D6 D5 X15 | idtac]; ulia) | (first [clear - D7 | idtac]; ulia) |].
               intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi]; [apply (RIfree c0 Hc0 NE); [clear -Hi; lia | exact Hr] | apply (FAother c0 Hc0 NE); [clear -Hi D7; lia | exact Hr]]. }
    (* [comment removed for export] *)
    assert (BAfree : forall q, rep_batches bt M q -> (forall b, In b q -> In b (a_tq st ++ a_gq st)) -> rep_batches bt M' q).
    { intros q RB SUB. eapply rep_batches_frame; [exact DEF | exact RB | |].
      - intros b Hb. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & B1 & B2). ulia.
      - intros b i Hb Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (CVb & BL & B1 & B2).
        apply (CHKfree BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [change (csize BATCHCLASS) with 8192; clear -Hi BL; ulia | exact Hr]. }
    split; [change (a_tq st') with (a_tq st); apply (BAfree _ R5); intros b Hb; apply in_app_iff; left; exact Hb|].
    split; [change (a_gq st') with (a_gq st); apply (BAfree _ R6); intros b Hb; apply in_app_iff; right; exact Hb|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNfree _ _ (sec_dyn st sc Hs)); [ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_headers bt st' Lc M') with (rep_headers bt st Lc M'). destruct R8 as [HLh HQh].
             assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
               destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
               - apply (CHKfree (blk_class n') (prim_alloc_beg p' n') HC' CV'); [unfold prim_alloc_beg in *; clear -W1 W2 W3 W4 N1' RZ'; lia | exact Hr].
               - apply (DYNfree _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
                 rewrite Eu', En' in *. ulia. }
             split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n').
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | ulia | ulia |]. intros i Hi Hr. exact (HDRfree p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (B1 & B2 & B3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -B1 B2 B3 RZn; ulia | clear -B1 B2 B3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRfree (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) as [LT _]. exact (IMGfree i LT).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); ulia.
               + destruct (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) as [LT _]. exact (IMGfree i LT).
               + apply (FIXfreeT _ _ (dtls_member bt st Lc FF W) (dtls_vs_thread bt st Lc FF W)); ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); (first [clear - A4 A2 A1 Hi Hr | idtac]; ulia). }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) as [LT _]. exact (IMGfree i LT). }
    (* [comment removed for export] *)
    split. { destruct R12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (quar st') with (quar st).
             assert (AGS : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. apply AGZ; [clear -Hi; ulia | clear -Hi; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi E9 SBH; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TD5 Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); Zlia | intros A; destruct (FAS i A) as [Q1 _]; clear -Q1 Hi SBH; ulia]. }
             assert (SHR : forall lo hi g, lo / 8 <= g < hi / 8 -> 0 <= lo -> hi <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo hi g Hg Hg0 Hg1. clear -Hg Hg0 Hg1. Zlia. }
             split. { intros c0 g Hc0 Hg NL'. rewrite RMU in Hg. pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros c0 g Hc0 Hg. rewrite RFA in Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros sc g Hs HQ HU. pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros c0 g Hc0 Hg. rewrite RMU in Hg. exact (def_keep M M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep M M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { pose proof (rep_ledger_sbm bt st mdl mdl' SBM R13) as (L1 & L2 & L3 & L4 & L5). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (dyn_maps st') with (dyn_maps st). change (a_dep st') with (a_dep st).
             assert (COMM : forall a, committed bt st' a <-> committed bt st a).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_nres st') with (a_nres st). split.
               - intros [(c1 & Hc1 & X) | X]; [left; exists c1; rewrite RMU, RFA in X; exact (conj Hc1 X) | right; exact X].
               - intros [(c1 & Hc1 & X) | X]; [left; exists c1; rewrite RMU, RFA; exact (conj Hc1 X) | right; exact X]. }
             assert (HOL : forall a, holes bt st' a <-> holes bt st a).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end). split.
               - intros (c1 & Hc1 & X). exists c1. rewrite RMU, RFA, RUH, RFH in X. exact (conj Hc1 X).
               - intros (c1 & Hc1 & X). exists c1. rewrite RMU, RFA, RUH, RFH. exact (conj Hc1 X). }
             split. { destruct L1 as (F6 & P1 & P2 & P3 & P4). exists F6. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
                      intros a Ha. rewrite (HOL a). exact (P4 a Ha). }
             split; [intros a; rewrite (COMM a), (HOL a); exact (L2 a)|]. split; [intros a; rewrite (COMM a), (HOL a); exact (L3 a)|].
             split; [exact L4 | exact L5]. }
    (* [comment removed for export] *)
    split. { destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3').
             split; [exact B1|]. split; [exact MI|]. split; [exact B3|]. split; [exact B4|].
             split. { intros c0 Hc0. rewrite RMU, RFA. exact (B5 c0 Hc0). }
             split; [exact B6|]. split; [exact B7|].
             rewrite E3'. change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st).
             assert (PC : prim_charge st' = prim_charge st).
             { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end).
               assert (EQ : forall k, sum_classes (fun c0 : Z => r_mapped_user (a_reg st' c0) + r_mapped_user (a_reg st' c0) / 8 + r_mapped_fa (a_reg st' c0) + r_mapped_fa (a_reg st' c0) / 8) k
                                  = sum_classes (fun c0 : Z => r_mapped_user (a_reg st c0) + r_mapped_user (a_reg st c0) / 8 + r_mapped_fa (a_reg st c0) + r_mapped_fa (a_reg st c0) / 8) k).
               { induction k as [|k IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH, RMU, RFA. reflexivity. }
               apply EQ. }
             rewrite PC. exact B8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (R15 p' n' Hin') as [V1 V2]. split; [frW DEF V1 | frW DEF V2]. }
    split. { intros f k0 Hf. frW DEF (R16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia | intros i Hi; exact (IMGfree i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia))))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia | intros i Hi; exact (IMGfree i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia))))] |].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.

  (* [comment removed for export] *)
  Lemma foot_drain_top_not_XB : forall st Lc FF (qt qg : Z) c m z, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> 0 <= m ->
    4 * (Z.of_nat (length (r_free (a_reg st c))) + m) <= r_mapped_fa (a_reg st c) -> foot_drain_top st c m z -> ~ XB bt st z.
  Proof using.
    intros st Lc FF qt qg c m z W Hc Hm Hfa Hf HX.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    unfold foot_drain_top in Hf. destruct Hf as [A|[A|[A|[A|[A|[A|A]]]]]].
    1-3: destruct (XB_zone bt st Lc FF W z HX) as [[HI _] | [HS _]]; [clear -A HI E9 I2 B3; ulia | clear -A HS E9; ulia].
    - apply (XB_not_T bt st Lc FF W z HX). clear -A Hc. unfold T_PC, PC_SZ, PG in *. lia.
    - destruct (XB_zone bt st Lc FF W z HX) as [[HI _] | [_ (a & (CVa & _) & Ha)]]; [clear -A HI E1 E2 E3 E4 I2 B3; ulia|].
      assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
      destruct (carved_range bt st Lc FF W BATCHCLASS a HC24 CVa) as (D1 & D2 & _). change (csize BATCHCLASS) with 8192 in D2. unfold BATCHSZ in Ha.
      pose proof (region_facts bt st Lc FF W BATCHCLASS HC24) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      pose proof W as ((WR1 & _) & _). destruct (WR1 BATCHCLASS HC24) as (R1' & _ & R3' & _). unfold KREGION_EXHAUST, KUSERMAP in R3'.
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c BATCHCLASS) as [LT|[EQ|GT]].
      * assert (c * 2 ^ 32 + 2 ^ 32 <= BATCHCLASS * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H A Ha D1 D2 E6 Hfa Hm. lia.
      * subst c. clear -A Ha D1 D2 F2 F3 Hm. lia.
      * assert (BATCHCLASS * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (BATCHCLASS * 2 ^ 32 + 2 ^ 32) with ((BATCHCLASS + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H A Ha D1 D2 F2 F3 R1' R3' Hm. lia.
    - apply (XB_not_T bt st Lc FF W z HX). clear -A. unfold PG in *. lia.
    - pose proof (XB_below_ceil bt st Lc FF W z HX). lia.
  Qed.
End DT.
