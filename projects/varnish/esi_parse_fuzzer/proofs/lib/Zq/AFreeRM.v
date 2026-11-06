(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys ATransp ABudget ACover ASecB2 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf ATranspR AFreeRS AFreeRT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize in *.

(* [comment removed for export] *)
Definition kLimboMax : Z := 2^29 + 2^21.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RoomR.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variable A : AState.
  Hypothesis W : WFR A.
  Hypothesis X : wf_extra LPA pa_site_pcs (a_pl A).
  Hypothesis QLB : q_bytes (a_qlimbo A) <= kLimboMax.
  Local Notation ch := (sr_chunks (a_sec A)).
  Local Notation qg := (a_qglobal A).
  Local Notation lb := (a_qlimbo A).

  Lemma wfr_sec_sums :
    sec_n_sum ch <= LIVE_MAX + kQuarantineMaxSize + kLimboMax /\
    Z.of_nat (length ch) <= NLIVE_MAX + 12516.
  Proof.
    (first [ pose proof ((wrS A W)) as dR_1; dand5 dR_1 as SND SLEN SRES SIN SCOV | destruct (wrS A W) as (SND & SLEN & SRES & SIN & SCOV) ]).
    (first [ pose proof ((wrV A W)) as dR_2; dand3 dR_2 as LV1 LV2 LV3 | destruct (wrV A W) as (LV1 & LV2 & LV3) ]).
    (first [ pose proof ((wrQ A W)) as dR_3; dand8 dR_3 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct (wrQ A W) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    (first [ pose proof ((wrL A W)) as dR_4; dand4 dR_4 as L1 L2 L3 L4 | destruct (wrL A W) as (L1 & L2 & L3 & L4) ]).
    (first [ pose proof ((wrB A W)) as dR_5; dand5 dR_5 as B1 B2 B3 B4 B5 | destruct (wrB A W) as (B1 & B2 & B3 & B4 & B5) ]).
    set (E := q_entries (qg ++ lb)).
    assert (EN : forall e, In e E -> 0 <= qe_n e /\ (forall mb n0, qe_chunk e = ChS (CS mb n0) -> n0 = qe_n e /\ 64512 < qe_n e)).
    { intros e He. subst E.
      assert (WE : wf_qentry_ (a_reg A) (a_sec A) e).
      { unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb].
        - (first [ pose proof ((proj1 (Forall_forall _ _) Q2 b Hb)) as dR_6; dand3 dR_6 as _ _ WB | pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as (_ & _ & WB) ]). exact (proj1 (Forall_forall _ _) WB e Heb).
        - (first [ pose proof ((proj1 (Forall_forall _ _) L1 b Hb)) as dR_7; dand3 dR_7 as _ _ WB | pose proof (proj1 (Forall_forall _ _) L1 b Hb) as (_ & _ & WB) ]). exact (proj1 (Forall_forall _ _) WB e Heb). }
      destruct WE as [R WE]. split; [lia|]. intros mb n0 Hc. rewrite Hc in WE. unfold kMaxPrimaryUser in WE. lia. }
    destruct (sec_sum_bound ch (a_livemap A) E) as [S1 S2].
    - exact (NoDup_of_map cs_map ch SND).
    - intros u li Hu. pose proof (LV1 u li Hu) as (X1 & _). lia.
    - exact EN.
    - intros s Hs. pose proof (SCOV s Hs) as C. unfold quarantined_chunks_ in C. cbn [app] in C. exact C.
    - intros s Hs. pose proof (SIN s Hs) as (X1 & _). unfold kMaxPrimaryUser in X1. lia.
    - assert (QS : qsum E <= kQuarantineMaxSize + kLimboMax).
      { subst E. rewrite q_entries_app, qsum_app.
        pose proof (qsum_le_q_bytes qg ltac:(intros e He; apply (proj1 (EN e ltac:(rewrite q_entries_app; apply in_app_iff; left; exact He))))).
        pose proof (qsum_le_q_bytes lb ltac:(intros e He; apply (proj1 (EN e ltac:(rewrite q_entries_app; apply in_app_iff; right; exact He))))).
        lia. }
      unfold as_nlive_ in B3. rewrite NLIVE_MAX_eq in *. rewrite LIVE_MAX_eq in *. unfold kQuarantineCacheSize, kQuarantineMaxSize, kLimboMax in *.
      split; [lia|]. nia.
  Qed.

  Lemma wfr_sec_eager : sec_eager_ ch <= 2^32 + 2^30 /\ Z.of_nat (length ch) <= 12580.
  Proof.
    pose proof wfr_sec_sums as [S1 S2]. (first [ pose proof ((wrS A W)) as dR_8; dand5 dR_8 as _ _ _ SIN _ | destruct (wrS A W) as (_ & _ & _ & SIN & _) ]).
    pose proof (sec_eager_le ch ltac:(intros s Hs; pose proof (SIN s Hs) as (X1 & _); unfold kMaxPrimaryUser, REQ_MAX in X1; lia)) as SE.
    rewrite NLIVE_MAX_eq, LIVE_MAX_eq in *. unfold kQuarantineCacheSize, kQuarantineMaxSize, kLimboMax in *. split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wfr_class_nonneg : forall c, 1 <= c <= 31 -> 0 <= rg_mapped_user (a_reg A c) /\ 0 <= rg_mapped_fa (a_reg A c).
  Proof.
    intros c Hc. (first [ pose proof ((wrR A W)) as dR_9; dand3 dR_9 as R1 R2 _ | destruct (wrR A W) as (R1 & R2 & _) ]).
    destruct (Z.eq_dec c 31) as [->|NE].
    - rewrite (R2 31) by lia. cbn. lia.
    - destruct (R1 c ltac:(lia)) as (Q1 & _ & _ & _ & Q5 & _). lia.
  Qed.
  Lemma wfr_classes_eager : 0 <= classes_eager_ (a_reg A) 31 /\ 8 * classes_eager_ (a_reg A) 31 <= 9 * PRIMCRED0 + 2674149888.
  Proof.
    (first [ pose proof ((wrR A W)) as dR_9; dand3 dR_9 as R1 R2 _ | destruct (wrR A W) as (R1 & R2 & _) ]).
    (first [ pose proof ((wrN A W)) as dR_8; dand3 dR_8 as N0 NS _ | destruct (wrN A W) as (N0 & NS & _) ]).
    pose proof (classes_eager_le (a_reg A) (a_paid A) 30 ltac:(lia) ltac:(intros c Hc; apply R1; lia)) as [P1 P2].
    rewrite csize_sum_30, slack_sum_30 in P2. unfold kQuarantineMaxSize, kQuarantineCacheSize in P2.
    rewrite (classes_eager_S (a_reg A) 30). rewrite (R2 (Z.of_nat 31)) by (clear; lia). cbn [rg_mapped_user rg_mapped_fa region_zero]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wfr_alregions_nonneg : forall b s, In (b, s) (alregions AL_pboth A) -> 0 <= s.
  Proof.
    intros b s Hin. unfold alregions, alregions_ in Hin.
    pose proof (wrP A W) as WP.
    assert (SP : 0 <= p_stk_span (a_pl A) <= 0x240000) by (apply wf_place_cheap in WP; lia).
    apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (lfixed_regions_weight _ SP) b s Hin)|].
    apply in_app_iff in Hin as [Hin|Hin].
    - exact (proj1 (lclasses_regions_weight (p_sb (a_pl A)) (a_reg A) 31 ltac:(intros c Hc; apply wfr_class_nonneg; lia)) b s Hin).
    - (first [ pose proof ((wrS A W)) as dR_11; dand5 dR_11 as _ _ _ SIN _ | destruct (wrS A W) as (_ & _ & _ & SIN & _) ]).
      exact (proj1 (lsec_regions_weight (sr_chunks (a_sec A)) ltac:(intros s' Hs'; pose proof (SIN s' Hs') as (Y & _); unfold kMaxPrimaryUser, REQ_MAX in Y; lia)) b s Hin).
  Qed.
  Lemma wfr_lhull_bytes : 8 * hull_bytes (pa_lhull A) <=
    8 * (2^29 + (2^29 + 2^28 + 2^27) + 8192 * (400 * 1000) + (2^28 + 2^26)) + classes_eager_ (a_reg A) 31 + 131328 * 31.   (* [comment removed for export] *)
  Proof.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. rewrite !hull_bytes_app.
    pose proof (wrP A W) as WP.
    assert (SP : 0 <= p_stk_span (a_pl A) <= 0x240000) by (apply wf_place_cheap in WP; lia). clear WP.
    assert (HX : hull_bytes (p_extra (a_pl A)) <= 2^28 + 2^26) by (destruct X as (_ & _ & _ & _ & _ & HX); apply HX || exact (proj1 HX)).
    assert (HD : hull_bytes (a_deadsh A) <= 8192 * (400 * 1000)).
    { (first [ pose proof ((wrE A W)) as dR_12; dand4 dR_12 as D1 _ _ D4 | destruct (wrE A W) as (D1 & _ & _ & D4) ]). unfold kDeadShadowBytes in D4. rewrite SECCRED0_eq in D1, D4.
      pose proof (Nat2Z.is_nonneg (length (sr_chunks (a_sec A)))). nia. }
    pose proof (hull_bytes_of_regions (alregions_ AL_pboth (a_pl A) (a_reg A) (a_sec A)) wfr_alregions_nonneg) as HR.
    unfold alregions_ in HR. rewrite !regions_weight_app in HR.
    pose proof (proj2 (lfixed_regions_weight _ SP)) as F.
    pose proof (proj2 (lclasses_regions_weight (p_sb (a_pl A)) (a_reg A) 31 ltac:(intros c Hc; apply wfr_class_nonneg; lia))) as C.
    (first [ pose proof ((wrS A W)) as dR_13; dand5 dR_13 as _ _ _ SIN _ | destruct (wrS A W) as (_ & _ & _ & SIN & _) ]).
    pose proof (proj2 (lsec_regions_weight (sr_chunks (a_sec A)) ltac:(intros s' Hs'; pose proof (SIN s' Hs') as (Y & _); unfold kMaxPrimaryUser, REQ_MAX in Y; lia))) as S.
    pose proof wfr_sec_eager as [E1 E2].
    replace (Z.of_nat 31) with 31 in C by reflexivity.
    pose proof (Z.div_mod (sec_eager_ (sr_chunks (a_sec A))) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sec_eager_ (sr_chunks (a_sec A))) 8 ltac:(lia)).
    lia.
  Qed.

  Lemma wfr_aeager : 0 <= aeager_of A /\ aeager_of A <= 2^25 + classes_eager_ (a_reg A) 31 + 2^17 + (2^32 + 2^30).   (* [comment removed for export] *)
  Proof.
    unfold aeager_of, aeager_of_.
    pose proof (wrP A W) as WP.
    assert (E0 : 0 <= p_eager0 (a_pl A) <= 2^25) by (apply wf_place_cheap in WP; lia). clear WP.
    pose proof wfr_classes_eager as [C _].
    (first [ pose proof ((wrS A W)) as dR_14; dand5 dR_14 as _ SLEN SRES SIN _ | destruct (wrS A W) as (_ & SLEN & SRES & SIN & _) ]).
    pose proof wfr_sec_eager as [E1 E2].
    assert (0 <= sec_eager_ (sr_chunks (a_sec A))).
    { generalize SIN. generalize (sr_chunks (a_sec A)) as ch0. clear. induction ch0 as [|c ch0 IH]; intros H; [cbn; lia|].
      change (sec_eager_ (c :: ch0)) with (map_size (cs_n c) + sec_eager_ ch0).
      pose proof (H c (or_introl eq_refl)) as (Y & _). unfold kMaxPrimaryUser in Y. pose proof (map_size_ge (cs_n c) ltac:(lia)).
      specialize (IH ltac:(intros; apply H; right; assumption)). lia. }
    unfold kChunksBlockCount in SRES. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem wfr_budget_room_min : aeager_of A + hull_bytes (pa_lhull A) + kBudgetRoom <= TLIM_MIN.   (* [comment removed for export] *)
  Proof. pose proof wfr_lhull_bytes. pose proof wfr_aeager. pose proof wfr_classes_eager. unfold kBudgetRoom. rewrite TLIM_MIN_eq. rewrite PRIMCRED0_eq in *. lia. Qed.
  Theorem wfr_budget_room : aeager_of A + hull_bytes (pa_lhull A) + kBudgetRoom <= p_tlim (a_pl A).
  Proof. pose proof wfr_budget_room_min. assert (TLIM_MIN <= p_tlim (a_pl A)) by (destruct X as (_ & _ & _ & _ & _ & _ & _ & T); exact T). lia. Qed.
End RoomR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CommitR.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (md0 md3 : Model) (beg len : Z).
  Hypothesis W : WFR A.
  Hypothesis LED3 : aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md3.   (* [comment removed for export] *)
  Hypothesis HH3 : m_halted md3 = None.
  Hypothesis HI3 : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md3.   (* [comment removed for export] *)
  Hypothesis COV3 : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md3).
  Hypothesis TOP3 : alloc_top (m_vmmaps md3) = alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis RANGE : a_sb A <= beg /\ beg + len <= a_sb A + kSpaceSize + 4096 /\ beg mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len.
  Local Notation begw := (wz beg).
  Local Notation lenw := (wz len).
  Local Notation md4 := (commit_model (wz 50) begw lenw false md3).
  Let W0 : WFT A. Proof. exact (WFT_of_WFR A W). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let LIM3 : vm_limit (m_vmmaps md3) = p_tlim (a_pl A).   (* [comment removed for export] *) Proof. destruct LED3 as (_ & _ & _ & _ & L5 & _). exact L5. Qed.
  Let SBF : a_sb A = space_beg_of (a_b6 A) /\ a_sb A mod 0x10000 = 0 /\ kHighMemBeg <= a_b6 A /\ a_b6 A < a_sb A <= a_b6 A + 0x10000 /\ a_sb A + kSpaceSize + 4096 <= alloc_ceiling.
  Proof. exact (sb_factsT A W0). Qed.
  Let BEGW : bv_unsigned begw = beg. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let LENW : bv_unsigned lenw = len. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.

  Lemma cr_gate : fixed_gate md3 begw len.
  Proof. unfold fixed_gate. rewrite TOP3, BEGW. pose proof SBF. pose proof RANGE. unfold page_size. kung_all. lia. Qed.

  Lemma cr_contained : region_free (vm_reserved (m_vmmaps md3)) begw lenw = true /\ map_contains (vm_maps (m_vmmaps md3)) begw lenw = true.
  Proof.
    pose proof SBF as (S1 & S2 & S3 & S4 & S5). pose proof RANGE as (R1 & R2 & R3 & R4 & R5).
    destruct LED3 as (L1 & _).
    split.
    - rewrite (proj2 (proj2 COV3)). apply pa_reserved_free; kung_all; lia.
    - unfold map_contains. apply existsb_exists. exists (wz (a_b6 A), wz kSpaceReserve). split.
      + apply L1. unfold big_maps_. cbn. left. reflexivity.
      + cbn [fst snd]. rewrite BEGW, LENW, !unsigned_lit by (kung_all; lia). apply andb_true_iff. split; apply Z.leb_le; kung_all; lia.
  Qed.

  Lemma cr_budget : pa_eager A + len + hull_bytes (pa_lhull A) <= p_tlim (a_pl A) -> mmap_fixed_rw_budget_ok (wz 50) md3 begw lenw = true.
  Proof.
    intros BR. apply (gate_fixed_rw_budget_ok (pa_hull A) (pa_lhull A) (pa_eager A) (wz 50) begw lenw md3 HI3).
    - pose proof cr_gate as (G1 & _). rewrite LENW. exact G1.
    - exact (proj2 cr_contained).
    - right. rewrite LENW, LIM3. clear - BR. lia.
  Qed.
  Lemma cr_minv : pa_eager A + len + hull_bytes (pa_lhull A) <= p_tlim (a_pl A) -> MInv (pa_hull A) (pa_lhull A) (pa_eager A + len) md4.
  Proof.
    intros BR. rewrite <- LENW at 1. apply (MInv_commit_rw (pa_hull A) (pa_lhull A) (pa_eager A) (wz 50) begw lenw md3 HI3 mmap_noreserve_b_50).
    - pose proof cr_gate as (G1 & _). rewrite LENW. exact G1.
    - exact (proj2 cr_contained).
    - rewrite LENW, LIM3. clear - BR. lia.
  Qed.
  Lemma cr_vm5 : vm5_same (m_vmmaps md3) (m_vmmaps md4).
  Proof. exact (vm5_same_commit _ _ _ md3). Qed.
  Lemma cr_halted : m_halted md4 = None.
  Proof. rewrite commit_model_halted. exact HH3. Qed.
  Lemma cr_ceil : alloc_top (m_vmmaps md4) = alloc_ceiling.
  Proof. (first [ pose proof (cr_vm5) as dR_15; dand5 dR_15 as _ _ _ E _ | pose proof cr_vm5 as (_ & _ & _ & E & _) ]). unfold alloc_top in *. rewrite E. exact TOP3. Qed.
  Lemma cr_limit : vm_limit (m_vmmaps md4) = p_tlim (a_pl A).
  Proof. (first [ pose proof (cr_vm5) as dR_16; dand4 dR_16 as _ _ E _ | pose proof cr_vm5 as (_ & _ & E & _) ]). rewrite E. exact LIM3. Qed.

  (* [comment removed for export] *)
  Lemma cr_lzfree_new : lazy_free (m_vm_lazy md4) beg (beg + len).
  Proof. pose proof (MInv_commit_lazy_free (pa_hull A) (pa_lhull A) (pa_eager A) (wz 50) begw lenw false md3 HI3 mmap_noreserve_b_50) as X. rewrite BEGW, LENW in X. exact X. Qed.
  Lemma cr_lzfree_old : forall lo hi, lazy_free (m_vm_lazy md3) lo hi -> lazy_free (m_vm_lazy md4) lo hi.
  Proof. intros lo hi Z0. exact (lazy_free_commit (wz 50) begw lenw false md3 lo hi mmap_noreserve_b_50 (minv_lazy_nw HI3) Z0). Qed.
  (* [comment removed for export] *)
  Lemma cr_ledger : aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md4.
  Proof.
    destruct LED3 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & [L8 L9]). (first [ pose proof (cr_vm5) as dR_17; dand5 dR_17 as C1 C2 C3 C4 C5 | pose proof cr_vm5 as (C1 & C2 & C3 & C4 & C5) ]).
    pose proof SBF as (S1 & S2 & S3 & S4 & S5). pose proof RANGE as (R1 & R2 & R3 & R4 & R5).
    unfold aledger_. cbv zeta. rewrite C1, C2, C3.
    split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [| split]]]]]].
    - apply Forall_forall. intros sc Hsc. pose proof (proj1 (Forall_forall _ _) L6 sc Hsc) as EM.
      pose proof (bm_nth_fixed A) as (E0 & _).
      assert (APT : cs_map sc + map_size (cs_n sc) <= a_b6 A \/ a_b6 A + kSpaceReserve <= cs_map sc).
      { apply In_nth_error' in Hsc as [i Hi]. pose proof (bm_sepT A (15 + i) 0 _ _ _ _ W0 (bm_nth_sec A i sc Hi) E0 ltac:(lia)). unfold a_b6 in *. lia. }
      assert (SCB : 0 <= cs_map sc /\ 0 < map_size (cs_n sc) /\ cs_map sc + map_size (cs_n sc) <= 2^47).
      { (first [ pose proof ((sec_chunk_boundsT A sc W0 Hsc)) as dR_18; dand5 dR_18 as B1 _ B3 B4 _ | pose proof (sec_chunk_boundsT A sc W0 Hsc) as (B1 & _ & B3 & B4 & _) ]). apply app_facts in B3.
        pose proof (map_size_ge (cs_n sc)). unfold kMaxPrimaryUser in *. lia. }
      apply eager_map_commit; [exact (minv_noacc_nw HI3)| exact (minv_lazy_nw HI3)| | | exact EM].
      + unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite BEGW, LENW. clear - RANGE SBF CE. kung_all. lia.
      + rewrite BEGW, LENW, !unsigned_lit by lia. clear - APT SCB RANGE SBF. kung_all. lia.
    - apply cuts_covered_commit_contained; [exact (minv_noacc_nw HI3)| exact (minv_lazy_nw HI3)| | exact (proj2 cr_contained)| exact L7].
      unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite BEGW, LENW. clear - RANGE SBF CE. kung_all. lia.
    - (* [comment removed for export] *)
      destruct L8 as [N1 N2]. split; [split; [exact (noacc_free_commit_rw _ _ _ _ _ _ (minv_noacc_nw HI3) N1)| exact (noacc_free_commit_rw _ _ _ _ _ _ (minv_noacc_nw HI3) N2)]|].
      (* [comment removed for export] *)
      destruct L9 as (Z1 & Z2 & Z3). split; [exact (cr_lzfree_old _ _ Z1)|]. split; [exact (cr_lzfree_old _ _ Z2)|].
      intros c Hc. destruct (Z3 c Hc) as [ZU ZF]. split; apply cr_lzfree_old; assumption.
  Qed.
  Lemma cr_cover : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md4).
  Proof.
    (first [ pose proof (cr_vm5) as dR_19; dand3 dR_19 as C1 C2 _ | pose proof cr_vm5 as (C1 & C2 & _) ]). apply (acover_vmmaps _ _ _ (m_vmmaps md3)); [exact C1| exact C2| exact COV3].
  Qed.
  Lemma cr_amd : amd_frame md0 md3 -> amd_frame md0 md4.
  Proof.
    intros F3. (first [ pose proof (cr_vm5) as dR_20; dand5 dR_20 as C1 C2 C3 C4 C5 | pose proof cr_vm5 as (C1 & C2 & C3 & C4 & C5) ]). pose proof cr_halted as HH4.
    (first [ pose proof ((commit_model_nonvm (wz 50) begw lenw false md3)) as dR_21; dand6 dR_21 as B1 B2 B3 B4 B5 B6 | pose proof (commit_model_nonvm (wz 50) begw lenw false md3) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    unfold amd_frame in *. rewrite C2, C3, C4, C5, B1, B2, B3, B4, B5, B6.
    decompose [and] F3. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cr_lzfree : forall md5, same_but_materialized md4 md5 -> lazy_free (m_vm_lazy md5) beg (beg + len).
  Proof. intros md5 SB5. exact (lazy_free_sbm _ _ _ _ SB5 cr_lzfree_new). Qed.
  Lemma cr_model : amd_frame md0 md3 -> forall md5, same_but_materialized md4 md5 ->
    aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md5 /\ acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md5) /\
    alloc_top (m_vmmaps md5) = alloc_ceiling /\ amd_frame md0 md5 /\ m_halted md5 = None.
  Proof.
    intros F3 md5 SB5. pose proof (same_but_materialized_vmmaps _ _ SB5) as V.
    split; [exact (aledger_sbm _ _ _ _ _ _ SB5 cr_ledger)|].
    split; [rewrite V; exact cr_cover|].
    split; [rewrite V; exact cr_ceil|].
    split.
    - pose proof (cr_amd F3) as F. (first [ pose proof ((same_but_materialized_frame _ _ SB5)) as dR_22; dand18 dR_22 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | pose proof (same_but_materialized_frame _ _ SB5) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      unfold amd_frame in *. rewrite X1, X2, X4, X5, X6, X7, X8, X17.
      decompose [and] F. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
    - rewrite (same_but_materialized_halted _ _ SB5). exact cr_halted.
  Qed.
End CommitR.
