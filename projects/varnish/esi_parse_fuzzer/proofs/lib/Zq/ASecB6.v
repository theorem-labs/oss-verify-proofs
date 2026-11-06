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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys ATransp ABudget ACover ASecB2 ASecB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Section Model.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md md1 : Model) (n : Z) (mbw : word) (key : list Z) (nres' : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis SB1 : same_but_materialized md md1.
  Hypothesis HI1 : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.   (* [comment removed for export] *)
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Local Notation mb := (bv_unsigned mbw).
  Local Notation ms := (map_size n).
  Local Notation h := (m_vmmaps md).
  Local Notation pa := (p_pa (a_pl A)).
  Local Notation sec' := (SR (sr_chunks (a_sec A) ++ [CS mb n]) nres').
  Local Notation A' := (secA A mb n key nres').
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let VM1 : m_vmmaps md1 = h. Proof. exact (same_but_materialized_vmmaps _ _ SB1). Qed.
  Let LIMv : vm_limit h = p_tlim (a_pl A).   (* [comment removed for export] *) Proof. (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_1; dand6 dR_1 as _ _ _ _ L5 _ | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _) ]). exact L5. Qed.
  Let TOP : alloc_top h = alloc_ceiling. Proof. exact (ai_ceil _ _ _ _ _ _ _ AI). Qed.
  Let MSP : 0 < ms < 2^40.
  Proof. pose proof NR as X. unfold kMaxPrimaryUser in X. pose proof (map_size_ge n ltac:(lia)). pose proof (map_size_le n ltac:(lia)). lia. Qed.
  Let MS31 : ms < 2^31 /\ ms <= 2^30 + 12296.   (* [comment removed for export] *)
  Proof. pose proof NR as X. unfold kMaxPrimaryUser in X. pose proof (map_size_le n ltac:(lia)). lia. Qed.
  Let MSA : ms mod 4096 = 0. Proof. apply map_size_page. Qed.
  Let MSW : bv_unsigned (wz ms) = ms. Proof. apply unsigned_lit. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sec_grant_exists : exists g : word, grant_okf (wz 34) (wz 0) md1 g ms = true.
  Proof.
    (first [ pose proof ((grant_room A h ms W0 (ai_cover _ _ _ _ _ _ _ AI) (minv_nooverlap (ai_minv _ _ _ _ _ _ _ AI)) TOP
                ltac:(lia) MSA ltac:(pose proof NR as X; unfold kMaxPrimaryUser in X; pose proof (map_size_le n ltac:(lia)); lia))) as dR_2; dex1 dR_2 as g; dand5 dR_2 as GA GP GH GT GF | pose proof ((grant_room A h ms W0 (ai_cover _ _ _ _ _ _ _ AI) (minv_nooverlap (ai_minv _ _ _ _ _ _ _ AI)) TOP
                ltac:(lia) MSA ltac:(pose proof NR as X; unfold kMaxPrimaryUser in X; pose proof (map_size_le n ltac:(lia)); lia))) as dR_2; dand6 dR_2 as g GA GP GH GT GF | destruct (grant_room A h ms W0 (ai_cover _ _ _ _ _ _ _ AI) (minv_nooverlap (ai_minv _ _ _ _ _ _ _ AI)) TOP
                ltac:(lia) MSA ltac:(pose proof NR as X; unfold kMaxPrimaryUser in X; pose proof (map_size_le n ltac:(lia)); lia))
      as (g & GA & GP & GH & GT & GF) ]).
    exists (wz g). rewrite grant_okf_plain. unfold grant_ok. rewrite VM1. rewrite !unsigned_lit by lia. unfold page_size.
    rewrite (proj2 (Z.eqb_eq _ _) GA). rewrite (proj2 (Z.ltb_lt _ _) GP). rewrite (proj2 (Z.leb_le _ _) GT). rewrite GF. cbn [andb].
    apply Z.leb_le. rewrite LIMv.
    pose proof (MInv_backing_used_le _ _ _ _ HI1). pose proof (pa_budget_room A m md AI). unfold kBudgetRoom in *.
    change (aeager_of A) with (pa_eager A) in *. change (alhull_of AL_pboth A) with (pa_lhull A) in *. clear - H H0 MS31. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Grant.
  Hypothesis GOK : grant_okf (wz 34) (wz 0) md1 mbw ms = true.
  Local Notation md2 := (grant_model (wz 34) mbw (wz ms) false md1).

  (* [comment removed for export] *)
  Lemma g_facts : mb mod 4096 = 0 /\ 0 < mb /\ mb + ms <= alloc_ceiling /\
                  region_free (vm_reserved h ++ vm_maps h) mbw (wz ms) = true.
  Proof.
    rewrite grant_okf_plain in GOK. unfold grant_ok in GOK. rewrite !andb_true_iff in GOK. destruct GOK as [[[[G1 G2] G3] G4] G5].
    apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. rewrite VM1 in G3, G4. rewrite TOP in G3. unfold page_size in G1.
    exact (conj G1 (conj G2 (conj G3 G4))).
  Qed.
  Let MBA : mb mod 4096 = 0. Proof. exact (proj1 g_facts). Qed.
  Let MB0 : 0 < mb. Proof. exact (proj1 (proj2 g_facts)). Qed.
  Let MBC : mb + ms <= alloc_ceiling. Proof. exact (proj1 (proj2 (proj2 g_facts))). Qed.
  Let RF : region_free (vm_reserved h ++ vm_maps h) mbw (wz ms) = true. Proof. exact (proj2 (proj2 (proj2 g_facts))). Qed.
  Let NW : entry_nowrap (mbw, wz ms). Proof. unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite MSW. lia. Qed.

  Lemma g_vmmaps : vm_maps (m_vmmaps md2) = (mbw, wz ms) :: vm_maps h /\ vm_reserved (m_vmmaps md2) = vm_reserved h /\
                   vm_limit (m_vmmaps md2) = vm_limit h /\ vm_init_sp (m_vmmaps md2) = vm_init_sp h /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base h.
  Proof. rewrite grant_model_vmmaps. rewrite <- VM1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
  Lemma g_halted : m_halted md2 = None.
  Proof. rewrite grant_model_halted. rewrite (same_but_materialized_halted _ _ SB1). exact (ai_halted _ _ _ _ _ _ _ AI). Qed.
  Lemma g_ceil : alloc_top (m_vmmaps md2) = alloc_ceiling.
  Proof. (first [ pose proof (g_vmmaps) as dR_3; dand5 dR_3 as _ _ _ E _ | pose proof g_vmmaps as (_ & _ & _ & E & _) ]). unfold alloc_top in *. rewrite E. exact TOP. Qed.
  Lemma g_amd : amd_frame md md2.
  Proof.
    (first [ pose proof ((same_but_materialized_frame _ _ SB1)) as dR_4; dand9 dR_4 as X1 X2 X3 X4 X5 X6 X7 X8 Xr | pose proof (same_but_materialized_frame _ _ SB1) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & Xr) ]).
    (first [ pose proof (g_vmmaps) as dR_5; dand5 dR_5 as V1 V2 V3 V4 V5 | pose proof g_vmmaps as (V1 & V2 & V3 & V4 & V5) ]). pose proof g_halted as HH2. unfold amd_frame. rewrite V2, V3, V4, V5.
    (first [ pose proof ((with_mmap_backing_nonvm (wz 34) mbw (wz ms) (with_vmmaps (grant_vmmaps (m_vmmaps md1) mbw (wz ms) false) md1))) as dR_6; dand6 dR_6 as B1 B2 B3 B4 B5 B6 | pose proof (with_mmap_backing_nonvm (wz 34) mbw (wz ms) (with_vmmaps (grant_vmmaps (m_vmmaps md1) mbw (wz ms) false) md1)) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    (first [ pose proof ((with_vmmaps_nonvm (grant_vmmaps (m_vmmaps md1) mbw (wz ms) false) md1)) as dR_7; dand6 dR_7 as C1 C2 C3 C4 C5 C6 | pose proof (with_vmmaps_nonvm (grant_vmmaps (m_vmmaps md1) mbw (wz ms) false) md1) as (C1 & C2 & C3 & C4 & C5 & C6) ]).
    unfold grant_model in *. rewrite B1, B2, B3, B4, B5, B6, C1, C2, C3, C4, C5, C6.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [congruence | reflexivity | exact HH2].
  Qed.

  (* [comment removed for export] *)
  Lemma g_lazy : m_vm_lazy md2 = m_vm_lazy md.
  Proof. rewrite (grant_model_lazy_plain _ _ _ _ _ mmap_noreserve_b_plain). rewrite SB1. apply m_vm_lazy_wvb. Qed.
  (* [comment removed for export] *)
  Lemma sec_ledger_grant : aledger_ AL_pboth (a_pl A) (a_reg A) sec' md2.
  Proof.
    (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_8; dand9 dR_8 as L1 L2 L3 L4 L5 L6 L7 L8 L9 | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9) ]). (first [ pose proof (g_vmmaps) as dR_9; dand5 dR_9 as V1 V2 V3 V4 V5 | pose proof g_vmmaps as (V1 & V2 & V3 & V4 & V5) ]).
    unfold aledger_. cbv zeta. rewrite V1, V2, V3. cbn [sr_chunks].
    split; [| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [| split]]]]]].
    - intros b s Hin. unfold big_maps_ in Hin. cbn [sr_chunks] in Hin. rewrite map_app in Hin. cbn [map cs_map cs_n] in Hin.
      rewrite app_assoc in Hin. apply in_app_iff in Hin as [Hin|[E|[]]].
      + right. exact (L1 b s Hin).
      + injection E as <- <-. left. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - apply Forall_app. split.
      + apply Forall_forall. intros sc Hsc. pose proof (proj1 (Forall_forall _ _) L6 sc Hsc) as EM.
        apply (eager_map_sbm _ _ md md1 SB1) in EM.
        apply (eager_map_grant _ _ (wz 34) mbw (wz ms) false md1 NW); [| exact EM].
        rewrite MSW, unsigned_lit by ((first [ pose proof ((sec_chunk_bounds A sc W0 Hsc)) as dR_10; dand5 dR_10 as B1 _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W0 Hsc) as (B1 & _ & B3 & B4 & _) ]); apply app_facts in B3; lia).
        apply In_nth_error' in Hsc as [i Hi]. pose proof (gf_APART A m md mbw ms AI MB0 MSP RF _ _ _ (bm_nth_sec A i sc Hi)) as D.
        rewrite unsigned_lit by ((first [ pose proof ((sec_chunk_bounds A sc W0 (nth_error_In _ _ Hi))) as dR_11; dand5 dR_11 as B1 _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W0 (nth_error_In _ _ Hi)) as (B1 & _ & B3 & B4 & _) ]); apply app_facts in B3;
                                 pose proof (map_size_ge (cs_n sc)); pose proof (map_size_le (cs_n sc)); unfold kMaxPrimaryUser in *; lia).
        clear - D. lia.
      + constructor; [| constructor]. cbn [cs_map cs_n]. rewrite Z_to_bv_bv_unsigned.
        apply eager_map_new_covered; [exact (cuts_covered_sbm md md1 SB1 L7)| apply mmap_noreserve_b_plain| rewrite VM1; exact RF| rewrite MSW; lia].
    - apply cuts_covered_grant; [exact NW| exact (cuts_covered_sbm md md1 SB1 L7)].
    - (* [comment removed for export] *)
      destruct L8 as [N1 N2]. split; [split; [exact (noacc_free_grant_rw _ _ _ _ _ _ (noacc_free_sbm _ _ _ _ SB1 N1))| exact (noacc_free_grant_rw _ _ _ _ _ _ (noacc_free_sbm _ _ _ _ SB1 N2))]|].
      (* [comment removed for export] *) exact (alzfree_lazy_eq _ _ _ md md2 g_lazy L9).
  Qed.

  (* [comment removed for export] *)
  Lemma sec_cover_grant : acover_ LPA (a_pl A) sec' (m_vmmaps md2).
  Proof.
    (first [ pose proof ((ai_cover _ _ _ _ _ _ _ AI)) as dR_12; dand3 dR_12 as (fog & FL & FS & COV & F1 & F2) GAP RSV | pose proof (ai_cover _ _ _ _ _ _ _ AI) as ((fog & FL & FS & COV & F1 & F2) & GAP & RSV) ]). (first [ pose proof (g_vmmaps) as dR_13; dand5 dR_13 as V1 V2 V3 V4 V5 | pose proof g_vmmaps as (V1 & V2 & V3 & V4 & V5) ]).
    unfold acover_. rewrite V1, V2. split; [| split; [right; exact GAP| exact RSV]].
    exists fog. split; [exact FL|]. split; [exact FS|]. split; [| split; [intros bs Hbs; right; exact (F1 bs Hbs)| exact F2]].
    intros e [<-|He]; cbv zeta.
    - left. cbn [fst snd]. rewrite MSW. unfold big_maps_. cbn [sr_chunks]. rewrite map_app. cbn [map cs_map cs_n].
      apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
    - destruct (COV e He) as [X|[X|X]]; [left| right; left; exact X| right; right; exact X].
      unfold big_maps_ in *. cbn [sr_chunks]. rewrite map_app. rewrite app_assoc. apply in_app_iff. left. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_minv_grant0 : MInv (pa_hull A) (pa_lhull A) (pa_eager A + ms) md2.   (* [comment removed for export] *)
  Proof.
    pose proof (MInv_grant_rw (pa_hull A) (pa_lhull A) (pa_eager A) (wz 34) mbw (wz ms) md1 HI1 mmap_noreserve_b_plain) as X. rewrite MSW in X. apply X.
    - rewrite VM1, TOP. exact MBC.
    - rewrite VM1. exact RF.
    - rewrite VM1, LIMv. pose proof (pa_budget_room A m md AI). unfold kBudgetRoom in *.
      change (aeager_of A) with (pa_eager A) in *. change (alhull_of AL_pboth A) with (pa_lhull A) in *. clear - H MS31. lia.
  Qed.
  Hypothesis WF' : WF A'.
  Hypothesis NRES : sr_reserved (a_sec A) <= nres' <= kChunksBlockCount.
  (* [comment removed for export] *)
  Lemma sec_cover : forall lo hi, In (lo, hi) (pa_hull A') ->
    iv_sub (pa_hull A) lo hi \/ iv_sub (pa_lhull A') lo hi \/ lazy_free (m_vm_lazy md2) lo hi.
  Proof. intros lo hi Hin. right. exact (ahull_cover A' md2 WF' sec_ledger_grant lo hi Hin). Qed.
  Lemma sec_minv_grant : MInv (pa_hull A') (pa_lhull A') (pa_eager A') md2.
  Proof.
    apply (MInv_hull_mono (pa_hull A) (pa_lhull A) (pa_hull A') (pa_lhull A') (pa_eager A + ms) (pa_eager A') md2 sec_minv_grant0).
    - apply sec_lhull_le.
    - apply sec_cover.
    - rewrite (sec_eager A mb n key nres'). lia.
    - (first [ pose proof (g_vmmaps) as dR_14; dand4 dR_14 as _ _ V3 _ | pose proof g_vmmaps as (_ & _ & V3 & _) ]). rewrite V3, LIMv.
      pose proof (wf_budget_room A' WF' (ai_extra _ _ _ _ _ _ _ AI)) as BR. unfold kBudgetRoom in BR. change (p_tlim (a_pl A')) with (p_tlim (a_pl A)) in BR.
      change (aeager_of A') with (pa_eager A') in BR. change (alhull_of AL_pboth A') with (pa_lhull A') in BR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sec_minv_grant1 : MInv (pa_hull A') (pa_lhull A') (pa_eager A + ms) md2.
  Proof.
    apply (MInv_hull_mono (pa_hull A) (pa_lhull A) (pa_hull A') (pa_lhull A') (pa_eager A + ms) (pa_eager A + ms) md2 sec_minv_grant0).
    - apply sec_lhull_le.
    - apply sec_cover.
    - lia.
    - (first [ pose proof (g_vmmaps) as dR_15; dand4 dR_15 as _ _ V3 _ | pose proof g_vmmaps as (_ & _ & V3 & _) ]). rewrite V3, LIMv.
      pose proof (wf_budget_room A' WF' (ai_extra _ _ _ _ _ _ _ AI)) as BR. unfold kBudgetRoom in BR. change (p_tlim (a_pl A')) with (p_tlim (a_pl A)) in BR.
      change (aeager_of A') with (pa_eager A') in BR. change (alhull_of AL_pboth A') with (pa_lhull A') in BR.
      rewrite (sec_eager A mb n key nres') in BR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sec_model_grant : forall md3, same_but_materialized md2 md3 ->
    aledger_ AL_pboth (a_pl A) (a_reg A) sec' md3 /\ acover_ LPA (a_pl A) sec' (m_vmmaps md3) /\ alloc_top (m_vmmaps md3) = alloc_ceiling /\ amd_frame md md3.
  Proof.
    intros md3 SB3. pose proof (same_but_materialized_vmmaps _ _ SB3) as V.
    split; [exact (aledger_sbm _ _ _ _ _ _ SB3 sec_ledger_grant)|]. split; [rewrite V; exact sec_cover_grant|]. split; [rewrite V; exact g_ceil|].
    pose proof g_amd as F. (first [ pose proof ((same_but_materialized_frame _ _ SB3)) as dR_16; dand18 dR_16 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | pose proof (same_but_materialized_frame _ _ SB3) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
    unfold amd_frame in *. rewrite X1, X2, X4, X5, X6, X7, X8, X17.
    decompose [and] F. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Commit.
  Variables (md3 : Model) (E3 : Z).
  Hypothesis SB3 : same_but_materialized md2 md3.
  Hypothesis HI3 : MInv (pa_hull A') (pa_lhull A') E3 md3.   (* [comment removed for export] *)
  Local Notation paw := (wz pa).
  Local Notation blk := (wz (8 * kChunksBlockCount)).
  Local Notation md4 := (commit_model (wz 50) paw blk false md3).
  Let V3 : m_vmmaps md3 = m_vmmaps md2. Proof. exact (same_but_materialized_vmmaps _ _ SB3). Qed.
  Let PAF : 4096 <= pa /\ pa + kPtrArrayReserve <= alloc_ceiling /\ pa mod 4096 = 0.
  Proof.
    pose proof (place_facts A W0) as PF. cbv zeta in PF. (first [ dand13 PF as _ _ _ _ _ _ _ _ _ _ _ (PPA & PPB & AL) _ | destruct PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (PPA & PPB & AL) & _) ]).
    apply app_facts in PPA. exact (conj (proj1 PPA) (conj PPB AL)).
  Qed.
  Let PAW : bv_unsigned paw = pa. Proof. apply unsigned_lit. unfold kPtrArrayReserve in PAF. lia. Qed.
  Let BLW : bv_unsigned blk = 0x20000. Proof. apply unsigned_lit. unfold kChunksBlockCount. lia. Qed.

  Lemma c_gate : fixed_gate md3 paw (8 * kChunksBlockCount).
  Proof.
    unfold fixed_gate. rewrite V3, g_ceil, PAW. unfold page_size, kChunksBlockCount, kPtrArrayReserve in *. lia.
  Qed.
  Lemma c_contained : region_free (vm_reserved (m_vmmaps md3)) paw blk = true /\ map_contains (vm_maps (m_vmmaps md3)) paw blk = true.
  Proof.
    rewrite V3. (first [ pose proof (g_vmmaps) as dR_18; dand3 dR_18 as V1 V2 _ | pose proof g_vmmaps as (V1 & V2 & _) ]). rewrite V1, V2.
    destruct (ai_ledger _ _ _ _ _ _ _ AI) as (L1 & _).
    assert (PA1 : 0x60a000 <= pa).
    { pose proof (place_facts A W0) as PF. cbv zeta in PF. (first [ dand13 PF as _ _ _ _ _ _ _ _ _ _ _ (PPA & _) _ | destruct PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (PPA & _) & _) ]).
      apply app_facts in PPA. unfold kPtrArrayReserve in PPA. lia. }
    split.
    - change (8 * kChunksBlockCount) with 0x20000. apply (pa_cover_reserved_free A m md pa 0x20000 AI); unfold kPtrArrayReserve in *; lia.
    - unfold map_contains. apply existsb_exists. exists (wz pa, wz kPtrArrayReserve). split.
      + right. apply L1. unfold big_maps_. cbn. tauto.
      + cbn [fst snd]. rewrite PAW, BLW, !unsigned_lit by (unfold kPtrArrayReserve in *; lia). apply andb_true_iff. split; apply Z.leb_le; unfold kPtrArrayReserve; lia.
  Qed.
  Lemma c_vmmaps : vm_maps (m_vmmaps md4) = (mbw, wz ms) :: vm_maps h /\ vm_reserved (m_vmmaps md4) = vm_reserved h /\
                   vm_limit (m_vmmaps md4) = vm_limit h /\ vm_init_sp (m_vmmaps md4) = vm_init_sp h /\ vm_mmap_base (m_vmmaps md4) = vm_mmap_base h.
  Proof.
    rewrite commit_model_vmmaps, V3. (first [ pose proof (g_vmmaps) as dR_20; dand5 dR_20 as V1 V2 V4 V5 V6 | pose proof g_vmmaps as (V1 & V2 & V4 & V5 & V6) ]).
    unfold commit_vmmaps. cbn [vm_maps vm_reserved vm_limit vm_init_sp vm_mmap_base]. rewrite V1, V2, V4, V5, V6. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  Qed.
  Lemma c_halted : m_halted md4 = None.
  Proof. rewrite commit_model_halted. rewrite (same_but_materialized_halted _ _ SB3). exact g_halted. Qed.
  Lemma c_ceil : alloc_top (m_vmmaps md4) = alloc_ceiling.
  Proof. (first [ pose proof (c_vmmaps) as dR_21; dand5 dR_21 as _ _ _ E _ | pose proof c_vmmaps as (_ & _ & _ & E & _) ]). pose proof g_ceil as G. (first [ pose proof (g_vmmaps) as dR_22; dand5 dR_22 as _ _ _ E2 _ | pose proof g_vmmaps as (_ & _ & _ & E2 & _) ]). unfold alloc_top in *. rewrite E. rewrite E2 in G. exact G. Qed.
  Lemma c_budget_room : E3 = pa_eager A + ms -> nres' = kChunksBlockCount -> sr_reserved (a_sec A) = 0 ->
    E3 + 0x20000 + hull_bytes (pa_lhull A') <= vm_limit (m_vmmaps md3).
  Proof.
    intros -> NRE SR0. rewrite V3. (first [ pose proof (g_vmmaps) as dR_23; dand4 dR_23 as _ _ VL _ | pose proof g_vmmaps as (_ & _ & VL & _) ]). rewrite VL, LIMv.
    pose proof (wf_budget_room A' WF' (ai_extra _ _ _ _ _ _ _ AI)) as BR. unfold kBudgetRoom in BR. change (p_tlim (a_pl A')) with (p_tlim (a_pl A)) in BR.
    change (aeager_of A') with (pa_eager A') in BR. change (alhull_of AL_pboth A') with (pa_lhull A') in BR.
    rewrite (sec_eager A mb n key nres') in BR. rewrite SR0 in BR. replace (8 * (nres' - 0)) with 0x20000 in BR by (rewrite NRE; reflexivity). clear - BR. lia.
  Qed.
  Lemma c_budget : E3 + 0x20000 + hull_bytes (pa_lhull A') <= vm_limit (m_vmmaps md3) -> mmap_fixed_rw_budget_ok (wz 50) md3 paw blk = true.
  Proof.
    intros BR. apply (gate_fixed_rw_budget_ok (pa_hull A') (pa_lhull A') E3 (wz 50) paw blk md3 HI3).
    - pose proof c_gate as (G1 & _). rewrite BLW. exact G1.
    - exact (proj2 c_contained).
    - right. rewrite BLW. clear - BR. lia.
  Qed.
  Lemma sec_minv_commit : E3 + 0x20000 + hull_bytes (pa_lhull A') <= vm_limit (m_vmmaps md3) -> MInv (pa_hull A') (pa_lhull A') (E3 + 0x20000) md4.
  Proof.
    intros BR. rewrite <- BLW at 1. apply (MInv_commit_rw (pa_hull A') (pa_lhull A') E3 (wz 50) paw blk md3 HI3 mmap_noreserve_b_50).
    - pose proof c_gate as (G1 & _). rewrite BLW. exact G1.
    - exact (proj2 c_contained).
    - rewrite BLW. clear - BR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sec_ledger_commit : aledger_ AL_pboth (a_pl A) (a_reg A) sec' md4.
  Proof.
    destruct (sec_model_grant md3 SB3) as ((L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9) & _). (first [ pose proof (c_vmmaps) as dR_24; dand5 dR_24 as C1 C2 C3 C4 C5 | pose proof c_vmmaps as (C1 & C2 & C3 & C4 & C5) ]).
    (first [ pose proof (g_vmmaps) as dR_25; dand5 dR_25 as V1 V2 V4 V5 V6 | pose proof g_vmmaps as (V1 & V2 & V4 & V5 & V6) ]). rewrite V3 in *.
    unfold aledger_. cbv zeta. rewrite C1, C2, C3. rewrite V1, V2, V4 in *.
    split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [| split]]]]]].
    - apply Forall_forall. intros sc Hsc. pose proof (proj1 (Forall_forall _ _) L6 sc Hsc) as EM.
      (first [ pose proof ((bm_nth_fixed A)) as dR_26; dand3 dR_26 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]).
      (* [comment removed for export] *)
      assert (APT : cs_map sc + map_size (cs_n sc) <= pa \/ pa + kPtrArrayReserve <= cs_map sc).
      { cbn [sr_chunks] in Hsc. apply in_app_iff in Hsc as [Hsc|[<-|[]]].
        - apply In_nth_error' in Hsc as [i Hi]. pose proof (bm_sep A (15 + i) 1 _ _ _ _ W0 (bm_nth_sec A i sc Hi) E1 ltac:(lia)). unfold a_pa in *. lia.
        - cbn [cs_map cs_n]. pose proof (gf_APART A m md mbw ms AI MB0 MSP RF _ _ _ E1). unfold a_pa in *. lia. }
      assert (SCB : 0 <= cs_map sc /\ 0 < map_size (cs_n sc) /\ cs_map sc + map_size (cs_n sc) <= 2^47).
      { cbn [sr_chunks] in Hsc. apply in_app_iff in Hsc as [Hsc|[<-|[]]].
        - (first [ pose proof ((sec_chunk_bounds A sc W0 Hsc)) as dR_27; dand5 dR_27 as B1 _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W0 Hsc) as (B1 & _ & B3 & B4 & _) ]). apply app_facts in B3.
          pose proof (map_size_ge (cs_n sc)). unfold kMaxPrimaryUser in *. lia.
        - cbn [cs_map cs_n]. lia. }
      apply eager_map_commit; [exact (minv_noacc_nw HI3)| exact (minv_lazy_nw HI3)| | | exact EM].
      + unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite PAW, BLW. clear - PAF CE. unfold kPtrArrayReserve in PAF. lia.
      + rewrite PAW, BLW, !unsigned_lit by lia. unfold kPtrArrayReserve in APT. clear - APT SCB. lia.
    - apply cuts_covered_commit_contained; [exact (minv_noacc_nw HI3)| exact (minv_lazy_nw HI3)| | exact (proj2 c_contained)| exact L7].
      unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite PAW, BLW. clear - PAF CE. unfold kPtrArrayReserve in PAF. lia.
    - (* [comment removed for export] *)
      destruct L8 as [N1 N2].
      split; [split; (refine (noacc_free_commit_rw _ _ _ _ _ _ (minv_noacc_nw HI3) _); unfold noacc_free; rewrite V3; assumption)|].
      (* [comment removed for export] *)
      destruct L9 as (Z1 & Z2 & Z3).
      assert (T : forall lo hi, lazy_free (m_vm_lazy md3) lo hi -> lazy_free (m_vm_lazy md4) lo hi)
        by (intros lo hi Z0; exact (lazy_free_commit (wz 50) paw blk false md3 lo hi mmap_noreserve_b_50 (minv_lazy_nw HI3) Z0)).
      split; [exact (T _ _ Z1)|]. split; [exact (T _ _ Z2)|]. intros c Hc. destruct (Z3 c Hc) as [ZU ZF]. split; apply T; assumption.
  Qed.
  Lemma c_amd : amd_frame md md4.
  Proof.
    (first [ pose proof ((sec_model_grant md3 SB3)) as dR_28; dand4 dR_28 as _ _ _ F3 | destruct (sec_model_grant md3 SB3) as (_ & _ & _ & F3) ]). (first [ pose proof (c_vmmaps) as dR_29; dand5 dR_29 as C1 C2 C3 C4 C5 | pose proof c_vmmaps as (C1 & C2 & C3 & C4 & C5) ]). pose proof c_halted as HH4.
    (first [ pose proof ((commit_model_nonvm (wz 50) paw blk false md3)) as dR_30; dand6 dR_30 as B1 B2 B3 B4 B5 B6 | pose proof (commit_model_nonvm (wz 50) paw blk false md3) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    unfold amd_frame in *. rewrite C2, C3, C4, C5, B1, B2, B3, B4, B5, B6. (first [ pose proof (g_vmmaps) as dR_31; dand5 dR_31 as _ V2 V4 V5 V6 | pose proof g_vmmaps as (_ & V2 & V4 & V5 & V6) ]). rewrite V3, V2, V4, V5, V6 in F3.
    decompose [and] F3. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
  Lemma sec_model_commit : forall md5, same_but_materialized md4 md5 ->
    aledger_ AL_pboth (a_pl A) (a_reg A) sec' md5 /\ acover_ LPA (a_pl A) sec' (m_vmmaps md5) /\ alloc_top (m_vmmaps md5) = alloc_ceiling /\ amd_frame md md5 /\ m_halted md5 = None.
  Proof.
    intros md5 SB5. pose proof (same_but_materialized_vmmaps _ _ SB5) as V.
    split; [exact (aledger_sbm _ _ _ _ _ _ SB5 sec_ledger_commit)|].
    split; [rewrite V; (first [ pose proof (c_vmmaps) as dR_32; dand3 dR_32 as C1 C2 _ | pose proof c_vmmaps as (C1 & C2 & _) ]); apply (acover_vmmaps _ _ _ (m_vmmaps md2)); [rewrite C1; symmetry; exact (proj1 g_vmmaps)| rewrite C2; symmetry; exact (proj1 (proj2 g_vmmaps))| exact sec_cover_grant]|].
    split; [rewrite V; exact c_ceil|].
    pose proof c_amd as F. (first [ pose proof ((same_but_materialized_frame _ _ SB5)) as dR_33; dand18 dR_33 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | pose proof (same_but_materialized_frame _ _ SB5) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
    unfold amd_frame in *. rewrite X1, X2, X4, X5, X6, X7, X8, X17.
    decompose [and] F. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
  End Commit.
  End Grant.
End Model.
