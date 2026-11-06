(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMTac AMalmys AMaly5g ATransp ASecBN AWrapKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.
Ltac alc_h H := cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
       al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks al_internal_alloc_inited al_internal_allocator_inst
       al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore al_tp AL_pboth cl_tp cl_shared cl_consts cl_segs LPA] in H.

Section StatsShell.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md md1 : Model) (fp : Z) (v1 : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis CEIL : alloc_ceiling <= fp - ASTK.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) (fp - ASTK) ASTK.
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  (* [comment removed for export] *)
  Definition wexc (a : Z) : Prop := (thr + 2800 <= a < thr + 3168) \/ (0x5e7b34 <= a < 0x5e7b38).
  Hypothesis AG : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ wexc a -> v1 (wz a) = v (wz a).
  Hypothesis UNWB : rw_cells rsegs v1 (thr + 3168) [C1 (Z_to_bv 8 0)].
  Hypothesis WM : wmono rsegs v v1.
  Hypothesis CL : forall a, hidc (pa_hull A) a = true -> v1 a = None.
  Hypothesis HI : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
  Hypothesis SB : same_but_materialized md md1.

  Theorem shell_ainv_stats : @pa_ainv _ DepotRepL A (munrestrict (hidc (pa_hull A)) m v1) md1.
  Proof.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    pose proof alloc_ceiling_val as CE. unfold ASTK in *.
    (first [ pose proof ((hit_place A m md AI)) as dR_1; dand7 dR_1 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    destruct (asI_minv A m md AI) as [HMI HH].
    pose proof (shell_unw A m md v1 AI UNWB WM) as UNW.
    pose proof (shell_view A m v1 CL) as VIEW.
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v1 (wz a) <> None).
    { intros a Ha0 Ha1 Ha2. apply (wmono_NN _ _ a WM); lia. }
    pose proof (aobj_facts _ _ TH1) as THF. pose proof (aobj_facts _ _ CT1) as CTF.
    (* [comment removed for export] *)
    (first [ pose proof ((bm_nth_fixed A)) as dR_2; dand15 dR_2 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    pose proof (bm_sep A 0 4 _ _ _ _ WF0 E0 E4 ltac:(lia)) as ST0. pose proof (bm_sep A 1 4 _ _ _ _ WF0 E1 E4 ltac:(lia)) as ST1.
    pose proof (bm_sep A 5 4 _ _ _ _ WF0 E5 E4 ltac:(lia)) as ST5. pose proof (bm_sep A 6 4 _ _ _ _ WF0 E6 E4 ltac:(lia)) as ST6.
    pose proof (bm_sep A 7 4 _ _ _ _ WF0 E7 E4 ltac:(lia)) as ST7. pose proof (bm_sep A 8 4 _ _ _ _ WF0 E8 E4 ltac:(lia)) as ST8.
    pose proof (bm_sep A 14 4 _ _ _ _ WF0 E14 E4 ltac:(lia)) as ST14.
    unfold a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_pa in *.
    assert (STS : forall sc, In sc (sr_chunks (a_sec A)) -> cs_map sc + map_size (cs_n sc) <= thr \/ thr + 4096 <= cs_map sc).
    { intros sc Hin. apply In_nth_error in Hin as [j Hj]. exact (bm_sep A (15 + j) 4 _ _ _ _ WF0 (bm_nth_sec A j sc Hj) E4 ltac:(lia)). }
    (* [comment removed for export] *)
    assert (AGB : forall a, 0 <= a < alloc_ceiling -> ~ wexc a -> v1 (wz a) = v (wz a)).
    { intros a Ha NE. destruct (Z.eq_dec a (thr + 3168)) as [->|NT]; [exact UNW|]. apply AG; [clear -Ha CE; lia| clear -Ha CEIL; lia| exact NT| exact NE]. }
    (first [ pose proof ((place_facts A WF0)) as dR_3; dand13 dR_3 as _ _ Pn0 Pf0 Pfs _ _ _ _ _ Pdt Ppa _ | pose proof (place_facts A WF0) as (_ & _ & Pn0 & Pf0 & Pfs & _ & _ & _ & _ & _ & Pdt & Ppa & _) ]). cbv zeta in Pn0, Pf0, Pfs, Pdt, Ppa.
    (first [ dand3 Pn0 as Pn0 _ _ | destruct Pn0 as (Pn0 & _ & _) ]). (first [ dand3 Pf0 as Pf0 _ _ | destruct Pf0 as (Pf0 & _ & _) ]). (first [ dand3 Pfs as Pfs _ _ | destruct Pfs as (Pfs & _ & _) ]). (first [ dand3 Pdt as Pdt _ _ | destruct Pdt as (Pdt & _ & _) ]). (first [ dand3 Ppa as Ppa _ _ | destruct Ppa as (Ppa & _ & _) ]).
    apply app_facts in Pn0. apply app_facts in Pf0. apply app_facts in Pfs. apply app_facts in Pdt. apply app_facts in Ppa.
    (first [ pose proof ((sb_facts A WF0)) as dR_9; dand5 dR_9 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]).
    (* [comment removed for export] *)
    assert (AGapp : forall b0 n1 a, (4096 <= b0 /\ 0 <= n1 /\ b0 + n1 <= alloc_ceiling /\ (b0 + n1 <= 0x10000 \/ 0x60a000 <= b0) /\ (b0 + n1 <= kLowShadowMapBeg \/ kHighMemBeg <= b0)) ->
                    (b0 + n1 <= thr \/ thr + 4096 <= b0) -> b0 <= a < b0 + n1 -> v1 (wz a) = v (wz a)).
    { intros b0 n1 a Hb Hs Ha. apply AGB; [clear -Hb Ha; lia|]. unfold wexc. clear -Hb Ha Hs. lia. }
    (* [comment removed for export] *)
    assert (AGprim : forall a, a_b6 A <= a < a_b6 A + kSpaceReserve -> a < alloc_ceiling -> v1 (wz a) = v (wz a)).
    { intros a Ha Hc. apply AGB; [clear -Ha Hc HB6; kung_all; lia|]. unfold wexc. clear -Ha ST0 HB6. kung_all. lia. }
    assert (AGcarved : forall ch a, carved A ch -> chunk_lo (a_sb A) ch <= a < chunk_hi (a_sb A) ch -> v1 (wz a) = v (wz a)).
    { intros ch a C Ha. (first [ pose proof ((carved_range A v AR ch C)) as dR_10; dand3 dR_10 as R1 R2 _ | pose proof (carved_range A v AR ch C) as (R1 & R2 & _) ]).
      destruct ch as [[c k]|sc].
      - (* [comment removed for export] *)
        cbv delta [chunk_hi chunk_lo alloc_beg] in Ha, R2. cbv iota beta in Ha, R2.
        destruct C as [Hc Hk]. pose proof (region_piece_bounds A c WF0 Hc) as RB. cbv zeta in RB.
        (first [ pose proof ((carved_chunk_bounds A c k WF0 Hc Hk)) as dR_11; dand4 dR_11 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k WF0 Hc Hk) as (B1 & B2 & B3 & B4) ]).
        apply AGprim; [clear -Ha RB B1 B2 RSB HB6 SCE; unfold kRegionInfoSize in *; kung_all; lia| clear -Ha R2; lia].
      - (* [comment removed for export] *)
        cbn [carved] in C. pose proof (STS sc C) as SS. destruct sc as [mb n0]. cbn [chunk_lo chunk_hi cs_map cs_n] in Ha, R1, R2, SS.
        apply AGB; [clear -R1 R2 Ha; lia|]. unfold wexc. clear -R1 Ha SS. lia. }
    (* [comment removed for export] *)
    assert (IMGT : forall a, 0x10000 <= a < 0x60a000 -> ~ (thr + 2800 <= a < thr + 3168)) by (intros a Ha; clear -Ha THF; lia).
    (* [comment removed for export] *)
    assert (R' : @arepr _ DepotRepL LPA AL_pboth [] A v1).
    { constructor.
      - (* [comment removed for export] *) apply (consts_P A v v1 AR).
        + intros cst a Hin Ha. cbn [cl_consts LPA] in Hin.
          assert (BLW : a < alloc_ceiling /\ 0 <= a /\ ~ (thr + 2800 <= a < thr + 3168)).
          { destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
            - unfold pa_shared in S. clear -S CE THF. lia.
            - unfold pa_image_shadow, sh in S. clear -S CE THF. kung_all. unfold kLowShadowMapBeg in *. lia.
            - pose proof (pa_static_low a S). unfold pa_static in S. clear -S H CE THF. lia. }
          apply AGB; [clear -BLW; lia|].
          pose proof pa_consts_noexc as OK2. rewrite forallb_forall in OK2. specialize (OK2 cst Hin). unfold const_noexc in OK2.
          apply andb_true_iff in OK2 as [OK2 OK3]. apply orb_true_iff in OK3. rewrite !Z.leb_le in OK3.
          unfold wexc. clear -OK3 Ha BLW. lia.
        + intros a Ha. cbn [cl_shared LPA] in Ha. unfold pa_shared in Ha. apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia].
        + intros a Ha. unfold cfoot_stat in Ha. offs_h Ha. alc_h Ha. apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia].
        + intros a Ha. unfold cfoot_thr in Ha. offs_h Ha. apply AGB; [clear -Ha THF; lia| unfold wexc; clear -Ha THF; lia].
        + intros a Ha. unfold cfoot_misc in Ha. rewrite TPL in Ha.
          destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]];
            (apply AGB; [first [clear -Ha CTF; lia| clear -Ha CE; lia| clear -Ha Pdt; lia]
                        | unfold wexc; first [clear -Ha CTF ST5; lia| clear -Ha THF; lia| clear -Ha Pdt ST14; lia]]).
      - (* [comment removed for export] *) apply (locks_P A v v1 AR). intros a Ha. unfold lfoot in Ha. alc_h Ha. unfold p_ri in Ha. change (p_sb (a_pl A)) with (a_sb A) in Ha.
        destruct Ha as [Ha|Ha].
        + apply AGprim; [clear -Ha SCE RSB HB6; unfold kRegionInfoSize in Ha; kung_all; lia| clear -Ha SCE RSB; unfold kRegionInfoSize in Ha; kung_all; lia].
        + offs_h Ha. apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia].
      - (* [comment removed for export] *) intros c' Hc. apply (region_P A v v1 AR NN c' Hc). intros a Ha. unfold rfoot in Ha.
        pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. unfold region_info_addr, free_array_beg in Ha. change (p_sb (a_pl A)) with (a_sb A) in *.
        destruct Ha as [Ha|Ha]; (apply AGprim; [clear -Ha RB SCE RSB HB6 Hc; unfold kRegionInfoSize in *; kung_all; lia| clear -Ha RB SCE RSB Hc; unfold kRegionInfoSize in *; kung_all; lia]).
      - (* [comment removed for export] *)
        apply (cache_P A v v1 AR NN). intros c' Hc'. apply (cache_line_P A v v1 AR NN (a_cache A) c' Hc' eq_refl).
        intros a Ha. offs_h Ha. cbv beta in Ha. apply AGB; [clear -Ha Hc' THF; lia| unfold wexc; clear -Ha Hc' THF; lia].
      - (* [comment removed for export] *) apply (live_sub_P A v v1 AR NN (a_livemap A) (fun u li Hu => Hu)). intros u li a Hu Ha.
        exact (AGcarved _ a (known_carved A v AR _ _ (known_live A v AR u li Hu)) Ha).
      - (* [comment removed for export] *) apply (quar_P A v v1 AR NN).
        + intros a Ha. unfold off_th_qcache in Ha. apply AGB; [clear -Ha THF; lia| unfold wexc; clear -Ha THF; lia].
        + intros a Ha. alc_h Ha. unfold off_q_cache_list_size in Ha. apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia].
        + intros b a Hb Ha. (* [comment removed for export] *)
          destruct (batch_known A v AR b Hb) as [Hk _].
          assert (C24 : carved A (ChP (CP kQuarantineBatchClass (ba_idx b)))) by (split; [unfold kQuarantineBatchClass; clear; lia| exact Hk]).
          apply (AGcarved _ a C24).
          cbv delta [chunk_lo chunk_hi alloc_beg]. cbv iota beta. unfold batch_addr, kQuarantineBatchBytes in Ha.
          rewrite class_size_24. exact Ha.
        + intros e a He Ha. exact (AGcarved _ a (known_carved A v AR _ _ (known_quar A v AR e He)) Ha).
      - (* [comment removed for export] *) (first [ pose proof ((wfS A WF0)) as dR_12; dand4 dR_12 as _ LEN RES _ | destruct (wfS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. apply (sec_P A v v1 AR NN).
        + intros a Ha. unfold sfoot_stat in Ha. offs_h Ha. alc_h Ha. apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia].
        + intros a Ha. apply (AGapp _ _ a Ppa); [clear -ST1; unfold kPtrArrayReserve, kChunksBlockCount in *; lia|]. unfold kPtrArrayReserve. clear -Ha LEN RES. lia.
        + intros sc a Hin Ha. (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_13; dand5 dR_13 as _ _ SB3 SB4 SB5 | pose proof (sec_chunk_bounds A sc WF0 Hin) as (_ & _ & SB3 & SB4 & SB5) ]). apply app_facts in SB3.
          pose proof (needed_size2_secondary (cs_n sc) ltac:(destruct (sec_chunk_bounds A sc WF0 Hin) as (X & _); exact (proj1 X))) as NS2. pose proof (rounded_size_ge (cs_n sc)) as RG. unfold kSecondaryHeaderSize, kPageSize in *.
          apply AGB; [clear -Ha SB3 SB5 NS2 RG; lia| unfold wexc; pose proof (STS sc Hin) as SS; clear -Ha SB3 SB5 NS2 RG SS; lia].
      - (* [comment removed for export] *) apply (depot_P A v1 (a_depot A) v (ar_depot _ _ _ _ _ (proj2 AR))). intros a Ha.
        unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1 in Ha.
        destruct Ha as [Ha|[Ha|Ha]]; [apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia]
                                    | apply (AGapp _ _ a Pn0); [clear -ST7; kung_all; lia| exact Ha]
                                    | apply (AGapp _ _ a Pf0); [clear -ST8; kung_all; lia| exact Ha]].
      - (* [comment removed for export] *) apply (ia_P A v v1 AR). intros a Ha. unfold iafoot in Ha. offs_h Ha. alc_h Ha. unfold kDepotNodesL1 in Ha.
        apply AGB; [clear -Ha CE; lia| unfold wexc; clear -Ha THF; lia].
      - apply (fsbase_P A v v1 AR NN). intros a Ha. unfold a_fs in *. apply (AGapp _ _ a Pfs); [clear -ST6; unfold kFakeStackBytes in *; lia|]. unfold kFakeFlagsOffset, kFakeStackBytes in *. clear -Ha. lia.
      - apply (fsptrs_P A v v1 AR). intros a Ha. unfold a_fs in *. apply (AGapp _ _ a Pfs); [clear -ST6; unfold kFakeStackBytes in *; lia|]. unfold kFakeFramesOffset, kFakeStackBytes in *. clear -Ha. lia.
      - apply (fsflags_P A v v1 AR). intros a Ha. unfold a_fs in *. apply (AGapp _ _ a Pfs); [clear -ST6; unfold kFakeStackBytes in *; lia|]. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. clear -Ha. lia.
      - exact (maps_P A v v1 AR NN).
      - apply (shadow_P0 A v v1 AR). intros z Hz. pose proof (heap_shadow_range A z WF0 Hz) as SR. unfold in_shadow_maps, kLowShadowMapBeg in SR.
        (first [ pose proof (asI_layout_order) as dR_14; dand4 dR_14 as _ _ _ LO4 | pose proof asI_layout_order as (_ & _ & _ & LO4) ]). apply AGB; [clear -SR LO4; unfold kHighShadowMapSize in SR; kung_all; lia| unfold wexc; clear -SR THF; unfold kHighShadowMapSize, kLowShadowMapBeg in *; kung_all; lia]. }
    (* [comment removed for export] *)
    constructor.
    - exact WF0.
    - change (ahull_of pa_image_ivs AL_pboth A) with (pa_hull A). rewrite VIEW. exact R'.
    - (* [comment removed for export] *)
      pose proof (ai_hidden _ _ _ _ _ _ _ AI) as [H1 H2]. unfold hidden_repr. unfold munrestrict.
      assert (VIS : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> v1 (wz z) <> None).
      { intros z Hz Hm E. apply NN; [lia| lia| lia|]. unfold aview_of, mrestrict. rewrite E. exact Hm. }
      (first [ pose proof (asI_layout_order) as dR_15; dand4 dR_15 as _ _ _ LO4 | pose proof asI_layout_order as (_ & _ & _ & LO4) ]).
      split.
      + intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _].
        destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (conj P1 P2)|]. split.
        * apply VIS; [clear -Hz CE; unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in Hz; kung_all; lia| exact P1| exact E].
        * intros NHS. rewrite <- (P2 NHS). transitivity (v (wz z)); [| unfold aview_of, mrestrict; rewrite E; reflexivity].
          unfold in_shadow_maps, kHighShadowMapSize, kLowShadowMapBeg in Hz. apply AGB; [clear -Hz LO4; kung_all; lia| unfold wexc; clear -Hz THF; unfold kLowShadowMapBeg in *; kung_all; lia].
      + intros z Hz NB. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (H2 z Hz NB)|]. apply VIS; [clear -Hz CE; unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NB)| exact E].
    - exact (ai_extra _ _ _ _ _ _ _ AI).
    - exact (aledger_sbm _ _ _ _ md md1 SB (ai_ledger _ _ _ _ _ _ _ AI)).
    - exact HI.
    - pose proof (same_but_materialized_frame _ _ SB) as FRM. (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HH.
    - rewrite (same_but_materialized_vmmaps _ _ SB). exact (ai_cover _ _ _ _ _ _ _ AI).
    - rewrite (same_but_materialized_vmmaps _ _ SB). exact (ai_ceil _ _ _ _ _ _ _ AI).
  Qed.
End StatsShell.
