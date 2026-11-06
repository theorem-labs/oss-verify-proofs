(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState LayoutPA AInv ALogic1 ALogic2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac offs :=
  cbv delta [off_primary_reserved_base off_primary_reserved_size off_SpaceBeg off_release_interval off_RegionInfo_ptr off_PremappedHeap
             off_secondary off_sec_page_size off_sec_chunks off_sec_ptr_array_base off_sec_ptr_array_size off_sec_n_reserved off_sec_n_chunks
             off_sec_chunks_sorted off_sec_stat_n_allocs off_sec_stat_n_frees off_sec_stat_cur_alloc off_sec_stat_max_alloc off_sec_stat_by_size_log
             off_sec_mutex off_global_stats off_gstat_allocated off_gstat_mapped off_quarantine off_q_max_size off_q_min_size off_q_max_cache_size
             off_q_cache_mutex off_q_recycle_mutex off_q_cache_list_size off_q_cache_first off_q_cache_last off_q_cache_bytes off_fallback_mutex
             off_fallback_alloc_cache off_fallback_q_cache off_max_user_malloc off_min_redzone off_max_redzone off_alloc_dealloc_mismatch
             off_th_context off_th_stack_top off_th_stack_bottom off_th_stack_switching off_th_qcache off_th_qcache_n off_th_qcache_first
             off_th_qcache_last off_th_qcache_bytes off_th_alloc_cache off_th_per_class off_th_cache_stats off_th_cache_allocated off_th_cache_mapped
             off_th_stats off_th_unwinding off_pc_count off_pc_max_count off_pc_class_size off_pc_chunk kPerClassSize
             off_ri_mutex off_ri_num_freed off_ri_mapped_free_array off_ri_allocated_user off_ri_allocated_meta off_ri_mapped_user off_ri_mapped_meta
             off_ri_exhausted off_ri_n_allocated off_ri_n_freed off_ri_rtoi kRegionInfoSize
             off_qb_next off_qb_size off_qb_count off_qb_batch kQuarantineBatchBytes kChunkHeaderSize kSecondaryHeaderSize kCompactPtrScale
             kDepotNodesL1 kDepotNodesBlock kDepotTabBytes kStackStoreBlockBytes kChunksBlockCount kPtrArrayReserve kFakeFlagsOffset kFakeFramesOffset];
  cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
       al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks al_internal_alloc_inited al_internal_allocator_inst
       al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore al_tp AL_pasan cl_tp cl_shared cl_consts cl_segs LPA].

Ltac offs_h H := cbv delta [off_primary_reserved_base off_primary_reserved_size off_SpaceBeg off_release_interval off_RegionInfo_ptr off_PremappedHeap
             off_secondary off_sec_page_size off_sec_chunks off_sec_ptr_array_base off_sec_ptr_array_size off_sec_n_reserved off_sec_n_chunks
             off_sec_chunks_sorted off_sec_stat_n_allocs off_sec_stat_n_frees off_sec_stat_cur_alloc off_sec_stat_max_alloc off_sec_stat_by_size_log
             off_sec_mutex off_global_stats off_gstat_allocated off_gstat_mapped off_quarantine off_q_max_size off_q_min_size off_q_max_cache_size
             off_q_cache_mutex off_q_recycle_mutex off_q_cache_list_size off_q_cache_first off_q_cache_last off_q_cache_bytes off_fallback_mutex
             off_fallback_alloc_cache off_fallback_q_cache off_max_user_malloc off_min_redzone off_max_redzone off_alloc_dealloc_mismatch
             off_th_context off_th_stack_top off_th_stack_bottom off_th_stack_switching off_th_qcache off_th_qcache_n off_th_qcache_first
             off_th_qcache_last off_th_qcache_bytes off_th_alloc_cache off_th_per_class off_th_cache_stats off_th_cache_allocated off_th_cache_mapped
             off_th_stats off_th_unwinding off_pc_count off_pc_max_count off_pc_class_size off_pc_chunk kPerClassSize
             off_ri_mutex off_ri_num_freed off_ri_mapped_free_array off_ri_allocated_user off_ri_allocated_meta off_ri_mapped_user off_ri_mapped_meta
             off_ri_exhausted off_ri_n_allocated off_ri_n_freed off_ri_rtoi kRegionInfoSize
             off_qb_next off_qb_size off_qb_count off_qb_batch kQuarantineBatchBytes kChunkHeaderSize kSecondaryHeaderSize kCompactPtrScale
             kDepotNodesL1 kDepotNodesBlock kDepotTabBytes kStackStoreBlockBytes kChunksBlockCount kPtrArrayReserve kFakeFlagsOffset kFakeFramesOffset] in H.

Section Pasan.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Context {DR : DepotRep}.
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sel.
  Variable A : AState.
  Let FT := afoot LPA AL_pasan A.
  Ltac pre := intros; unfold FT, afoot, afoot_; cbv zeta.

  Lemma af_stat : forall a, rt_statics AL_pasan a -> FT a. Proof. pre. left. assumption. Qed.
  Lemma af_shared : forall a, cl_shared LPA a -> FT a. Proof. pre. do 1 right. left. assumption. Qed.
  Lemma af_consts : forall a c, In c (cl_consts LPA) -> fst c <= a < fst c + Z.of_nat (length (snd c)) -> FT a. Proof. pre. do 2 right. left. eauto. Qed.
  Lemma af_tsd : forall a, bv_unsigned (cl_tp LPA) - 88 <= a < bv_unsigned (cl_tp LPA) - 80 -> FT a. Proof. pre. do 3 right. left. assumption. Qed.
  Lemma af_tp : forall a, bv_unsigned (cl_tp LPA) <= a < bv_unsigned (cl_tp LPA) + 8 -> FT a. Proof. pre. do 4 right. left. assumption. Qed.
  Lemma af_thr : forall a, a_thr A <= a < a_thr A + 4096 -> FT a. Proof. pre. do 5 right. left. assumption. Qed.
  Lemma af_ctx : forall a, a_ctx A <= a < a_ctx A + 0x10000 -> FT a. Proof. pre. do 6 right. left. assumption. Qed.
  Lemma af_ri : forall a, a_ri A <= a < a_ri A + 4096 -> FT a. Proof. pre. do 7 right. left. assumption. Qed.
  Lemma af_fa : forall a c, 1 <= c <= 30 -> free_array_beg (a_sb A) c <= a < free_array_beg (a_sb A) c + rg_mapped_fa (a_reg A c) -> FT a.
  Proof. pre. do 8 right. left. eauto. Qed.
  Lemma af_hdr_live : forall a u li, a_livemap A !! u = Some li -> hdr_foot (a_sb A) (li_chunk li) (li_n li) a -> FT a. Proof. pre. do 9 right. left. eauto. Qed.
  Lemma af_quar : forall a e, In e (q_entries (a_qthread A ++ a_qglobal A)) ->
    (hdr_foot (a_sb A) (qe_chunk e) (qe_n e) a \/ user_of (a_sb A) (qe_chunk e) (qe_n e) <= a < user_of (a_sb A) (qe_chunk e) (qe_n e) + 8) -> FT a.
  Proof. pre. do 10 right. left. eauto. Qed.
  Lemma af_batch : forall a b, In b (a_qthread A ++ a_qglobal A) -> batch_addr (a_sb A) b <= a < batch_addr (a_sb A) b + kQuarantineBatchBytes -> FT a.
  Proof. pre. do 11 right. left. eauto. Qed.
  Lemma af_pa : forall a, a_pa A <= a < a_pa A + 8 * kChunksBlockCount -> FT a. Proof. pre. do 12 right. left. assumption. Qed.
  Lemma af_sechdr : forall a s, In s (sr_chunks (a_sec A)) -> cs_map s <= a < cs_map s + kSecondaryHeaderSize -> FT a. Proof. pre. do 13 right. left. eauto. Qed.
  Lemma af_fshdr : forall a, a_fs A <= a < a_fs A + kFakeFlagsOffset -> FT a. Proof. pre. do 14 right. left. assumption. Qed.
  Lemma af_ptr : forall a ff f, a_fframes A !! ff = Some f -> saved_flag_ptr ff (ff_class f) <= a < saved_flag_ptr ff (ff_class f) + 8 -> FT a.
  Proof. pre. do 15 right. left. eauto. Qed.
  Lemma af_hs : forall a, heap_shadow A a -> FT a. Proof. pre. do 16 right. left. assumption. Qed.
  Lemma af_depot : forall a, depot_foot AL_pasan (a_nodes0 A) (a_frames0 A) a -> FT a. Proof. pre. do 17 right. left. assumption. Qed.
  Lemma af_tp40 : forall a, bv_unsigned (cl_tp LPA) + 8 <= a < bv_unsigned (cl_tp LPA) + 16 -> FT a.   (* [comment removed for export] *) Proof. pre. do 18 right. left. assumption. Qed.
  Lemma af_dtls : forall a, p_dtls (a_pl A) <= a < p_dtls (a_pl A) + 4096 -> FT a. Proof. pre. do 19 right. assumption. Qed.
End Sel.

(* [comment removed for export] *)
Lemma afoot_not_flags : forall A m md a, pa_ainv A m md -> afoot LPA AL_pasan A a -> ~ flags_area (a_fs A) a.
Proof.
  intros A m md a AI FT FL. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE. unfold flags_area in FL.
  (first [ pose proof ((place_fs A W)) as dR_1; dand3 dR_1 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]). (first [ pose proof ((sb_facts A W)) as dR_2; dand5 dR_2 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
  (first [ pose proof ((bm_nth_fixed A)) as dR_3; dand15 dR_3 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
  assert (INFS : a_fs A <= a < a_fs A + kFakeStackBytes) by (try (generalize alloc_ceiling_val); clear - FL; kun; lia).
  assert (SEP : forall i b s, i <> 6%nat -> nth_error (big_maps A) i = Some (b, s) -> b <= a < b + s -> False).
  { intros i b s Hi Hn Hb. destruct (bm_sep A i 6 _ _ _ _ W Hn E6 Hi); unfold a_fs in *; lia. }
  assert (B6 : forall x, a_sb A <= x < a_sb A + kSpaceSize + 4096 -> x = a -> False).
  { intros x Hx ->. eapply (SEP 0%nat); [lia| exact E0| apply primary_in_b6; assumption]. }
  (first [ pose proof ((app_facts _ _ FS1)) as dR_4; dand5 dR_4 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
  assert (IMGX : 0x10000 <= a < 0x60a000 -> False) by (clear - INFS G4; unfold a_fs, kFakeStackBytes in *; lia).
  assert (SHX : in_shadow_maps a -> False) by (intros SM; apply (app_not_in_shadow_maps a); [clear - INFS G5; unfold a_fs in *; lia| exact SM]).
  unfold afoot, afoot_ in FT. cbv zeta in FT. cbn [cl_tp cl_shared cl_consts LPA] in FT. rewrite unsigned_lit in FT by lia.
  change (p_sb (a_pl A)) with (a_sb A) in FT.
  destruct FT as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]]]]].
  - apply IMGX. pose proof (rt_statics_static a F) as S. clear - S. unfold pa_static in *. lia.
  - apply IMGX. clear - F. unfold pa_shared in F. lia.
  - (first [ dex1 F as c; destruct F as [Hc Ha] | dand3 F as c Hc Ha | destruct F as (c & Hc & Ha) ]). destruct (pa_consts_where c a Hc Ha) as [S|[S|S]]; [apply IMGX; clear - S; unfold pa_shared in S; lia| exact (SHX (image_shadow_in_maps a S)) | apply IMGX; clear - S; unfold pa_static in S; lia].
  - apply IMGX; lia.
  - apply IMGX; lia.
  - eapply (SEP 4%nat); [lia| exact E4| exact F].
  - eapply (SEP 5%nat); [lia| exact E5| exact F].
  - apply (B6 a); [unfold a_ri, p_ri, a_sb, kSpaceSize in *; lia| reflexivity].
  - (first [ dex1 F as c; destruct F as [Hc Ha] | dand3 F as c Hc Ha | destruct F as (c & Hc & Ha) ]). unfold free_array_beg in Ha. pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
    apply (B6 a); [unfold kRegionSize, kFreeArrayOffset in *; lia| reflexivity].
  - (first [ dex2 F as u li; destruct F as [Hl HF] | dand4 F as u li Hl HF | destruct F as (u & li & Hl & HF) ]). destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_8; dand3 dR_8 as N U C | pose proof (V1 u li Hl) as (N & U & C) ]). cbv zeta in *. unfold hdr_foot in HF.
    destruct li as [[[c k]|[mb n0]] n]; cbn [li_chunk li_n] in *.
    + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
      (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_10; dand5 dR_10 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_11; dand3 dR_11 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      apply (B6 a); [unfold kChunkHeaderSize, kRegionSize, kFreeArrayOffset in *; lia| reflexivity].
    + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_13; dand7 dR_13 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_14; dand5 dR_14 as _ _ _ _ MR | pose proof (sec_chunk_bounds A _ W Hin) as (_ & _ & _ & _ & MR) ]). cbn [cs_n cs_map] in MR.
      destruct (In_nth_error' _ _ Hin) as [j Hj]. eapply (SEP (15 + j)%nat); [lia| apply (bm_nth_sec A j _ Hj)|].
      cbn [cs_map cs_n]. unfold kChunkHeaderSize, kSecondaryHeaderSize, kPageSize in *. lia.
  - (first [ dex1 F as e; destruct F as [He HF] | dand3 F as e He HF | destruct F as (e & He & HF) ]). (first [ pose proof ((wfQ A W)) as dR_16; dand3 dR_16 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]).
    assert (WE : wf_qentry_ (a_reg A) (a_sec A) e).
    { unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
      [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
      (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB e Heb). }
    destruct WE as (N & C). unfold hdr_foot in HF. destruct e as [[[c k]|[mb n0]] n]; cbn [qe_chunk qe_n] in *.
    + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
      (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_19; dand5 dR_19 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_20; dand3 dR_20 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      apply (B6 a); [unfold kChunkHeaderSize, kRegionSize, kFreeArrayOffset in *; lia| reflexivity].
    + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_22; dand7 dR_22 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_23; dand5 dR_23 as _ _ _ _ MR | pose proof (sec_chunk_bounds A _ W Hin) as (_ & _ & _ & _ & MR) ]). cbn [cs_n cs_map] in MR.
      destruct (In_nth_error' _ _ Hin) as [j Hj]. eapply (SEP (15 + j)%nat); [lia| apply (bm_nth_sec A j _ Hj)|].
      cbn [cs_map cs_n]. unfold kChunkHeaderSize, kSecondaryHeaderSize, kPageSize in *. lia.
  - (first [ dex1 F as b; destruct F as [Hb Ha] | dand3 F as b Hb Ha | destruct F as (b & Hb & Ha) ]). (first [ pose proof ((wfQ A W)) as dR_25; dand3 dR_25 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]).
    assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
    { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
    (first [ dand3 WB as _ Hk _ | destruct WB as (_ & Hk & _) ]). assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    unfold batch_addr in Ha. rewrite <- class_size_24 in Ha.
    (first [ pose proof ((carved_chunk_bounds A _ _ W C24 Hk)) as dR_27; dand3 dR_27 as B1 B2 _ | pose proof (carved_chunk_bounds A _ _ W C24 Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A _ W C24) as RB. cbv zeta in *.
    apply (B6 a); [unfold kRegionSize, kFreeArrayOffset in *; lia| reflexivity].
  - eapply (SEP 1%nat); [lia| exact E1| unfold a_pa, kChunksBlockCount, kPtrArrayReserve in *; lia].
  - (first [ dex1 F as sc; destruct F as [Hin Ha] | dand3 F as sc Hin Ha | destruct F as (sc & Hin & Ha) ]). destruct (In_nth_error' _ _ Hin) as [j Hj].
    (first [ pose proof ((sec_chunk_bounds A sc W Hin)) as dR_29; dand5 dR_29 as N _ _ _ MR | pose proof (sec_chunk_bounds A sc W Hin) as (N & _ & _ & _ & MR) ]). pose proof (needed_size_ge (cs_n sc)).
    eapply (SEP (15 + j)%nat); [lia| apply (bm_nth_sec A j _ Hj)|].
    rewrite needed_size2_secondary in MR by lia. pose proof (rounded_size_ge (cs_n sc)). unfold kSecondaryHeaderSize, kPageSize in *. lia.
  - unfold a_fs, kFakeFlagsOffset in *. lia.
  - (first [ dex2 F as ff f; destruct F as [Hf Ha] | dand4 F as ff f Hf Ha | destruct F as (ff & f & Hf & Ha) ]). unfold saved_flag_ptr in Ha.
    pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. (first [ dand10 FF as K _ _ R1 R2 _ _ _ SZ _ | destruct FF as (K & _ & _ & R1 & R2 & _ & _ & _ & SZ & _) ]).
    unfold a_fs, kFakeFramesOffset in *. lia.
  - exact (SHX (heap_shadow_range A a W F)).
  - destruct F as [F|[F|F]].
    + apply IMGX. pose proof (depot_static a F) as S. clear - S. unfold pa_static in *. lia.
    + eapply (SEP 7%nat); [lia| exact E7| exact F].
    + eapply (SEP 8%nat); [lia| exact E8| exact F].
  - apply IMGX; lia.
  - eapply (SEP 14%nat); [lia| exact E14| exact F].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shpat_length_nat : forall n, 0 <= n -> length (shpat n) = Z.to_nat ((n + 7) / 8).
Proof. intros n Hn. pose proof (shpat_length n Hn). lia. Qed.
Lemma pshadow_live_length : forall c n, 0 <= n <= kMaxPrimaryUser -> c = class_of n -> Z.of_nat (length (pshadow_live c n)) = class_size c / 8.
Proof.
  intros c n Hn Hc. unfold pshadow_live, fa8. rewrite !length_app, !repeat_length.
  (first [ pose proof ((user_size_pos n ltac:(lia))) as dR_32; dand3 dR_32 as U1 U2 U3 | pose proof (user_size_pos n ltac:(lia)) as (U1 & U2 & U3) ]). rewrite shpat_length_nat by lia.
  pose proof (user_end_fits 0 n Hn) as [F1 F2]. rewrite <- Hc in F2. unfold user_beg in F1.
  pose proof (rz_size_range n). pose proof (rz_size_mod16 n) as RM. pose proof (class_size_mod32 c ltac:(rewrite Hc; apply class_of_range; lia)) as CM.
  pose proof (Z_div_exact_full_2 (rz_size n) 8 ltac:(lia) (mod0_down _ 16 8 (divide_wit 8 2) RM)).
  pose proof (Z_div_exact_full_2 (class_size c) 8 ltac:(lia) (mod0_down _ 32 8 (divide_wit 8 4) CM)).
  assert ((user_size n + 7) / 8 <= class_size c / 8 - rz_size n / 8).
  { assert ((user_size n + 7) / 8 < class_size c / 8 - rz_size n / 8 + 1); [|lia]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  assert (0 <= (user_size n + 7) / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma pshadow_quar_length : forall c n, 0 <= n <= kMaxPrimaryUser -> c = class_of n -> Z.of_nat (length (pshadow_quar c n)) = class_size c / 8.
Proof.
  intros c n Hn Hc. pose proof (pshadow_live_length c n Hn Hc) as L. unfold pshadow_quar, pshadow_live, fa8, fd8 in *.
  rewrite !length_app, !repeat_length in *. rewrite shpat_length_nat in L by (pose proof (user_size_pos n ltac:(lia)); lia). lia.
Qed.
Lemma sshadow_live_length : forall n, kMaxPrimaryUser < n -> Z.of_nat (length (sshadow_live n)) = map_size n / 8.
Proof.
  intros n Hn. unfold sshadow_live, fa8. rewrite !length_app, !repeat_length.
  (first [ pose proof ((user_size_pos n ltac:(unfold kMaxPrimaryUser in Hn; lia))) as dR_33; dand3 dR_33 as U1 U2 U3 | pose proof (user_size_pos n ltac:(unfold kMaxPrimaryUser in Hn; lia)) as (U1 & U2 & U3) ]). rewrite shpat_length_nat by lia.
  (first [ pose proof ((secondary_layout 0 n Hn)) as dR_34; dand7 dR_34 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout 0 n Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). unfold sec_user_beg, kPageSize in *.
  pose proof (map_size_page n) as MP. pose proof (Z_div_exact_full_2 (map_size n) 8 ltac:(lia) (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP)).
  assert ((user_size n + 7) / 8 <= map_size n / 8 - 768).
  { assert ((user_size n + 7) / 8 < map_size n / 8 - 768 + 1); [|lia]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  assert (0 <= (user_size n + 7) / 8) by (apply Z.div_pos; lia). change (Z.of_nat (Z.to_nat 768)) with 768. lia.
Qed.
Lemma sshadow_quar_length : forall n, kMaxPrimaryUser < n -> Z.of_nat (length (sshadow_quar n)) = map_size n / 8.
Proof.
  intros n Hn. pose proof (sshadow_live_length n Hn) as L. unfold sshadow_quar, sshadow_live, fa8, fd8 in *.
  rewrite !length_app, !repeat_length in *. rewrite shpat_length_nat in L by (pose proof (user_size_pos n ltac:(unfold kMaxPrimaryUser in Hn; lia)); lia). lia.
Qed.

Lemma div8_ceil_exact : forall x, x mod 8 = 0 -> (x + 7) / 8 = x / 8.
Proof.
  intros x Hx. pose proof (Z_div_exact_full_2 x 8 ltac:(lia) Hx) as E.
  replace (x + 7) with (x / 8 * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
Qed.

Section Transport.
  Variables (A : AState) (m m' : mem) (md : Model).
  Let v := aview_of (pa_hull A) m.
  Let v' := aview_of (pa_hull A) m'.
  Hypothesis AI : pa_ainv A m md.
  Hypothesis AGF : forall a, afoot LPA AL_pasan A a -> v' (wz a) = v (wz a).
  Hypothesis NN : forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v (wz a) <> None -> v' (wz a) <> None.

  Let W : WF A := ai_wf _ _ _ _ _ _ _ AI.
  Let R : arepr LPA AL_pasan [] A v := ai_repr _ _ _ _ _ _ _ AI.

  (* [comment removed for export] *)
  Lemma NN' : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v' (wz a) <> None.
  Proof. intros a H0 H1 H2 H3. apply NN; [lia| | exact H3]. unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. lia. Qed.
  Lemma mapped_T : forall a n, 0 <= a -> (a + n <= 0x10000 \/ 0x60a000 <= a) -> a + n <= 2^64 -> mapped v a n -> mapped v' a n.
  Proof. intros a n H0 H1 H2 M. eapply mapped_mono; [exact M|]. intros i Hi. apply NN'; lia. Qed.

  (* [comment removed for export] *)
  Let AGstat := fun a H => AGF a (af_stat A a H).
  Let AGshared := fun a H => AGF a (af_shared A a H).
  Let AGthr := fun a H => AGF a (af_thr A a H).
  Let AGctx := fun a H => AGF a (af_ctx A a H).
  Let AGri := fun a H => AGF a (af_ri A a H).
  Let AGpa := fun a H => AGF a (af_pa A a H).
  Let AGfs := fun a H => AGF a (af_fshdr A a H).
  Let AGhs := fun a H => AGF a (af_hs A a H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac trim := repeat match goal with H : _ /\ _ /\ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : arepr _ _ _ _ _ |- _ => clear H end.
  Ltac by_stat := apply AGstat; trim; unfold rt_statics; offs; lia.
  Ltac by_thr := apply AGthr; trim; unfold a_thr; offs; lia.
  Ltac by_ctx := apply AGctx; trim; unfold a_ctx; offs; lia.
  (* [comment removed for export] *)
  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.
  (* [comment removed for export] *)
  Ltac walk H AG :=
    lazymatch goal with
    | |- _ /\ _ => let H1 := fresh "L" in let H2 := fresh "L" in destruct H as [H1 H2]; split; [walk H1 AG | walk H2 AG]
    | |- _ => leaf H AG
    end.

  Lemma consts_T : consts_repr_ LPA AL_pasan (a_pl A) v'.
  Proof.
    pose proof (ar_consts _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE.
    unfold consts_repr_ in *. cbv zeta in *. destruct C as (CF & C).
    split.
    { apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) CF c Hc) as B.
      eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply AGF. apply (af_consts A _ c Hc). lia. }
    (* [comment removed for export] *)
    do 17 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_stat |]).
    (first [ dand7 C as K1 K2 K3 KS KE1 KE2 C | destruct C as (K1 & K2 & K3 & KS & KE1 & KE2 & C) ]).
    split; [leaf K1 ltac:(apply AGshared; apply KS; lia)|]. split; [leaf K2 ltac:(apply AGshared; rewrite KE1; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [leaf K3 ltac:(apply AGshared; rewrite KE2; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [exact KS|]. split; [exact KE1|]. split; [exact KE2|].
    do 7 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_stat |]).
    do 5 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_thr |]).
    do 2 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_ctx |]).
    destruct C as [(tsd & T1 & T2 & T3) C]. split.
    - exists tsd. split; [|split; [exact T2|]].
      + leaf T1 ltac:(apply AGF; apply af_tsd; offs; lia).
      + leaf T3 ltac:(apply AGshared; apply T2; lia).
    - (first [ dand5 C as C D1 D2 D3 D4 | destruct C as (C & D1 & D2 & D3 & D4) ]). split; [leaf C ltac:(apply AGF; apply af_tp; offs; lia)|].
      split; [leaf D1 ltac:(apply AGF; apply af_tp40; offs; lia)|].
      split; [leaf D2 ltac:(apply AGF; apply af_dtls; offs; lia)|].
      split; [leaf D3 by_thr| leaf D4 by_thr].
  Qed.

  Lemma locks_T : locks_repr_ LPA AL_pasan (a_pl A) [] v'.
  Proof.
    pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    split.
    - intros c Hc. destruct (C0 c Hc) as [X Y]. split; [leaf X ltac:(apply AGri; unfold a_ri; offs; lia) | leaf Y ltac:(apply AGri; unfold a_ri; offs; lia)].
    - walk C by_stat.
  Qed.

  Lemma regions_T : forall c, 1 <= c <= 30 -> region_repr_ LPA (a_sb A) (a_reg A c) v' c.
  Proof.
    intros c Hc. pose proof (ar_regions _ _ _ _ _ R c Hc) as C. pose proof alloc_ceiling_val as CE.
    pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB. (first [ pose proof ((wfR A W)) as dR_37; dand3 dR_37 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c Hc)) as dR_38; dand8 dR_38 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (WR c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]).
    unfold region_repr_ in *. cbv zeta in *. unfold region_info_addr, free_array_beg in *.
    assert (AGri' : forall x, a_sb A + kSpaceSize + kRegionInfoSize * c <= x < a_sb A + kSpaceSize + kRegionInfoSize * c + 128 -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AGri. unfold a_ri, p_ri, a_sb, kRegionInfoSize, kSpaceSize in *. lia. }
    assert (AGfa' : forall x, region_beg (a_sb A) c + kFreeArrayOffset <= x < region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AGF. apply (af_fa A x c Hc). unfold free_array_beg. exact Hx. }
    do 10 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGri'; offs; lia) |]).
    (first [ dand3 C as CF M1 M2 | destruct C as (CF & M1 & M2) ]). split; [|split].
    - intros i k E. pose proof (CF i k E) as LF. assert (Z.of_nat i < Z.of_nat (length (rg_free (a_reg A c)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf LF ltac:(apply AGfa'; offs; lia).
    - apply mapped_T; [unfold kHighMemBeg, kFreeArrayOffset in *; lia| right; unfold kHighMemBeg, kFreeArrayOffset in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M1].
    - apply mapped_T; [unfold kHighMemBeg in *; lia| right; unfold kHighMemBeg in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M2].
  Qed.

  Lemma cache_T : cache_repr_ LPA (a_pl A) (a_cache A) (a_cache_inited A) v'.
  Proof.
    pose proof (ar_cache _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_facts A W)) as dR_40; dand3 dR_40 as Pthr Pctx _ | pose proof (place_facts A W) as (Pthr & Pctx & _) ]). cbv zeta in Pthr, Pctx.
    (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). apply app_facts in Pthr1. (first [ dand3 Pctx as Pctx1 Pctx2 Pctx3 | destruct Pctx as (Pctx1 & Pctx2 & Pctx3) ]). apply app_facts in Pctx1.
    unfold cache_repr_ in *. cbv zeta in *. (first [ dand5 C as C0 J1 J2 M1 M2 | destruct C as (C0 & J1 & J2 & M1 & M2) ]).
    split; [| split; [leaf J1 by_thr| split; [leaf J2 by_thr| split; apply mapped_T; try assumption; clear - Pthr1 Pthr2 Pctx1 Pctx2 CE; lia]]].
    intros c Hc. (first [ pose proof ((C0 c Hc)) as dR_44; dand5 dR_44 as LEN X1 X2 X3 X4 | destruct (C0 c Hc) as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|]. split; [leaf X1 by_thr|]. split; [|split].
    - destruct (a_cache_inited A && negb (c =? 0)); destruct X2 as [Y1 Y2]; split; first [leaf Y1 by_thr | leaf Y2 by_thr].
    - intros i k E. pose proof (X3 i k E) as L.
      assert (Z.of_nat i < Z.of_nat (length (pk_chunks (a_cache A c)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L by_thr.
    - leaf X4 by_thr.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_T : forall ch n st, (forall a, hdr_foot (a_sb A) ch n a -> v' (wz a) = v (wz a)) ->
    hdr_repr_ LPA (a_sb A) v ch n st -> hdr_repr_ LPA (a_sb A) v' ch n st.
  Proof.
    intros ch n st AG [(id & b1 & Hid & Hb1 & Hb1m & RC) LH]. split.
    - exists id, b1. split; [exact Hid|]. split; [exact Hb1|]. split; [exact Hb1m|].
      eapply rw_cells_agree; [exact RC|]. rewrite chunk_hdr_size. intros i Hi. apply AG. unfold hdr_foot. left. lia.
    - intros NE. destruct (LH NE) as [X Y]. split; [leaf X ltac:(apply AG; unfold hdr_foot; right; lia) | leaf Y ltac:(apply AG; unfold hdr_foot; right; lia)].
  Qed.

  Lemma chunk_mapped_T : forall ch n, (exists u li, a_livemap A !! u = Some li /\ li_chunk li = ch /\ li_n li = n) \/ In (QE ch n) (q_entries (a_qthread A ++ a_qglobal A)) ->
    mapped v (chunk_lo (a_sb A) ch) (chunk_hi (a_sb A) ch - chunk_lo (a_sb A) ch) -> mapped v' (chunk_lo (a_sb A) ch) (chunk_hi (a_sb A) ch - chunk_lo (a_sb A) ch) /\
    0x60a000 <= user_of (a_sb A) ch n /\ user_of (a_sb A) ch n + 8 <= alloc_ceiling /\ user_of (a_sb A) ch n + n <= alloc_ceiling.
    (* [comment removed for export] *)
  Proof.
    intros ch n H M. pose proof alloc_ceiling_val as CE.
    assert (CL : match ch with ChP (CP c k) => 1 <= c <= 30 /\ 0 <= k < carved_count A c /\ 0 <= n <= kMaxPrimaryUser /\ c = class_of n
                               | ChS (CS mb n0) => In (CS mb n0) (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < n /\ n0 = n end).
    { destruct H as [(u & li & Hl & <- & <-)|Hq].
      - destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_45; dand3 dR_45 as N U C | pose proof (V1 u li Hl) as (N & U & C) ]). cbv zeta in C.
        destruct (li_chunk li) as [[c k]|[mb n0]].
        + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range (li_n li) ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
        + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2].
      - (first [ pose proof ((wfQ A W)) as dR_48; dand3 dR_48 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]).
        assert (WE : wf_qentry_ (a_reg A) (a_sec A) (QE ch n)).
        { unfold q_entries in Hq. apply in_flat_map in Hq as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
          [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
          (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB _ Heb). }
        destruct WE as (N & C). cbn [qe_chunk qe_n] in *. destruct ch as [[c k]|[mb n0]].
        + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
        + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2]. }
    destruct ch as [[c k]|[mb n0]].
    - (first [ dand4 CL as CR Hk Hn Hc | destruct CL as (CR & Hk & Hn & Hc) ]). (first [ pose proof ((primary_layout (a_sb A) c k n CR Hn Hc)) as dR_53; dand5 dR_53 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR Hn Hc) as (L1 & L2 & L3 & L5 & L4) ]).
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_54; dand3 dR_54 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      cbn [chunk_lo chunk_hi alloc_beg user_of] in *. unfold kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *.
      split; [apply mapped_T; [lia| right; lia| lia| exact M]|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n Hn)) as dR_56; dand7 dR_56 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
      (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_57; dand5 dR_57 as _ _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ W Hin) as (_ & _ & B3 & B4 & B5) ]). cbn [cs_map cs_n chunk_lo chunk_hi user_of] in *.
      apply app_facts in B3. pose proof (needed_size_ge n). rewrite needed_size2_secondary in B5 by lia. pose proof (rounded_size_ge n).
      unfold kMaxPrimaryUser, kPageSize, kSecondaryHeaderSize in *. split; [apply mapped_T; [lia| right; lia| lia| exact M]|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  Lemma live_T : live_repr_ LPA (a_sb A) (a_livemap A) v'.
  Proof.
    intros u li Hl. (first [ pose proof ((ar_live _ _ _ _ _ R u li Hl)) as dR_58; dand3 dR_58 as HR MU MC | destruct (ar_live _ _ _ _ _ R u li Hl) as (HR & MU & MC) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((chunk_mapped_T (li_chunk li) (li_n li) ltac:(left; exists u, li; auto) MC)) as dR_59; dand4 dR_59 as MC' G1 G2 G3 | destruct (chunk_mapped_T (li_chunk li) (li_n li) ltac:(left; exists u, li; auto) MC) as (MC' & G1 & G2 & G3) ]).
    destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_60; dand3 dR_60 as N U _ | pose proof (V1 u li Hl) as (N & U & _) ]).
    split; [|split].
    - apply hdr_T; [|exact HR]. intros a Ha. apply AGF. eapply af_hdr_live; eauto.
    - apply mapped_T; [rewrite U; lia| right; rewrite U; lia| rewrite U; lia| exact MU].
    - exact MC'.
  Qed.

  Lemma batches_T : forall bs, (forall b, In b bs -> In b (a_qthread A ++ a_qglobal A)) ->
    batches_repr LPA v (a_sb A) bs -> batches_repr LPA v' (a_sb A) bs.
  Proof.
    induction bs as [|b bs IH]; intros SUB BR; [exact I|]. pose proof alloc_ceiling_val as CE.
    cbn [batches_repr] in *. (first [ dand6 BR as X1 X2 X3 X4 M BR | destruct BR as (X1 & X2 & X3 & X4 & M & BR) ]).
    assert (INb : In b (a_qthread A ++ a_qglobal A)) by (apply SUB; left; reflexivity).
    (first [ pose proof ((wfQ A W)) as dR_62; dand3 dR_62 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]).
    assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
    { apply in_app_iff in INb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
    (first [ dand3 WB as LEN Hk _ | destruct WB as (LEN & Hk & _) ]).
    assert (AGb : forall x, batch_addr (a_sb A) b <= x < batch_addr (a_sb A) b + kQuarantineBatchBytes -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AGF. eapply af_batch; eauto. }
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    (first [ pose proof ((carved_chunk_bounds A _ _ W C24 Hk)) as dR_64; dand3 dR_64 as B1 B2 _ | pose proof (carved_chunk_bounds A _ _ W C24 Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A _ W C24) as RB. cbv zeta in *.
    split; [leaf X1 ltac:(apply AGb; offs; lia)|]. split; [leaf X2 ltac:(apply AGb; offs; lia)|]. split; [leaf X3 ltac:(apply AGb; offs; lia)|].
    split; [|split].
    - intros i e E. pose proof (X4 i e E) as L.
      assert (Z.of_nat i < Z.of_nat (length (ba_entries b))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L ltac:(apply AGb; unfold kQuarantineBatchCount in *; offs; lia).
    - pose proof class_size_24 as C24E. unfold batch_addr in *.
      apply mapped_T; [| right | | exact M]; unfold kQuarantineBatchBytes, kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
    - apply IH; [| exact BR]. intros b' Hb'. apply SUB. right. exact Hb'.
  Qed.

  Lemma quar_T : quarantine_repr_ LPA AL_pasan (a_pl A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_65; dand3 dR_65 as QT QG QR | pose proof (ar_quar _ _ _ _ _ R) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with (a_sb A) in *.
    split; [|split].
    - (first [ dand5 QT as X1 X2 X3 X4 BR | destruct QT as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      split; [leaf X1 by_thr|]. split; [leaf X2 by_thr|]. split; [leaf X3 by_thr|]. split; [leaf X4 by_thr|].
      apply batches_T; [intros b Hb; apply in_or_app; left; exact Hb| exact BR].
    - (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      split; [leaf X1 by_stat|]. split; [leaf X2 by_stat|]. split; [leaf X3 by_stat|]. split; [leaf X4 by_stat|].
      apply batches_T; [intros b Hb; apply in_or_app; right; exact Hb| exact BR].
    - intros e He. (first [ pose proof ((QR e He)) as dR_68; dand3 dR_68 as HR J MC | destruct (QR e He) as (HR & J & MC) ]). pose proof alloc_ceiling_val as CE.
      (first [ pose proof ((chunk_mapped_T (qe_chunk e) (qe_n e) ltac:(right; destruct e; exact He) MC)) as dR_69; dand4 dR_69 as MC' G1 G2 G3 | destruct (chunk_mapped_T (qe_chunk e) (qe_n e) ltac:(right; destruct e; exact He) MC) as (MC' & G1 & G2 & G3) ]).
      split; [|split; [|exact MC']].
      + apply hdr_T; [|exact HR]. intros a Ha. apply AGF. eapply af_quar; eauto.
      + leaf J ltac:(apply AGF; eapply af_quar; [exact He| right; lia]).
  Qed.

  Lemma sec_T : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v'.
  Proof.
    pose proof (ar_sec _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_facts A W)) as dR_70; dand13 dR_70 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa.
    (first [ dand3 Ppa as Ppa1 Ppa2 Ppa3 | destruct Ppa as (Ppa1 & Ppa2 & Ppa3) ]). apply app_facts in Ppa1.
    (first [ pose proof ((wfS A W)) as dR_72; dand4 dR_72 as _ LEN RES _ | destruct (wfS A W) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. unfold sec_repr_ in *. cbv zeta in *.
    (first [ dand7 C as X1 X2 J1 J2 J3 CH M | destruct C as (X1 & X2 & J1 & J2 & J3 & CH & M) ]).
    split; [leaf X1 by_stat|]. split; [leaf X2 by_stat|]. split; [leaf J1 by_stat|]. split; [leaf J2 by_stat|]. split; [leaf J3 by_stat|]. split.
    - intros i s E. destruct (CH i s E) as [X Y]. pose proof (nth_error_In _ _ E) as Hin.
      assert (Z.of_nat i < Z.of_nat (length (sr_chunks (a_sec A)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      split.
      + leaf X ltac:(apply AGpa; unfold a_pa; offs; lia).
      + eapply rw_cells_agree; [exact Y|]. rewrite sec_hdr_size. intros j Hj. apply AGF. eapply af_sechdr; [exact Hin|]. offs. lia.
    - apply mapped_T; [clear - Ppa1; lia| clear - Ppa1 RES LEN; kun; lia| clear - Ppa1 Ppa2 RES LEN CE; kun; lia| exact M].
  Qed.

  Lemma depot_T : depot_repr_ LPA AL_pasan (a_pl A) (a_depot A) v'.
  Proof.
    pose proof (ar_depot _ _ _ _ _ R) as C. unfold depot_repr_ in *. eapply depot_rep_agree; [exact C|].
    intros a Ha. apply AGF. apply af_depot. exact Ha.
  Qed.

  Lemma ia_T : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof.
    pose proof (ar_ia _ _ _ _ _ R) as C. unfold ia_repr_ in *. cbv zeta in *. destruct C as [C0 C]. split.
    - intros i Hi. pose proof (C0 i Hi) as L. unfold kDepotNodesL1 in Hi. leaf L by_stat.
    - destruct (a_ia_inited A); walk C by_stat.
  Qed.

  Lemma fsbase_T : fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof.
    pose proof (ar_fsbase _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fs A W)) as dR_74; dand3 dR_74 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]). unfold a_fs in FS1, FS2, FSM.
    unfold fs_base_ in *. cbv zeta in *. (first [ dand5 C as H0 H1 H2 M1 M2 | destruct C as (H0 & H1 & H2 & M1 & M2) ]).
    split; [|split; [leaf H1 ltac:(apply AGfs; unfold a_fs; offs; lia)| split; [leaf H2 ltac:(apply AGfs; unfold a_fs; offs; lia)| split]]].
    - intros k Hk. pose proof (H0 k Hk) as L. leaf L ltac:(apply AGfs; unfold a_fs; offs; lia).
    - apply app_facts in FS1. apply mapped_T; [lia| unfold kFakeStackBytes in *; lia| lia| exact M1].
    - pose proof (fs_shadow_strict A (sh (p_fs (a_pl A))) W ltac:(unfold a_fs, kFakeStackBytes; lia)) as X1.
      pose proof (fs_shadow_strict A (sh (p_fs (a_pl A)) + (kFakeStackBytes / 8 - 1)) W ltac:(unfold a_fs, kFakeStackBytes; lia)) as X2.
      unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in X1, X2.
      apply mapped_T; [lia| right; lia| lia| exact M2].
  Qed.

  Lemma fsptrs_T : forall g, (forall ff f, g !! ff = Some f -> a_fframes A !! ff = Some f) -> fs_ptrs_ LPA (a_fs A) (a_fhint A) g v'.
  Proof.
    intros g SUB ff f Hg. pose proof (SUB ff f Hg) as Hf. pose proof (ar_fsptrs _ _ _ _ _ R ff f Hf) as L.
    leaf L ltac:(apply AGF; eapply af_ptr; [exact Hf| lia]).
  Qed.

  Lemma maps_T : maps_repr_ AL_pasan (a_pl A) v'.
  Proof.
    (first [ pose proof ((ar_maps _ _ _ _ _ R)) as dR_76; dand4 dR_76 as M1 M2 M3 M4 | pose proof (ar_maps _ _ _ _ _ R) as (M1 & M2 & M3 & M4) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_facts A W)) as dR_77; dand14 dR_77 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
    (first [ pose proof ((sb_facts A W)) as dR_78; dand5 dR_78 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). unfold maps_repr_. unfold a_sb, a_b6, p_ri in *.
    cbn [al_image_lo al_image_hi AL_pasan] in M4 |- *.
    change (shadow_region 65536 (6332416 - 65536)) with (0x7fffa000, 0xbf400) in M4 |- *. cbn [fst snd] in M4 |- *.
    (first [ pose proof (stack_shadow_iv_facts) as dR_79; dand4 dR_79 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    kun.
    split; [apply mapped_T; [lia| right; lia| lia| exact M1]|]. split; [apply mapped_T; [lia| right; lia| lia| exact M2]|].
    split; [apply mapped_T; [lia| right; lia| lia| exact M3]| apply mapped_T; [lia| right; lia| lia| exact M4]].
  Qed.

  Lemma shadow_T : shadow_repr_ LPA (a_sb A) (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_80; dand6 dR_80 as S1 S2 S3 S4 S5 S6 | pose proof (ar_shadow _ _ _ _ _ R) as (S1 & S2 & S3 & S4 & S5 & S6) ]). (first [ pose proof ((sb_facts A W)) as dR_81; dand3 dR_81 as _ SBA _ | pose proof (sb_facts A W) as (_ & SBA & _) ]).
    (* [comment removed for export] *)
    assert (CHK : forall c k bs, 1 <= c <= 30 -> 0 <= k < carved_count A c -> Z.of_nat (length bs) = class_size c / 8 ->
                  bytes_at (cl_segs LPA) v (sh (chunk_addr (a_sb A) c k)) bs -> bytes_at (cl_segs LPA) v' (sh (chunk_addr (a_sb A) c k)) bs).
    { intros c k bs Hc Hk L B. eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply AGhs.
      (first [ pose proof ((carved_chunk_bounds A c k W Hc Hk)) as dR_82; dand4 dR_82 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W Hc Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in *.
      (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
      pose proof (class_size_mod32 c Hc) as CM.
      pose proof (sh_ceil_le (chunk_addr (a_sb A) c k) (class_size c) (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c))
        ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9]) Q10 ltac:(lia) ltac:(lia)) as [X Y].
      rewrite (div8_ceil_exact (class_size c) (mod0_down _ 32 8 (divide_wit 8 4) CM)) in Y.
      unfold heap_shadow, heap_shadow_. left. exists c. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with (a_sb A). lia. }
    (first [ pose proof ((wfR A W)) as dR_84; dand3 dR_84 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((wfC A W)) as dR_85; dand3 dR_85 as WC _ _ | destruct (wfC A W) as (WC & _ & _) ]). (first [ pose proof ((wfQ A W)) as dR_86; dand3 dR_86 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]). (first [ pose proof ((wfV A W)) as dR_87; dand3 dR_87 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]).
    assert (QWF : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> wf_qentry_ (a_reg A) (a_sec A) e).
    { intros e He. unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
      [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
      (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB e Heb). }
    assert (BWF : forall k, In k (batch_indices A) -> 0 <= k < carved_count A kQuarantineBatchClass).
    { intros k Hk. unfold batch_indices, batch_indices_ in Hk. apply in_map_iff in Hk as (b & <- & Hb).
      assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
      { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
      (first [ dand3 WB as _ K _ | destruct WB as (_ & K & _) ]). exact K. }
    split; [|split; [|split; [|split; [|split]]]].
    - intros c k Hc ST. apply CHK; [exact Hc| | unfold pshadow_free, fa8; rewrite repeat_length; pose proof (class_size_range c Hc); rewrite Z2Nat.id by (apply Z.div_pos; lia); reflexivity| exact (S1 c k Hc ST)].
      destruct ST as [F|[C|[E B]]].
      + (first [ pose proof ((WR c Hc)) as dR_90; dand10 dR_90 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F).
      + (first [ pose proof ((WC c ltac:(lia))) as dR_91; dand4 dR_91 as _ _ CR _ | destruct (WC c ltac:(lia)) as (_ & _ & CR & _) ]). exact (CR k C).
      + subst c. apply BWF. exact B.
    - intros u c k n Hl. (first [ pose proof ((V1 u _ Hl)) as dR_92; dand5 dR_92 as N U N2 Hc Hk | pose proof (V1 u _ Hl) as (N & U & N2 & Hc & Hk) ]). cbn [li_n li_chunk] in *.
      apply CHK; [rewrite Hc; apply class_of_range; lia| exact Hk| apply pshadow_live_length; [lia| exact Hc]| exact (S2 u c k n Hl)].
    - intros c k n He. (first [ pose proof ((QWF _ He)) as dR_93; dand4 dR_93 as N N2 Hc Hk | pose proof (QWF _ He) as (N & N2 & Hc & Hk) ]). cbn [qe_n qe_chunk] in *.
      apply CHK; [rewrite Hc; apply class_of_range; lia| exact Hk| apply pshadow_quar_length; [lia| exact Hc]| exact (S3 c k n He)].
    - intros c Hc. destruct (S4 c Hc) as [X Y]. pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in *.
      (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
      assert (RBM : region_beg (a_sb A) c mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact R9]).
      split.
      + eapply fill_at_agree; [exact X|]. intros i Hi. apply AGhs. unfold heap_shadow, heap_shadow_. left. exists c. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with (a_sb A).
        rewrite (sh_add _ _ RBM R11).
        pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) R10). pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) R11).
        assert ((rg_mapped_user (a_reg A c) - rg_allocated_user (a_reg A c)) / 8 = rg_mapped_user (a_reg A c) / 8 - rg_allocated_user (a_reg A c) / 8).
        { symmetry. apply (Z.div_unique_exact _ _ _); [lia|]. lia. } lia.
      + eapply fill_at_agree; [exact Y|]. intros i Hi. apply AGhs. unfold heap_shadow, heap_shadow_. right. left. exists c. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with (a_sb A). lia.
    - intros u mb n Hl. (first [ pose proof ((V1 u _ Hl)) as dR_95; dand5 dR_95 as N U N2 _ Hin | pose proof (V1 u _ Hl) as (N & U & N2 & _ & Hin) ]). cbn [li_n li_chunk] in *.
      eapply bytes_at_agree_gen; [exact (S5 u mb n Hl)|]. rewrite sshadow_live_length by lia. intros i Hi. apply AGhs.
      unfold heap_shadow, heap_shadow_. right. right. exists (CS mb n). split; [exact Hin|]. cbn [cs_map cs_n]. lia.
    - intros mb n0 n He. pose proof (S6 mb n0 n He) as B. (first [ pose proof ((QWF _ He)) as dR_96; dand4 dR_96 as N N2 E0 Hin | pose proof (QWF _ He) as (N & N2 & E0 & Hin) ]). cbn [qe_n qe_chunk] in *. subst n0.
      eapply bytes_at_agree_gen; [exact B|]. rewrite sshadow_quar_length by lia. intros i Hi. apply AGhs.
      unfold heap_shadow, heap_shadow_. right. right. exists (CS mb n). split; [exact Hin|]. cbn [cs_map cs_n]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arepr_T : forall g, (forall ff f, g !! ff = Some f -> a_fframes A !! ff = Some f) ->
    fs_flags_ LPA (a_fs A) (a_fhint A) g v' -> arepr LPA AL_pasan [] (set_fframes A g) v'.
  Proof.
    intros g SUB FL. constructor; cbn [a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes set_fframes].
    - exact consts_T. - exact locks_T. - exact regions_T. - exact cache_T. - exact live_T. - exact quar_T. - exact sec_T.
    - exact depot_T. - exact ia_T. - exact fsbase_T. - exact (fsptrs_T g SUB). - exact FL. - exact maps_T. - exact shadow_T.
  Qed.
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint del_all (rel : list Z) (g : gmap Z fframe) : gmap Z fframe :=
  match rel with [] => g | ff :: rel' => del_all rel' (delete ff g) end.
Lemma fold_delete_del_all : forall rel g, fold_left (fun g ff => delete ff g) rel g = del_all rel g.
Proof. induction rel as [|ff rel IH]; intros g; cbn; [reflexivity| apply IH]. Qed.
Lemma del_all_notin : forall rel g x, ~ In x rel -> del_all rel g !! x = g !! x.
Proof.
  induction rel as [|ff rel IH]; intros g x H; cbn; [reflexivity|].
  rewrite IH by (intros I; apply H; right; exact I). apply lookup_delete_ne. intros E. apply H. left. congruence.
Qed.
Lemma del_all_none : forall rel g x, g !! x = None -> del_all rel g !! x = None.
Proof.
  induction rel as [|ff rel IH]; intros g x H; cbn; [exact H|]. apply IH.
  destruct (Z.eq_dec ff x) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by exact NE; exact H].
Qed.
Lemma del_all_in : forall rel g x, In x rel -> del_all rel g !! x = None.
Proof.
  induction rel as [|ff rel IH]; intros g x H; [destruct H|]. cbn. destruct H as [E|H].
  - subst ff. apply del_all_none. apply lookup_delete_eq.
  - apply IH. exact H.
Qed.
Lemma del_all_sub : forall rel g x f, del_all rel g !! x = Some f -> g !! x = Some f /\ ~ In x rel.
Proof.
  intros rel g x f H. destruct (in_dec Z.eq_dec x rel) as [I|NI].
  - rewrite (del_all_in rel g x I) in H. discriminate.
  - rewrite (del_all_notin rel g x NI) in H. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem asI_frame : forall A (rel : list Z) m m' md md',
  pa_ainv A m md ->
  (forall ff, In ff rel -> exists k age, as_fframe A ff = Some (k, age)) -> NoDup rel ->
  let A' := fold_left as_release rel A in
  let v := aview_of (pa_hull A) m in let v' := aview_of (pa_hull A) m' in
  (forall a : word, hidc (pa_hull A) a = true -> m' a = m a) ->
  (forall a, pa_owned A a ->
      v' (wz a) = v (wz a)
      \/ (exists ff k age fa, In ff rel /\ as_fframe A ff = Some (k, age) /\ a = fa /\
            bytes_at (cl_segs LPA) v (ff + fsize k - 8) (le8 (wz fa)) /\ v' (wz a) = Some (Z_to_bv 8 0))) ->
  (forall ff k age fa, In ff rel -> as_fframe A ff = Some (k, age) ->
      bytes_at (cl_segs LPA) v (ff + fsize k - 8) (le8 (wz fa)) -> v' (wz fa) = Some (Z_to_bv 8 0)) ->
  (forall a, cl_shared LPA a -> v' (wz a) = v (wz a)) ->
  (forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v (wz a) <> None -> v' (wz a) <> None) ->
  (forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v' (wz a) <> None -> v (wz a) <> None) ->
  MInv (pa_hull A) (pa_lhull A) (pa_eager A) md' -> same_but_materialized md md' ->   (* [comment removed for export] *)
  pa_ainv A' m' md'.
Proof.
  intros A rel m m' md md' AI REL ND A' v v' HID CH FZ SH NN NN2 MI SBM.
  pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE. pose proof (ai_repr _ _ _ _ _ _ _ AI) as R. fold v in R.
  (first [ pose proof ((place_fs A W)) as dR_97; dand3 dR_97 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]). (first [ pose proof ((app_facts _ _ FS1)) as dR_98; dand5 dR_98 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
  subst A'. rewrite fold_release, fold_delete_del_all. set (g := del_all rel (a_fframes A)).
  assert (SUB : forall ff f, g !! ff = Some f -> a_fframes A !! ff = Some f /\ ~ In ff rel) by (intros ff f H; apply del_all_sub; exact H).
  (* [comment removed for export] *)
  assert (PTR : forall ff f fa, a_fframes A !! ff = Some f -> bytes_at (cl_segs LPA) v (ff + fsize (ff_class f) - 8) (le8 (wz fa)) -> 0 <= fa < 2^64 ->
                fa = fflag_addr (a_fs A) (ff_class f) (ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f))).
  { intros ff f fa Hf B Hfa. pose proof (ar_fsptrs _ _ _ _ _ R ff f Hf) as B2. unfold u64_at, saved_flag_ptr in B2.
    pose proof (bytes_at_func _ v _ _ _ B B2 ltac:(rewrite !length_le8; reflexivity)) as LE. apply le8_wz_inj in LE.
    pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. (first [ dand4 FF as K _ AG _ | destruct FF as (K & _ & AG & _) ]).
    pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
    pose proof (fflag_addr_range (a_fs A) (ff_class f) _ K PR). unfold a_fs in *.
    apply wz_inj in LE; [exact LE| exact Hfa| clear -H G1 FS2 CE; kun; lia]. }
  (* [comment removed for export] *)
  assert (AGF : forall a, afoot LPA AL_pasan A a -> v' (wz a) = v (wz a)).
  { intros a FT. destruct (afoot_owned_shared A m md a AI FT) as [OW|SHD]; [|apply SH; exact SHD].
    destruct (CH a OW) as [E|(ff & k & age & fa & Hin & HF & -> & B & Z0)]; [exact E|]. exfalso.
    unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as <- <-.
    pose proof (owned_lt64 A m md fa AI OW) as Hfa. pose proof (PTR ff f fa Hf B Hfa) as E.
    apply (afoot_not_flags A m md fa AI FT). unfold flags_area.
    pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. destruct FF as (K & _).
    pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
    pose proof (fflag_addr_range (a_fs A) (ff_class f) _ K PR). rewrite E. lia. }
  (* [comment removed for export] *)
  assert (FL : fs_flags_ LPA (a_fs A) (a_fhint A) g v').
  { intros k pos Hk Hpos. (first [ pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_100; dex1 dR_100 as b; destruct dR_100 as [U8 CASES] | pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_100; dand3 dR_100 as b U8 CASES | destruct (ar_fsflags _ _ _ _ _ R k pos Hk Hpos) as (b & U8 & CASES) ]).
    set (F := fflag_addr (a_fs A) k pos) in *.
    pose proof (fflag_addr_range (a_fs A) k pos Hk Hpos) as FR. fold F in FR.
    (first [ pose proof ((bm_nth_fixed A)) as dR_101; dand8 dR_101 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    assert (OWN : pa_owned A F).
    { eapply (owned_rt A F (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia| |].
      - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia].
      - intros LF. pose proof (live_frame_zone A F W LF). unfold kFakeFlagsOffset, kFakeFramesOffset in *. lia. }
    assert (F64 : 0 <= F < 2^64) by (clear - FR G1 FS2 CE; unfold a_fs in *; kun; lia).
    destruct (classic (exists ff f, In ff rel /\ a_fframes A !! ff = Some f /\ ff_class f = k /\ ff_pos (a_fhint A k) k (ff_age f) = pos)) as [(ff & f & Hin & Hf & Hc & Hp)|NO].
    - (* [comment removed for export] *)
      exists 0. split.
      + assert (Z0 : v' (wz F) = Some (Z_to_bv 8 0)).
        { apply (FZ ff k (ff_age f) F Hin); [unfold as_fframe, as_fframe_; rewrite Hf; cbn; rewrite Hc; reflexivity|].
          pose proof (ar_fsptrs _ _ _ _ _ R ff f Hf) as B2. unfold u64_at, saved_flag_ptr in B2. rewrite Hc in B2. unfold F. rewrite <- Hp. exact B2. }
        split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia. cbn [nth_error]. unfold mrd, wa. rewrite Z.add_0_r. rewrite Z0. reflexivity.
      + right. split; [reflexivity|]. ((first [ intro dR_107; dex2 dR_107 as ff2 f2; dand3 dR_107 as Hg2 Hc2 Hp2 | intro dR_107; dand5 dR_107 as ff2 f2 Hg2 Hc2 Hp2 | intros (ff2 & f2 & Hg2 & Hc2 & Hp2) ])). destruct (SUB ff2 f2 Hg2) as [Hf2 NI2].
        assert (NE : ff <> ff2) by (intros ->; exact (NI2 Hin)).
        (first [ pose proof ((wfF A W)) as dR_102; dand3 dR_102 as F1 _ F3 | destruct (wfF A W) as (F1 & _ & F3) ]). apply (F3 ff ff2 f f2 Hf Hf2 NE ltac:(congruence)).
        (first [ pose proof ((F1 ff f Hf)) as dR_103; dand3 dR_103 as K1 _ A1 | destruct (F1 ff f Hf) as (K1 & _ & A1) ]). (first [ pose proof ((F1 ff2 f2 Hf2)) as dR_104; dand3 dR_104 as K2 _ A2 | destruct (F1 ff2 f2 Hf2) as (K2 & _ & A2) ]). cbv zeta in *.
        apply (ff_pos_inj (a_fhint A k) k); [exact Hk| rewrite <- Hc; exact A1| rewrite <- Hc2; exact A2| rewrite <- Hc at 2; rewrite <- Hc2 at 3]. 
        rewrite Hc, Hc2. rewrite Hp, Hp2. reflexivity.
    - (* [comment removed for export] *)
      assert (EQ : v' (wz F) = v (wz F)).
      { destruct (CH F OWN) as [E|(ff & k2 & age2 & fa & Hin & HF & EF & B & Z0)]; [exact E|]. exfalso.
        unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as <- <-.
        rewrite <- EF in B. pose proof (PTR ff f F Hf B F64) as E.
        pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. destruct FF as (K & _).
        pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
        unfold F in E. destruct (fflag_addr_inj _ _ _ _ _ Hk K Hpos PR E) as [EK EP].
        apply NO. exists ff, f. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact Hf| congruence| rewrite EK; symmetry; exact EP]. }
      exists b. split; [eapply u8_at_agree; [exact U8| exact EQ]|].
      destruct CASES as [[-> (ff & f & Hf & Hc & Hp)]|[-> NSL]].
      + left. split; [reflexivity|]. exists ff, f. split; [|split; assumption].
        unfold g. rewrite del_all_notin; [exact Hf|]. intros Hin. apply NO. exists ff, f. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + right. split; [reflexivity|]. ((first [ intro dR_108; dex2 dR_108 as ff f; dand3 dR_108 as Hg Hc Hp | intro dR_108; dand5 dR_108 as ff f Hg Hc Hp | intros (ff & f & Hg & Hc & Hp) ])). apply NSL. exists ff, f. split; [exact (proj1 (SUB ff f Hg))| split; assumption]. }
  pose proof (same_but_materialized_frame md md' SBM) as SF. (first [ dand18 SF as _ VMM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HALT _ | destruct SF as (_ & VMM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HALT & _) ]).
  constructor.
  - (* [comment removed for export] *) destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN]. constructor; cbn [a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid set_fframes]; try assumption.
    (first [ dand3 wF as F1 F2 F3 | destruct wF as (F1 & F2 & F3) ]). split; [|split; [exact F2|]].
    + intros ff f Hg. apply F1. exact (proj1 (SUB ff f Hg)).
    + intros ff ff' f f' Hg Hg' NE. apply (F3 ff ff' f f'); [exact (proj1 (SUB _ _ Hg))| exact (proj1 (SUB _ _ Hg'))| exact NE].
  - (* [comment removed for export] *) change (aview_of (ahull_of pa_image_ivs AL_pasan (set_fframes A g)) m') with v'.
    apply (arepr_T A m m' md AI AGF NN g (fun ff f H => proj1 (SUB ff f H)) FL).
  - (* [comment removed for export] *)
    pose proof (ai_hidden _ _ _ _ _ _ _ AI) as MH.
    assert (XFER : forall a, 0x60a000 <= a -> a < 2^64 -> m (wz a) <> None -> m' (wz a) <> None).
    { intros a H1 H2 H3. destruct (hidc (pa_hull A) (wz a)) eqn:HV.
      - rewrite (HID _ HV). exact H3.
      - assert (VV : v (wz a) = m (wz a)) by (unfold v, aview_of; apply view_visible; exact HV).
        assert (VV' : v' (wz a) = m' (wz a)) by (unfold v', aview_of; apply view_visible; exact HV).
        rewrite <- VV'. apply NN; [lia| unfold in_image; cbn [cl_image_lo cl_image_hi LPA]; lia| rewrite VV; exact H3]. }
    cbn [a_pl a_reg a_sec set_fframes]. unfold hidden_repr in MH. destruct MH as [MH1 MH2]. split.
    + (* [comment removed for export] *)
      intros z GZ. destruct (MH1 z GZ) as [P1 P2].
      assert (EQ : m' (wz z) = m (wz z)).
      { destruct (hidc (pa_hull A) (wz z)) eqn:HV; [exact (HID _ HV)|].
        assert (VV : v (wz z) = m (wz z)) by (unfold v, aview_of; apply view_visible; exact HV).
        assert (VV' : v' (wz z) = m' (wz z)) by (unfold v', aview_of; apply view_visible; exact HV).
        rewrite <- VV, <- VV'.
        assert (OW : pa_owned A z) by (left; right; right; exact GZ).
        destruct (CH z OW) as [E|(ff & k & age & fa & Hin & HF & -> & B & Z0)]; [exact E|]. exfalso.
        unfold as_fframe, as_fframe_ in HF. destruct (a_fframes A !! ff) as [f|] eqn:Hf; [|discriminate]. cbn in HF. injection HF as <- <-.
        pose proof (owned_lt64 A m md fa AI OW) as Hfa. pose proof (PTR ff f fa Hf B Hfa) as E.
        pose proof (frame_facts A m md ff f AI Hf) as FF. cbv zeta in FF. destruct FF as (K & _).
        pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
        pose proof (fflag_addr_range (a_fs A) (ff_class f) _ K PR). unfold a_fs in *.
        apply (app_not_ghost' (a_pl A) fa); [clear -H E G1 G5 FS2 CE; kun; lia| exact GZ]. }
      rewrite EQ. exact (conj P1 P2).
    + intros z Hz NB. apply XFER; unfold kLowShadowMapBeg in *; try lia. apply (MH2 z); [unfold kLowShadowMapBeg; lia| exact NB].
  - (* [comment removed for export] *) cbn [a_pl set_fframes]. exact (ai_extra _ _ _ _ _ _ _ AI).
  - (* [comment removed for export] *) cbn [a_pl a_reg a_sec set_fframes]. exact (aledger_sbm _ _ _ _ md md' SBM (ai_ledger _ _ _ _ _ _ _ AI)).
  - (* [comment removed for export] *) exact MI.
  - rewrite HALT. exact (ai_halted _ _ _ _ _ _ _ AI).
  - (* [comment removed for export] *) cbn [a_pl a_sec set_fframes]. rewrite (same_but_materialized_vmmaps _ _ SBM). exact (ai_cover _ _ _ _ _ _ _ AI).
  - (* [comment removed for export] *) rewrite (same_but_materialized_vmmaps _ _ SBM). exact (ai_ceil _ _ _ _ _ _ _ AI).
Qed.

End Pasan.
