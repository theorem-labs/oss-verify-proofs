(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQPart ATransp ATranspR AFreeRS AFreeRT AFreeRI AFreeRK2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section RU.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Definition same_ext (reg reg' : Z -> region) : Prop :=
    forall c, rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c).

  Lemma same_ext_classes_regions : forall sb reg reg' m, same_ext reg reg' -> classes_regions_ sb reg' m = classes_regions_ sb reg m.
  Proof.
    intros sb reg reg' m E. induction m as [|m IH]; [reflexivity|]. cbn [classes_regions_]. rewrite IH. f_equal.
    unfold class_regions_. destruct (E (Z.of_nat (S m))) as [E1 E2]. rewrite E1, E2. reflexivity.
  Qed.
  Lemma same_ext_lclasses_regions : forall sb reg reg' m, same_ext reg reg' -> lclasses_regions_ sb reg' m = lclasses_regions_ sb reg m.   (* [comment removed for export] *)
  Proof.
    intros sb reg reg' m E. induction m as [|m IH]; [reflexivity|]. cbn [lclasses_regions_]. rewrite IH. f_equal.
    unfold lclass_regions_. destruct (E (Z.of_nat (S m))) as [E1 E2]. rewrite E1, E2. reflexivity.
  Qed.
  Lemma same_ext_classes_eager : forall reg reg' m, same_ext reg reg' -> classes_eager_ reg' m = classes_eager_ reg m.
  Proof.
    intros reg reg' m E. induction m as [|m IH]; [reflexivity|]. cbn [classes_eager_]. destruct (E (Z.of_nat (S m))) as [E1 E2]. rewrite IH, E1, E2. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Variables (A : AState) (reg' : Z -> region) (cache' : Z -> pcache) (limbo' : list batch).
  Let A' := mkA (a_pl A) reg' (a_cache_inited A) cache' (a_livemap A) [] (a_qglobal A) (a_sec A) (a_depot A) (a_fhint A) (a_fframes A)
                (a_ia_inited A) (a_oom A) (a_tiny A) limbo' (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
  Hypothesis EXT : same_ext (a_reg A) reg'.

  Lemma su_hull : pa_hull A' = pa_hull A.
  Proof. unfold pa_hull, ahull_of, ahull_of_, aregions_. subst A'. cbn [a_pl a_reg a_sec a_deadsh]. rewrite (same_ext_classes_regions _ _ _ 31 EXT). reflexivity. Qed.
  Lemma su_lhull : pa_lhull A' = pa_lhull A.   (* [comment removed for export] *)
  Proof. unfold pa_lhull, alhull_of, alhull_of_, alregions_. subst A'. cbn [a_pl a_reg a_sec a_deadsh]. rewrite (same_ext_lclasses_regions _ _ _ 31 EXT). reflexivity. Qed.
  Lemma su_eager : pa_eager A' = pa_eager A.
  Proof. unfold pa_eager, aeager_of, aeager_of_. subst A'. cbn [a_pl a_reg a_sec]. rewrite (same_ext_classes_eager _ _ 31 EXT). reflexivity. Qed.
  Lemma su_owned : forall a, pa_owned A' a <-> pa_owned A a.
  Proof. intros a. apply owned_iff_ext; subst A'; try reflexivity. intros c _. exact (EXT c). Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma su_hidden : forall (m : mem) (v' : mem),
    hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    (forall z, ghost_hs_ (a_pl A) z -> hidc (pa_hull A) (wz z) = false -> aview_of (pa_hull A) m (wz z) <> None -> v' (wz z) <> None) ->
    (forall z, ghost_hs_ (a_pl A) z -> hidc (pa_hull A) (wz z) = false -> ~ heap_shadow A z -> v' (wz z) = aview_of (pa_hull A) m (wz z)) ->
    (forall z, kLowShadowMapBeg <= z < kLowShadowMapBeg + 0x10000000 -> hidc (pa_hull A) (wz z) = false -> aview_of (pa_hull A) m (wz z) <> None -> v' (wz z) <> None) ->
    hidden_repr (a_pl A') (a_reg A') (a_sec A') (munrestrict (hidc (pa_hull A)) m v').
  Proof.
    intros m v' [H1 H2] NNg AGg NNl. subst A'. cbn [a_pl a_reg a_sec]. unfold hidden_repr. split.
    - intros z Gz. destruct (H1 z Gz) as [P1 P2]. unfold munrestrict. destruct (hidc (pa_hull A) (wz z)) eqn:Hc.
      + split; [exact P1|]. intros NH. apply P2. intros HS. apply NH. apply (heap_shadow_ext (p_sb (a_pl A)) (a_reg A) reg' (a_sec A) z); [intros c _; exact (EXT c)| exact HS].
      + assert (VZ : aview_of (pa_hull A) m (wz z) = m (wz z)) by (unfold aview_of, mrestrict; rewrite Hc; reflexivity).
        split; [apply (NNg z Gz Hc); rewrite VZ; exact P1|].
        intros NH. assert (NH0 : ~ heap_shadow A z).
        { intros HS. apply NH. apply (heap_shadow_ext (p_sb (a_pl A)) (a_reg A) reg' (a_sec A) z); [intros c _; exact (EXT c)| exact HS]. }
        rewrite (AGg z Gz Hc NH0), VZ. exact (P2 NH0).
    - intros z Hz NV. unfold munrestrict. destruct (hidc (pa_hull A) (wz z)) eqn:Hc; [exact (H2 z Hz NV)|].
      apply (NNl z Hz Hc). unfold aview_of, mrestrict. rewrite Hc. exact (H2 z Hz NV).
  Qed.

  (* [comment removed for export] *)
  Lemma su_virgin : forall c0 c, a_reg A c0 <> region_zero ->
    (forall c', c' <> c0 -> reg' c' = a_reg A c') -> (forall c', c' <> c0 -> cache' c' = a_cache A c') ->
    a_virgin A c -> a_virgin A' c.
  Proof.
    intros c0 c NZ RO CO [R0 K0]. subst A'. unfold a_virgin. cbn [a_reg a_cache].
    destruct (Z.eq_dec c c0) as [->|NE]; [exfalso; exact (NZ R0)|]. rewrite (RO c NE), (CO c NE). exact (conj R0 K0).
  Qed.
End RU.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keep.
Context {Clg : Ceiling}.
  Variables (A : AState) (v v' : mem) (held : list Z).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  Hypothesis AGC : forall a, 0 <= a < alloc_ceiling -> v' (wz a) = v (wz a).
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v' (wz a) <> None.
  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                          kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve in *.

  Lemma keep_img : forall a, 0x10000 <= a < 0x60a000 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. pose proof alloc_ceiling_val. apply AGC. clear -Ha H. lia. Qed.
  Lemma keep_chunk : forall ch a, carved A ch -> chunk_lo (a_sb A) ch <= a < chunk_hi (a_sb A) ch -> v' (wz a) = v (wz a).
  Proof. intros ch a CV Ha. (first [ pose proof ((carved_range A v held AR ch CV)) as dR_1; dand3 dR_1 as R1 R2 _ | pose proof (carved_range A v held AR ch CV) as (R1 & R2 & _) ]). apply AGC. clear -Ha R1 R2. lia. Qed.
  Lemma keep_thr : forall a, p_thr (a_pl A) <= a < p_thr (a_pl A) + 4096 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. pose proof (place_factsT A W) as ((P1 & P2 & _) & _). pose proof (app_facts _ _ P1) as (X & _). apply AGC. clear -Ha P2 X. lia. Qed.

  Theorem arepr_keep : @arepr _ DepotRepL LPA AL_pasan held A v'.
  Proof.
    pose proof alloc_ceiling_val as CE. pose proof (proj2 AR) as R.
    (first [ pose proof ((place_factsT A W)) as dR_2; dand13 dR_2 as _ Pctx Pn0 Pf0 Pfs _ _ _ _ _ Pdt Ppa _ | pose proof (place_factsT A W) as (_ & Pctx & Pn0 & Pf0 & Pfs & _ & _ & _ & _ & _ & Pdt & Ppa & _) ]). cbv zeta in *.
    (first [ dand3 Pctx as Pctx PctxC _ | destruct Pctx as (Pctx & PctxC & _) ]). (first [ dand3 Pn0 as Pn0 Pn0C _ | destruct Pn0 as (Pn0 & Pn0C & _) ]). (first [ dand3 Pf0 as Pf0 Pf0C _ | destruct Pf0 as (Pf0 & Pf0C & _) ]).
    (first [ dand3 Pfs as Pfs PfsC _ | destruct Pfs as (Pfs & PfsC & _) ]). (first [ dand3 Pdt as Pdt PdtC _ | destruct Pdt as (Pdt & PdtC & _) ]). (first [ dand3 Ppa as Ppa PpaC _ | destruct Ppa as (Ppa & PpaC & _) ]).
    apply app_facts in Pctx. destruct Pctx as (Pctx & _). apply app_facts in Pn0. destruct Pn0 as (Pn0 & _). apply app_facts in Pf0. destruct Pf0 as (Pf0 & _).
    apply app_facts in Pfs. destruct Pfs as (Pfs & _). apply app_facts in Pdt. destruct Pdt as (Pdt & _). apply app_facts in Ppa. destruct Ppa as (Ppa & _).
    (first [ pose proof ((sb_factsT A W)) as dR_9; dand5 dR_9 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]).
    constructor.
    - apply (consts_P A v v' held AR).
      + intros cst a Hin Ha. cbn [cl_consts LPA] in Hin. destruct (pa_consts_where cst a Hin Ha) as [Sh|[IS|St]].
        * pose proof (asI_shared_where a Sh) as X. cbn [cl_rw_lo cl_image_hi LPA] in X. apply keep_img. lia.
        * apply AGC. unfold pa_image_shadow, sh in IS. kung_all. lia.
        * cbn [cl_static LPA] in St. unfold pa_static in St. apply keep_img. lia.
      + intros a Sh. pose proof (asI_shared_where a Sh) as X. cbn [cl_rw_lo cl_image_hi LPA] in X. apply keep_img. lia.
      + intros a H. apply keep_img. unfold cfoot_stat in H. cbn [al_instance al_kHighMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache al_may_return_null
          al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in H.
        unfold off_primary_reserved_base, off_primary_reserved_size, off_SpaceBeg, off_release_interval, off_RegionInfo_ptr, off_PremappedHeap, off_sec_page_size,
          off_sec_chunks, off_sec_ptr_array_base, off_sec_ptr_array_size, off_q_max_size, off_q_min_size, off_q_max_cache_size, off_max_user_malloc,
          off_min_redzone, off_max_redzone, off_alloc_dealloc_mismatch in H. lia.
      + intros a H. unfold cfoot_thr, off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in H. apply keep_thr. lia.
      + intros a H. unfold cfoot_misc in H. cbn [cl_tp LPA] in H. rewrite unsigned_lit in H by (clear; lia).
        destruct H as [H|[H|[H|[H|[H|H]]]]]; apply AGC; clear -H Pctx PctxC Pdt PdtC CE; lia.
    - apply (locks_P A v v' held AR). intros a H. unfold lfoot in H. change (al_internal_alloc_inited AL_pasan) with 0x144e48 in H. change (al_instance AL_pasan) with 0xb1d58 in H.
      unfold p_ri, kRegionInfoSize, off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex in H. apply AGC. clear -H SCE HB6 RSB CE. unfold a_sb, a_b6 in *. kung_all. lia.
    - intros c Hc. apply (region_P A v v' held AR NN c Hc). intros a H. unfold rfoot in H.
      (first [ pose proof ((region_piece_boundsT A c W Hc)) as dR_10; dand9 dR_10 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 _ | pose proof (region_piece_boundsT A c W Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _) ]). cbv zeta in *.
      unfold region_info_addr, free_array_beg, kRegionInfoSize in H. unfold a_sb in *. apply AGC. clear -H Hc Q1 Q5 Q6 Q7 Q8. kung_all. lia.
    - apply (cache_P A v v' held AR NN (a_cache A)). intros c' Hc'. apply (cache_line_P A v v' held AR NN (a_cache A) c' Hc' eq_refl).
      intros a Ha. unfold off_th_per_class, off_th_alloc_cache, kPerClassSize in Ha. apply keep_thr. lia.
    - apply (live_sub_P A v v' held AR NN (a_livemap A)); [intros u li Hl; exact Hl|].
      intros u li a Hl Ha. exact (keep_chunk _ a (known_carved A v held AR _ _ (known_live A v held AR u li Hl)) Ha).
    - apply (quar_P A v v' held AR NN).
      + intros a Ha. unfold off_th_qcache in Ha. apply keep_thr. lia.
      + intros a Ha. apply keep_img. change (al_instance AL_pasan) with 0xb1d58 in Ha. unfold off_q_cache_list_size in Ha. lia.
      + intros b a Hb Ha. (first [ pose proof ((batch_range A v held AR b (b_in_big A b Hb))) as dR_11; dand3 dR_11 as R1 R2 _ | pose proof (batch_range A v held AR b (b_in_big A b Hb)) as (R1 & R2 & _) ]). apply AGC. clear -Ha R1 R2. unfold kQuarantineBatchBytes in *. kung_all. lia.
      + intros e a He Ha. exact (keep_chunk _ a (known_carved A v held AR _ _ (known_quar A v held AR e (q_in_big A e He))) Ha).
    - (first [ pose proof ((wtS A W)) as dR_12; dand4 dR_12 as _ LEN RES _ | destruct (wtS A W) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. apply (sec_P A v v' held AR NN).
      + intros a H. apply keep_img. unfold sfoot_stat in H. change (al_instance AL_pasan) with 0xb1d58 in H.
        unfold off_sec_n_reserved, off_sec_n_chunks, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_global_stats in H. lia.
      + intros a Ha. apply AGC. clear -Ha LEN RES Ppa PpaC. kung_all. lia.
      + intros sc a Hin Ha. (first [ pose proof ((sec_chunk_boundsT A sc W Hin)) as dR_13; dand5 dR_13 as _ _ SB3 SB4 SB5 | pose proof (sec_chunk_boundsT A sc W Hin) as (_ & _ & SB3 & SB4 & SB5) ]). pose proof (app_facts _ _ SB3) as (F1 & _).
        pose proof (needed_size_ge (cs_n sc)) as N1. pose proof (rz_size_range (cs_n sc)) as N2. unfold needed_size2 in SB5.
        apply AGC. clear -Ha SB4 SB5 F1 N1 N2. destruct (from_primary (cs_n sc)); unfold kSecondaryHeaderSize, kPageSize in *; lia.
    - apply (depot_P A v' (a_depot A) v); [exact (ar_depot _ _ _ _ _ R)|].
      intros a H. unfold depot_foot in H. cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in H. unfold kDepotNodesL1 in H.
      destruct H as [H|[H|H]]; [apply keep_img; clear -H; lia| apply AGC; clear -H Pn0 Pn0C; kung_all; lia| apply AGC; clear -H Pf0 Pf0C; kung_all; lia].
    - apply (ia_P A v v' held AR). intros a H. apply keep_img. unfold iafoot in H.
      cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in H. clear -H. lia.
    - apply (fsbase_P A v v' held AR NN). intros a Ha. apply AGC. clear -Ha Pfs PfsC. unfold a_fs, kFakeFlagsOffset, kFakeStackBytes in *. lia.
    - apply (fsptrs_P A v v' held AR). intros a Ha. apply AGC. clear -Ha Pfs PfsC. unfold a_fs, kFakeFramesOffset, kFakeStackBytes in *. lia.
    - apply (fsflags_P A v v' held AR). intros a Ha. apply AGC. clear -Ha Pfs PfsC. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia.
    - exact (maps_P A v v' held AR NN).
    - apply (shadow_P0 A v v' held AR). intros z Hz. pose proof (heap_shadow_rangeT A z W Hz) as X. unfold in_shadow_maps in X. apply AGC. clear -X CE. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma keep_sh : forall lo hi z, 0 <= lo -> hi <= alloc_ceiling -> sh lo <= z < sh lo + (hi - lo) / 8 + 1 -> v' (wz z) = v (wz z).
  Proof. intros lo hi z H0 H1 Hz. pose proof alloc_ceiling_val as CE. apply AGC. unfold sh in Hz. clear -H0 H1 Hz CE. kung_all. lia. Qed.

  (* [comment removed for export] *)
  Lemma lentry_keep : forall e, In e (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) -> lentry_cells (a_sb A) v e -> lentry_cells (a_sb A) v' e.
  Proof.
    (intros e He; (first [ intro dR_18; dand4 dR_18 as HR J MC SH | intros (HR & J & MC & SH) ])). pose proof alloc_ceiling_val as CE.
    pose proof (known_quar A v held AR e He) as CL. pose proof (known_range A v held AR _ _ CL) as RNG.
    assert (AG : forall a, chunk_lo (a_sb A) (qe_chunk e) <= a < chunk_hi (a_sb A) (qe_chunk e) -> v' (wz a) = v (wz a)) by (intros a Ha; apply AGC; clear -Ha RNG; lia).
    pose proof (user_in A _ _ CL) as UI. pose proof (qentry_wf A v held AR _ He) as [N0 _].
    split; [|split; [|split]].
    - apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply AG. apply (hdr_foot_in A _ (qe_n e)); [exact CL| left; exact Ha].
    - apply (junk_N v v' NN); [clear -UI RNG; lia| right; clear -UI RNG N0; lia| exact J].
    - apply (mapped_N v v' NN); [clear -RNG; lia| right; clear -RNG; lia| clear -RNG CE; lia| exact MC].
    - destruct (qe_chunk e) as [[c'' k'']|[mb n1]] eqn:EC.
      + eapply bytes_at_xfer; [exact SH|]. intros z Hz. unfold known in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]).
        rewrite (pshadow_quar_length c'' (qe_n e)) in Hz by (clear -Hn Hcl; lia). cbn [chunk_lo chunk_hi alloc_beg] in RNG.
        apply (keep_sh (chunk_addr (a_sb A) c'' k'') (chunk_addr (a_sb A) c'' k'' + class_size c'')); clear -RNG Hz; [lia|lia|lia].
      + eapply bytes_at_xfer; [exact SH|]. intros z Hz. unfold known in CL. (first [ dand3 CL as Hin Hn En | destruct CL as (Hin & Hn & En) ]). subst n1.
        rewrite (sshadow_quar_length (qe_n e)) in Hz by (clear -Hn; lia). cbn [chunk_lo chunk_hi cs_map cs_n] in RNG.
        apply (keep_sh mb (mb + map_size (qe_n e))); clear -RNG Hz; [lia|lia|lia].
  Qed.

  Lemma lbatch_keep : forall b es (j : nat) sz, In b (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)) -> Z.of_nat (length es) <= kQuarantineBatchCount ->
    let ba := batch_addr (a_sb A) b in
    lbatch_cells (a_sb A) v ba es j sz -> lbatch_cells (a_sb A) v' ba es j sz /\
    (bytes_at rsegs v (sh ba) (pshadow_free kQuarantineBatchClass) -> bytes_at rsegs v' (sh ba) (pshadow_free kQuarantineBatchClass)).
  Proof.
    intros b es j sz Hb LEN. cbv zeta. ((first [ intro dR_19; dand3 dR_19 as SL SZ MP | intros (SL & SZ & MP) ])). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((batch_range A v held AR b Hb)) as dR_16; dand3 dR_16 as R1 R2 _ | pose proof (batch_range A v held AR b Hb) as (R1 & R2 & _) ]).
    assert (AG : forall a, batch_addr (a_sb A) b <= a < batch_addr (a_sb A) b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)) by (intros a Ha; apply AGC; clear -Ha R1 R2; kung_all; lia).
    split; [split; [|split]|].
    - intros i e Hi He. eapply u64_at_agree; [exact (SL i e Hi He)|]. intros q Hq. apply AG.
      pose proof (nth_error_Some_lt _ _ _ He) as IL. unfold off_qb_batch, kQuarantineBatchBytes, kQuarantineBatchCount in *. clear -Hq IL LEN. lia.
    - eapply u64_at_agree; [exact SZ|]. intros q Hq. apply AG. unfold off_qb_size, kQuarantineBatchBytes in *. clear -Hq. lia.
    - unfold kQuarantineBatchBytes in *. apply (mapped_N v v' NN); [clear -R1; kung_all; lia| right; clear -R1; kung_all; lia| clear -R2 CE; lia| exact MP].
    - intros SH. eapply bytes_at_xfer; [exact SH|]. intros z Hz. unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size kQuarantineBatchClass) with 8192; clear; lia).
      change (class_size kQuarantineBatchClass) with 8192 in Hz. unfold kQuarantineBatchBytes in *.
      apply (keep_sh (batch_addr (a_sb A) b) (batch_addr (a_sb A) b + 8192)); clear -R1 R2 Hz; kung_all; [lia|lia|lia].
  Qed.

  Lemma tmp_chain_keep : forall bs, (forall b', In b' bs -> In b' (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) -> tmp_chain (a_sb A) v bs -> tmp_chain (a_sb A) v' bs.
  Proof.
    induction bs as [|b' bs IH]; intros SUB TC; [exact I|]. cbn [tmp_chain] in *. destruct TC as [X TC]. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((batch_range A v held AR b' (SUB b' ltac:(left; reflexivity)))) as dR_17; dand3 dR_17 as R1 R2 _ | pose proof (batch_range A v held AR b' (SUB b' ltac:(left; reflexivity))) as (R1 & R2 & _) ]).
    split; [| apply IH; [intros b'' Hb''; apply SUB; right; exact Hb''| exact TC]].
    eapply rw_cells_agree; [exact X|]. cbn [cells_size csize Nat.add]. intros i Hi. apply AGC. unfold kQuarantineBatchBytes in *. clear -Hi R1 R2. kung_all. lia.
  Qed.
End Keep.

(* [comment removed for export] *)
Lemma hidden_keep {Clg : Ceiling} : forall (A : AState) (m v' : mem),
  hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
  (forall a, 0 <= a < alloc_ceiling -> v' (wz a) = aview_of (pa_hull A) m (wz a)) ->
  hidden_repr (a_pl A) (a_reg A) (a_sec A) (munrestrict (hidc (pa_hull A)) m v').
Proof.
  intros A m v' [H1 H2] AG. pose proof alloc_ceiling_val as CE.
  assert (E : forall z, in_shadow_maps z -> munrestrict (hidc (pa_hull A)) m v' (wz z) = m (wz z)).
  { intros z Hz. unfold munrestrict. destruct (hidc (pa_hull A) (wz z)) eqn:Hc; [reflexivity|].
    rewrite AG by (unfold in_shadow_maps in Hz; clear -Hz CE; unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize in *; lia).
    unfold aview_of, mrestrict. rewrite Hc. reflexivity. }
  split.
  - intros z Gz. rewrite (E z (proj1 Gz)). exact (H1 z Gz).
  - intros z Hz NV. rewrite (E z ltac:(unfold in_shadow_maps; left; exact Hz)). exact (H2 z Hz NV).
Qed.
