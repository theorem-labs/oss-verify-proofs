(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMallocA AMallocI AMalmys AMal9l1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AFreeB1 AFreeB2 ATransp AFreeB3 AFreeB4 AFreeB5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5.
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

Section IaShell.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md md1 : Model) (fp : Z) (v1 : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis IA : a_ia_inited A = false.
  Hypothesis CEIL : alloc_ceiling <= fp - ASTK.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) (fp - ASTK) ASTK.
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  (* [comment removed for export] *)
  Hypothesis AG : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ ia_blk a -> v1 (wz a) = v (wz a).
  Hypothesis UNWB : rw_cells rsegs v1 (thr + 3168) [C1 (Z_to_bv 8 0)].
  Hypothesis IAP : ia_post0 v1.
  Hypothesis WM : wmono rsegs v v1.
  Hypothesis CL : forall a, hidc (pa_hull A) a = true -> v1 a = None.
  Hypothesis HI : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
  Hypothesis SB : same_but_materialized md md1.

  Lemma ia_shell_view : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v1) = v1.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL. Qed.

  Theorem ia_shell_ainv : @pa_ainv _ DepotRepL (set_ia A true) (munrestrict (hidc (pa_hull A)) m v1) md1.
  Proof.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    pose proof alloc_ceiling_val as CE. unfold ASTK in *.
    (first [ pose proof ((hit_place A m md AI)) as dR_1; dand7 dR_1 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    assert (LO : alloc_ceiling <= fp - 8192 /\ fp - 8192 <= fp) by (clear -CEIL; lia).
    pose proof ia_shell_view as VIEW.
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v1 (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WM); lia. }
    (first [ pose proof ((ia_post0_facts v1 IAP)) as dR_2; dand3 dR_2 as IR IL IP | destruct (ia_post0_facts v1 IAP) as (IR & IL & IP) ]).
    assert (MU' : forall a, 0 <= a < 2^64 -> ~ (fp - 8192 <= a < fp) -> a <> p_thr (a_pl A) + 3168 -> ~ ia_blk a -> v1 (wz a) = v (wz a)) by exact AG.
    assert (UNW : v1 (wz (p_thr (a_pl A) + 3168)) = v (wz (p_thr (a_pl A) + 3168))).
    { pose proof (ar_consts _ _ _ _ _ (proj2 AR)) as C. unfold consts_repr_ in C. cbv zeta in C.
      (first [ dand36 C as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dR_C_t0; destruct dR_C_t0 as [U0 _] | destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0 & _) ]).
      (first [ dand3 U0 as _ _ U | destruct U0 as (_ & _ & U) ]). destruct UNWB as [[_ (_ & _ & U')] _]. cbn [cells_bytes cbytes app length] in U'.
      specialize (U 0%nat ltac:(cbn; lia)). specialize (U' 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in U, U'. offs_h U. offs_h U'. rewrite Z.add_0_r in U, U'.
      assert (Vn : v (wz (p_thr (a_pl A) + 3168)) <> None).
      { (first [ pose proof ((ar_cache _ _ _ _ _ (proj2 AR))) as dR_5; dand5 dR_5 as _ _ _ MT _ | pose proof (ar_cache _ _ _ _ _ (proj2 AR)) as (_ & _ & _ & MT & _) ]). apply (MT 3168). lia. }
      assert (V'n : v1 (wz (p_thr (a_pl A) + 3168)) <> None) by (pose proof (aobj_facts _ _ TH1) as TF; apply NN; [clear -TF; lia| clear -TF; lia| clear -TF CE; lia| exact Vn]).
      rewrite (mrd_some_eq v _ _ Vn U), (mrd_some_eq v1 _ _ V'n U'). reflexivity. }
    assert (AGB : forall a, 0 <= a < alloc_ceiling -> ~ ia_blk a -> v1 (wz a) = v (wz a)).
    { intros a Ha NI. destruct (Z.eq_dec a (p_thr (a_pl A) + 3168)) as [->|NT]; [exact UNW|]. apply MU'; [clear -Ha CE; lia| clear -Ha LO; lia| exact NT| exact NI]. }
    (* [comment removed for export] *)
    pose proof (aobj_facts _ _ TH1) as THF. pose proof (aobj_facts _ _ CT1) as CTF.
    (first [ pose proof ((place_facts A WF0)) as dR_6; dand13 dR_6 as _ _ Pn0 Pf0 Pfs _ _ _ _ _ Pdt Ppa _ | pose proof (place_facts A WF0) as (_ & _ & Pn0 & Pf0 & Pfs & _ & _ & _ & _ & _ & Pdt & Ppa & _) ]). cbv zeta in Pn0, Pf0, Pfs, Pdt, Ppa.
    (first [ dand3 Pn0 as Pn0 _ _ | destruct Pn0 as (Pn0 & _ & _) ]). (first [ dand3 Pf0 as Pf0 _ _ | destruct Pf0 as (Pf0 & _ & _) ]). (first [ dand3 Pfs as Pfs _ _ | destruct Pfs as (Pfs & _ & _) ]). (first [ dand3 Pdt as Pdt _ _ | destruct Pdt as (Pdt & _ & _) ]). (first [ dand3 Ppa as Ppa _ _ | destruct Ppa as (Ppa & _ & _) ]).
    apply app_facts in Pn0. apply app_facts in Pf0. apply app_facts in Pfs. apply app_facts in Pdt. apply app_facts in Ppa.
    (first [ pose proof ((sb_facts A WF0)) as dR_12; dand5 dR_12 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]).
    assert (AGapp : forall b0 n1 a, (4096 <= b0 /\ 0 <= n1 /\ b0 + n1 <= alloc_ceiling /\ (b0 + n1 <= 0x10000 \/ 0x60a000 <= b0) /\ (b0 + n1 <= kLowShadowMapBeg \/ kHighMemBeg <= b0)) ->
                    b0 <= a < b0 + n1 -> v1 (wz a) = v (wz a)).
    { intros b0 n1 a Hb Ha. apply AGB; [clear -Hb Ha; lia|]. unfold ia_blk. clear -Hb Ha. lia. }
    assert (AGcarved : forall ch a, carved A ch -> chunk_lo (a_sb A) ch <= a < chunk_hi (a_sb A) ch -> v1 (wz a) = v (wz a)).
    { intros ch a C Ha. (first [ pose proof ((carved_range A v AR ch C)) as dR_13; dand3 dR_13 as R1 R2 _ | pose proof (carved_range A v AR ch C) as (R1 & R2 & _) ]). apply AGB; [clear -R1 R2 Ha; lia| unfold ia_blk; clear -R1 Ha; lia]. }
    (* [comment removed for export] *)
    assert (R' : @arepr _ DepotRepL LPA AL_pboth [] (set_ia A true) v1).
    { constructor; cbn [set_ia a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes a_qlimbo a_scred a_deadsh a_pcred a_paid].
      - (* [comment removed for export] *) apply (consts_P2 A v v1 AR).
        + intros cst Hin. destruct (decide (cst = ia_pad)) as [->|NP]; [right; exact IP|]. left. intros a Ha.
          cbn [cl_consts LPA] in Hin.
          assert (BLW : a < alloc_ceiling /\ 0 <= a).
          { destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
            - unfold pa_shared in S. clear -S CE. lia.
            - unfold pa_image_shadow, sh in S. clear -S CE. kung_all. lia.
            - pose proof (pa_static_low a S). unfold pa_static in S. clear -S H CE. lia. }
          apply AGB; [clear -BLW; lia|].
          destruct (decide (cst = q_pad)) as [->|NQ]; [unfold q_pad in Ha; cbn in Ha; unfold ia_blk; clear -Ha; lia|].
          pose proof pa_consts_noia as OK2. rewrite forallb_forall in OK2. specialize (OK2 cst Hin). cbv beta in OK2.
          apply orb_true_iff in OK2 as [OK2|OK2]; [| exfalso; apply NQ; apply (proj1 (bool_decide_eq_true _)) in OK2; exact OK2].
          apply orb_true_iff in OK2 as [OK2|OK2]; [| exfalso; apply NP; apply (proj1 (bool_decide_eq_true _)) in OK2; exact OK2].
          unfold const_noia in OK2. apply andb_true_iff in OK2 as [OK2 _]. apply andb_true_iff in OK2 as [OK2 _]. apply andb_true_iff in OK2 as [OK2 OK3].
          apply orb_true_iff in OK2. apply orb_true_iff in OK3. rewrite !Z.leb_le in OK2, OK3. unfold ia_blk. clear -OK2 OK3 Ha. lia.
        + intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGB; [clear -H CE; lia| unfold ia_blk; clear -H; lia].
        + intros a H. unfold cfoot_stat in H. offs_h H. alc_h H. apply AGB; [clear -H CE; lia| unfold ia_blk; clear -H; lia].
        + intros a H. unfold cfoot_thr in H. offs_h H. apply AGB; [clear -H THF; lia| unfold ia_blk; clear -H THF; lia].
        + intros a H. unfold cfoot_misc in H. pose proof TPV as TP. rewrite TP in H.
          destruct H as [H|[H|[H|[H|[H|H]]]]]; (apply AGB; [first [clear -H CTF; lia| clear -H CE; lia| clear -H Pdt; lia]| unfold ia_blk; first [clear -H CTF; lia| clear -H; lia| clear -H Pdt; lia]]).
      - (* [comment removed for export] *) apply (locks_P2 A v v1 AR); [| exact IL]. intros a H NE. unfold lfoot in H. alc_h H. alc_h NE. unfold p_ri in H. change (p_sb (a_pl A)) with (a_sb A) in H.
        destruct H as [H|H].
        + apply AGB; [clear -H SCE RSB HB6 CE; unfold kRegionInfoSize in H; kung_all; lia| unfold ia_blk; clear -H RSB HB6; unfold kRegionInfoSize in H; kung_all; lia].
        + offs_h H. apply AGB; [clear -H CE; lia| unfold ia_blk; clear -H NE; lia].
      - (* [comment removed for export] *) intros c' Hc. apply (region_P A v v1 AR NN c' Hc). intros a H. unfold rfoot in H.
        pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. unfold region_info_addr, free_array_beg in H. change (p_sb (a_pl A)) with (a_sb A) in *.
        destruct H as [H|H]; (apply AGB; [clear -H RB SCE RSB HB6 CE Hc; unfold kRegionInfoSize in *; kung_all; lia| unfold ia_blk; clear -H RB RSB HB6 Hc; unfold kRegionInfoSize in *; kung_all; lia]).
      - (* [comment removed for export] *) apply (cache_P A v v1 AR NN). intros c' Hc'. apply (cache_line_P A v v1 AR NN (a_cache A) c' Hc' eq_refl).
        intros a Ha. offs_h Ha. cbv beta in Ha. apply AGB; [clear -Ha Hc' THF; lia| unfold ia_blk; clear -Ha Hc' THF; lia].
      - (* [comment removed for export] *) apply (live_sub_P A v v1 AR NN (a_livemap A) (fun u li H => H)). intros u li a Hu Ha.
        exact (AGcarved _ a (known_carved A v AR _ _ (known_live A v AR u li Hu)) Ha).
      - (* [comment removed for export] *) apply (quar_P A v v1 AR NN).
        + intros a Ha. unfold off_th_qcache in Ha. apply AGB; [clear -Ha THF; lia| unfold ia_blk; clear -Ha THF; lia].
        + intros a Ha. alc_h Ha. unfold off_q_cache_list_size in Ha. apply AGB; [clear -Ha CE; lia| unfold ia_blk; clear -Ha; lia].
        + intros b a Hb Ha. (first [ pose proof ((batch_range A v AR b Hb)) as dR_14; dand3 dR_14 as R1 R2 _ | pose proof (batch_range A v AR b Hb) as (R1 & R2 & _) ]). apply AGB; [clear -Ha R1 R2; kung_all; lia| unfold ia_blk; clear -Ha R1; kung_all; lia].
        + intros e a He Ha. exact (AGcarved _ a (known_carved A v AR _ _ (known_quar A v AR e He)) Ha).
      - (* [comment removed for export] *) (first [ pose proof ((wfS A WF0)) as dR_15; dand4 dR_15 as _ LEN RES _ | destruct (wfS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. apply (sec_P A v v1 AR NN).
        + intros a H. unfold sfoot_stat in H. offs_h H. alc_h H. apply AGB; [clear -H CE; lia| unfold ia_blk; clear -H; lia].
        + intros a Ha. apply (AGapp _ _ a Ppa). unfold kPtrArrayReserve. clear -Ha LEN RES. lia.
        + intros sc a Hin Ha. (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_16; dand5 dR_16 as _ _ SB3 SB4 SB5 | pose proof (sec_chunk_bounds A sc WF0 Hin) as (_ & _ & SB3 & SB4 & SB5) ]). apply app_facts in SB3.
          pose proof (needed_size2_secondary (cs_n sc) ltac:(destruct (sec_chunk_bounds A sc WF0 Hin) as (X & _); exact (proj1 X))) as NS2. pose proof (rounded_size_ge (cs_n sc)) as RG. unfold kSecondaryHeaderSize, kPageSize in *.
          apply AGB; [clear -Ha SB3 SB5 NS2 RG; lia| unfold ia_blk; clear -Ha SB3 SB5 NS2 RG; lia].
      - (* [comment removed for export] *) apply (depot_P A v1 (a_depot A) v (ar_depot _ _ _ _ _ (proj2 AR))). intros a Ha.
        unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1 in Ha.
        destruct Ha as [Ha|[Ha|Ha]]; [apply AGB; [clear -Ha CE; lia| unfold ia_blk; clear -Ha; lia]| exact (AGapp _ _ a Pn0 Ha)| exact (AGapp _ _ a Pf0 Ha)].
      - (* [comment removed for export] *) exact IR.
      - apply (fsbase_P A v v1 AR NN). intros a Ha. unfold a_fs in *. apply (AGapp _ _ a Pfs). unfold kFakeFlagsOffset, kFakeStackBytes in *. clear -Ha. lia.
      - apply (fsptrs_P A v v1 AR). intros a Ha. unfold a_fs in *. apply (AGapp _ _ a Pfs). unfold kFakeFramesOffset, kFakeStackBytes in *. clear -Ha. lia.
      - apply (fsflags_P A v v1 AR). intros a Ha. unfold a_fs in *. apply (AGapp _ _ a Pfs). unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. clear -Ha. lia.
      - exact (maps_P A v v1 AR NN).
      - apply (shadow_P0 A v v1 AR). intros z Hz. pose proof (heap_shadow_range A z WF0 Hz) as SR. unfold in_shadow_maps, kLowShadowMapBeg in SR.
        (first [ pose proof (asI_layout_order) as dR_17; dand4 dR_17 as _ _ _ LO4 | pose proof asI_layout_order as (_ & _ & _ & LO4) ]). apply AGB; [clear -SR LO4; unfold kHighShadowMapSize in SR; kung_all; lia| unfold ia_blk; clear -SR; kung_all; lia]. }
    (* [comment removed for export] *)
    constructor.
      - apply WF_set_ia. exact WF0.
      - change (ahull_of pa_image_ivs AL_pboth (set_ia A true)) with (pa_hull A). rewrite VIEW. exact R'.
      - (* [comment removed for export] *)
        cbn [set_ia a_pl a_reg a_sec]. pose proof (ai_hidden _ _ _ _ _ _ _ AI) as [H1 H2]. unfold hidden_repr. unfold munrestrict.
        assert (VIS : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> v1 (wz z) <> None).
        { intros z Hz Hm E. apply NN; [lia| lia| lia|]. unfold aview_of, mrestrict. rewrite E. exact Hm. }
        (first [ pose proof (asI_layout_order) as dR_18; dand4 dR_18 as _ _ _ LO4 | pose proof asI_layout_order as (_ & _ & _ & LO4) ]).
        split.
        + intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _].
          destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (conj P1 P2)|]. split.
          * apply VIS; [unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in Hz; kung_all; lia| exact P1| exact E].
          * intros NHS. rewrite <- (P2 NHS). transitivity (v (wz z)); [| unfold aview_of, mrestrict; rewrite E; reflexivity].
            unfold in_shadow_maps, kHighShadowMapSize, kLowShadowMapBeg in Hz. apply AGB; [clear -Hz LO4; kung_all; lia| unfold ia_blk; clear -Hz; kung_all; lia].
        + intros z Hz NB. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (H2 z Hz NB)|]. apply VIS; [unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NB)| exact E].
      - cbn [set_ia a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
      - cbn [set_ia a_pl a_sec]. exact (aledger_sbm _ _ _ _ md md1 SB (ai_ledger _ _ _ _ _ _ _ AI)).
      - exact HI.
      - (first [ pose proof ((same_but_materialized_frame _ _ SB)) as dR_19; dand18 dR_19 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct (same_but_materialized_frame _ _ SB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact (ai_halted _ _ _ _ _ _ _ AI).
      - rewrite (same_but_materialized_vmmaps _ _ SB). cbn [set_ia a_pl a_sec]. exact (ai_cover _ _ _ _ _ _ _ AI).
      - (* [comment removed for export] *) rewrite (same_but_materialized_vmmaps _ _ SB). exact (ai_ceil _ _ _ _ _ _ _ AI).
  Qed.
End IaShell.
