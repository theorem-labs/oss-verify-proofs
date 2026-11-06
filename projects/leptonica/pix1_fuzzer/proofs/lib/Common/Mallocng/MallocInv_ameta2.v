(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_ameta_base.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Local Ltac llia ::= first [ solve [LiaFast.flia2] | pose proof layout_small; lia | pose proof layout_nums; lia | lia ].   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


Ltac cside := cbn [f_a f_n f_v caddr clen]; unfold C_AM, C_AMC, C_FMH, C_INIT, C_SECRET; llia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma last_in : forall (l : list Z) d, l <> [] -> In (last l d) l.
Proof using Type. pu_keep tt.
  induction l as [|a l IH]; intros d Hne; [exfalso; exact (Hne eq_refl)|].
  destruct l as [|b l']; [left; reflexivity|]. right. apply IH. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ts_assoc : forall {R B C} (m0 : M B) (f : B -> M C) (g : C -> M R) s P,
  tsafe ((x <- m0 ;; y <- f x ;; g y) s) P -> tsafe ((y <- (x <- m0 ;; f x) ;; g y) s) P.
Proof using Type. pu_keep tt. intros R B C m0 f g s P H. reassoc. exact H. Qed.

Section Carve.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate).
  Hypothesis HI : IS sp0 argv envp cb A s.
  Hypothesis HV : VMok A (ms_vm s).
  Hypothesis Hamc : a_ctx A KAmc > 0.
  Implicit Types (P : R -> mstate -> Prop).

  Let amc := a_ctx A KAmc.
  Let pg := last (a_areas A) 0.
  Let m := meta_addr pg (101 - amc).

  Definition cv_ctx : ctx_rec := cupd (cupd (a_ctx A) KAm (m + 40)) KAmc (amc - 1).
  Definition cvA1 : astate := set_ctx A cv_ctx.

  Lemma cv_ctx_other : forall k, k <> KAm -> k <> KAmc -> cv_ctx k = a_ctx A k.
  Proof using Type. pu_keep tt. intros k H1 H2. unfold cv_ctx. rewrite !cupd_other by assumption. reflexivity. Qed.
  Lemma cv_ctx_am : cv_ctx KAm = m + 40.
  Proof using Type. pu_keep tt. unfold cv_ctx. rewrite cupd_other by discriminate. apply cupd_same. Qed.
  Lemma cv_ctx_amc : cv_ctx KAmc = amc - 1.
  Proof using Type. pu_keep tt. unfold cv_ctx. apply cupd_same. Qed.

  (* [comment removed for export] *)
  Lemma carve_am : a_areas A <> [] /\ a_ctx A KAm = m /\ In pg (a_areas A) /\ amc <= 100 /\
    (forall k, 101 - amc <= k < 101 -> exists mt, a_meta A (meta_addr pg k) = Some mt /\ mt_role mt = RAvail).
  Proof using HI Hamc. pu_keep (HI, Hamc).
    pose proof (is_wf _ _ _ _ _ _ HI) as HW.
    destruct (wf_am A HW Hamc) as (pg' & H1 & H2 & H3 & H4). pose proof (wf_amc A HW).
    assert (Epg : pg' = pg) by (rewrite H2; reflexivity). subst pg'.
    split; [exact H1|]. split; [exact H3|]. split; [| split; [llia | exact H4]].
    unfold pg. apply last_in. exact H1.
  Qed.

  Variable D : list Z.
  Hypothesis HD : deads A D.
  Hypothesis HAV : AvOK A.

  Theorem carve_ok : forall (K : word -> M R) P,
    (forall s' A', IS sp0 argv envp cb A' s' -> VMok A' (ms_vm s') -> ms_vm s' = ms_vm s -> FR A s A' s' ->
       got_meta A D A' m -> a_areas A' = a_areas A -> a_ctx A' KAmc = amc - 1 ->
       a_freelist A' = a_freelist A -> a_pages A' = a_pages A -> a_mblocks A' = a_mblocks A -> a_xmaps A' = a_xmaps A ->
       (forall k, cvalid k -> k <> KAm -> k <> KAmc -> a_ctx A' k = a_ctx A k) ->
       tsafe (K (Z_to_bv 64 m) s') P) ->
    tsafe ((x <- (mm <- m_ld A_AVAIL_META ;;
                  m_sd A_AVAIL_META (at_ mm 40) ;;
                  m_sd A_AVAIL_META_CNT (v_addi (Z_to_bv 64 amc) (-1)) ;;
                  m_sd (at_ mm 8) w0 ;; m_sd mm w0 ;;
                  mret mm) ;; K x) s) P.
  Proof using HAV HD HI HV Hamc MLok. pu_keep (HAV, HD, HI, HV, Hamc, MLok).
    intros K P HK. pose proof HI as [HW HR HC HWIN HE HG].
    destruct carve_am as (Hane & Eam & Hpg & Hamc100 & Hav).
    destruct (Hav (101 - amc) ltac:(llia)) as (mt & Hmt & Hrmt). fold m in Hmt.
    destruct (wf_areas_al A HW pg Hpg) as [Hpal Hph]. unfold heap_range in Hph. ceil.
    pose proof (meta_addr_range pg (101 - amc) ltac:(llia)) as Hmr. fold m in Hmr.
    assert (Hdom : forall j, 0 <= j < 40 -> dom A (m + j)) by (intros j Hj; left; exists pg; split; [exact Hpg | llia]).
    reassoc. rewrite A_AVAIL_META_eq.
    eapply (ts_ld_ctx A); [exact HR | exact HWIN | exact I | reflexivity | rewrite Eam; llia |]. rewrite Eam.
    reassoc. unfold m_sd at 1. rewrite at_Z.
    eapply (ts_st_ctxw A); [apply repw_init; [exact HW | exact HR] | exact HWIN | exact I |].
    pose proof (repw_st_ctx A s (ms_mem s) [] KAm (Z_to_bv 64 (m + 40)) (repw_init A _ HW HR) I) as RW1.
    set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (caddr KAm)) (word_to_le_bytes (Z.to_nat (clen KAm)) (Z_to_bv 64 (m + 40)))) in RW1 |- *.
    reassoc. rewrite A_AVAIL_META_CNT_eq. unfold m_sd at 1. rewrite v_addi_Z.
    eapply (ts_st_ctxw A (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
    pose proof (repw_st_ctx A (upd s m1 (ms_vm s)) (ms_mem s) _ KAmc (Z_to_bv 64 (amc + -1)) RW1 I) as RW2. cbn [ms_mem upd] in RW2.
    set (m2 := wbytes m1 (Z_to_bv 64 (caddr KAmc)) (word_to_le_bytes (Z.to_nat (clen KAmc)) (Z_to_bv 64 (amc + -1)))) in RW2 |- *.
    reassoc. unfold m_sd at 1. rewrite at_Z.
    eapply (ts_st_domw A HW (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (m + 8 + j) with (m + (8 + j)) by llia; apply Hdom; llia |].
    cbn [ms_mem ms_vm upd].
    pose proof (repw_st_dom A HW (upd s m2 (ms_vm s)) (ms_mem s) _ 8 (m + 8) w0 RW2 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (m + 8 + j) with (m + (8 + j)) by llia; apply Hdom; llia)) as RW3.
    cbn [ms_mem upd] in RW3.
    set (m3 := wbytes m2 (Z_to_bv 64 (m + 8)) (word_to_le_bytes 8 w0)) in RW3 |- *.
    reassoc. unfold m_sd at 1.
    eapply (ts_st_domw A HW (upd s m3 (ms_vm s)) (ms_mem s)); [exact RW3 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom; llia |].
    cbn [ms_mem ms_vm upd].
    pose proof (repw_st_dom A HW (upd s m3 (ms_vm s)) (ms_mem s) _ 8 m w0 RW3 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom; llia)) as RW4.
    cbn [ms_mem upd] in RW4.
    set (m4 := wbytes m3 (Z_to_bv 64 m) (word_to_le_bytes 8 w0)) in RW4 |- *.
    apply ts_bind_ret.
    (* [comment removed for export] *)
    set (A2 := kmA cvA1 m mt).
    assert (HW1 : WF cvA1).
    { apply WF_set_ctx; try exact HW; rewrite ?cv_ctx_amc, ?cv_ctx_am; rewrite ?cv_ctx_other by discriminate.
      - exact (wf_init A HW).
      - intros H0. exfalso. destruct (wf_uninit A HW H0) as (_ & _ & E3 & _). unfold amc in Hamc. llia.
      - llia.
      - intros Hc. exists pg. split; [exact Hane|]. split; [reflexivity|]. split; [unfold m, meta_addr; llia|].
        intros k Hk. apply Hav. llia.
      - exact (wf_atail A HW).
      - exact (wf_ahead A HW).
      - exact (wf_fl_head A HW).
      - intros sc Hsc. rewrite cv_ctx_other by discriminate. exact (wf_act_head A HW sc Hsc).
      - intros k. unfold cv_ctx, cupd. destruct (cslot_eq_dec k KAmc); [llia|]. destruct (cslot_eq_dec k KAm); [llia|]. exact (wf_ctx_nonneg A HW k).
      - exact (wf_shift A HW).
      - exact (wf_noarea_shift A HW).
      - exact (wf_brk0 A HW).
      - exact (wf_mblocks_len A HW).
      - exact (wf_shift_mblocks A HW).
      - exact (wf_shift_acct A HW). }
    assert (Hmt1 : a_meta cvA1 m = Some mt) by exact Hmt.
    assert (HW2 : WF A2).
    { apply (WF_kill_meta cvA1 HW1 m mt Hmt1); [left; exact Hrmt|].
      cbn [a_ctx a_areas cvA1 set_ctx]. rewrite cv_ctx_amc. fold pg. intros k Hc Hk E.
      unfold m, meta_addr in E. llia. }
    pose proof (wf_avail_zero A HW m mt Hmt Hrmt) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
    (* [comment removed for export] *)
    assert (HR2 : Rep A2 m4).
    { apply (repw_commit A A2 (ms_mem s) _ m4 RW4).
      - intros x b (f & Hf & Hfb). apply (proj1 (has_kmA cvA1 m mt Hmt1 (or_introl Hrmt) f)) in Hf.
        destruct (has_set_ctx A cv_ctx f Hf) as [(k & Hk & ->) | [(Har & _) | [(pg' & Hpg' & ->) | Hrest]]].
        + destruct Hfb as [Hx ->]. cbn [f_a f_n f_v] in Hx |- *.
          destruct (cslot_eq_dec k KAm) as [-> | Hn1]; [right; cbn [caddr clen] in Hx; unfold C_AM in Hx; rewrite !wlook_skip by cside; rewrite wlook_hit by cside; discriminate|].
          destruct (cslot_eq_dec k KAmc) as [-> | Hn2]; [right; cbn [caddr clen] in Hx; unfold C_AMC in Hx; rewrite !wlook_skip by cside; rewrite wlook_hit by cside; discriminate|].
          left. rewrite (cv_ctx_other k Hn1 Hn2). exists (FCT (caddr k) (clen k) (a_ctx A k)). split; [left; exists k; auto | split; [exact Hx | reflexivity]].
        + left. exists f. split; [right; left; exact Har | exact Hfb].
        + left. rewrite (cv_ctx_other KSecret) in Hfb by discriminate. exists (FCT pg' 8 (a_ctx A KSecret)). split; [right; left; exists pg'; auto | exact Hfb].
        + left. exists f. split; [destruct Hrest as [Hm | Hg]; [right; right; left; exact Hm | right; right; right; exact Hg] | exact Hfb].
      - intros x b (f & Hf & Hfb) Hw. apply (proj1 (has_kmA cvA1 m mt Hmt1 (or_introl Hrmt) f)) in Hf.
        (* [comment removed for export] *)
        destruct Hfb as [Hx ->].
        assert (CASES : (m <= x < m + 16) \/ (caddr KAmc <= x < caddr KAmc + 8) \/ (caddr KAm <= x < caddr KAm + 8)).
        { assert (DQrng : m <= x < (m + 16) \/ (caddr KAmc) <= x < (caddr KAmc + 8) \/ (caddr KAm) <= x < (caddr KAm + 8) \/
                         (~ (m <= x < (m + 16)) /\ ~ ((caddr KAmc) <= x < (caddr KAmc + 8)) /\ ~ ((caddr KAm) <= x < (caddr KAm + 8)))) by lia.
          destruct DQrng as [DQrng | [DQrng | [DQrng | DQrng]]];
            [ left; llia
            | right; left; llia
            | right; right; llia |].
           
          exfalso; apply Hw; cbn [caddr clen] in *; unfold C_AM, C_AMC in *; rewrite !wlook_skip by cside; reflexivity. }
        destruct CASES as [Cm | [Camc | Cam]].
        + (* [comment removed for export] *)
          assert (Hf0 : has A f).
          { destruct (has_set_ctx A cv_ctx f Hf) as [(k & Hk & ->) | [(Har & _) | [(pg' & Hpg' & ->) | Hrest]]].
            - exfalso. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). cbn in Hx. unfold LOCKA, CTX_END in *. llia.
            - right; left. exact Har.
            - right; left. exists pg'. rewrite (cv_ctx_other KSecret) by discriminate. auto.
            - destruct Hrest as [Hm | Hg]; [right; right; left; exact Hm | right; right; right; exact Hg]. }
          destruct (Z.lt_ge_cases x (m + 8)) as [C0 | C8].
          * pose proof (fact_at_meta A HW f m mt FPrev x Hf0 Hmt Hx ltac:(cbn; llia)) as ->. cbn [f_a f_v]. unfold mt_prev in Z1. rewrite Z1.
            cbn [caddr clen]. unfold C_AM, C_AMC. rewrite wlook_hit by cside. cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity.
            rewrite !byte_of_zero. reflexivity.
          * pose proof (fact_at_meta A HW f m mt FNext x Hf0 Hmt Hx ltac:(cbn; llia)) as ->. cbn [f_a f_v]. unfold mt_next in Z2. rewrite Z2.
            cbn [caddr clen]. unfold C_AM, C_AMC. rewrite wlook_skip by cside. rewrite wlook_hit by cside. cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity.
            rewrite !byte_of_zero. reflexivity.
        + pose proof (fact_at_ctx cvA1 HW1 f KAmc x Hf I Hx Camc) as ->. cbn [f_a f_v a_ctx cvA1 set_ctx]. rewrite cv_ctx_amc.
          cbn [caddr clen] in *. unfold C_AM, C_AMC in *. rewrite !wlook_skip by cside. rewrite wlook_hit by cside. cbn [f_a f_v].
          rewrite uZ by llia. replace (amc + -1) with (amc - 1) by llia. reflexivity.
        + pose proof (fact_at_ctx cvA1 HW1 f KAm x Hf I Hx Cam) as ->. cbn [f_a f_v a_ctx cvA1 set_ctx]. rewrite cv_ctx_am.
          cbn [caddr clen] in *. unfold C_AM, C_AMC in *. rewrite !wlook_skip by cside. rewrite wlook_hit by cside. cbn [f_a f_v].
          rewrite uZ by llia. reflexivity.
      - intros x Hx. apply (proj1 (dom_kmA cvA1 m mt Hmt1 (or_introl Hrmt) x)) in Hx. exact Hx. }
    (* [comment removed for export] *)
    assert (FRM : forall a : word, m4 a = ms_mem s a \/
              (m <= bv_unsigned a < m + 16 \/ caddr KAmc <= bv_unsigned a < caddr KAmc + 8 \/ caddr KAm <= bv_unsigned a < caddr KAm + 8)).
    { intros a. pose proof (u64_range a).
      assert (DQrng : m <= (bv_unsigned a) < (m + 16) \/ (caddr KAmc) <= (bv_unsigned a) < (caddr KAmc + 8) \/ (caddr KAm) <= (bv_unsigned a) < (caddr KAm + 8) \/
                     (~ (m <= (bv_unsigned a) < (m + 16)) /\ ~ ((caddr KAmc) <= (bv_unsigned a) < (caddr KAmc + 8)) /\ ~ ((caddr KAm) <= (bv_unsigned a) < (caddr KAm + 8)))) by lia.
      destruct DQrng as [DQrng | [DQrng | [DQrng | DQrng]]];
        [ right; llia
        | right; llia
        | right; llia |].
       
        left; unfold m4, m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *; unfold C_AM, C_AMC in *;
        rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn; llia); reflexivity. }
    assert (KEEP : forall a : word, ms_mem s a <> None -> m4 a <> None).
    { intros a Ha. unfold m4, m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat]. unfold C_AM, C_AMC.
      repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|]). exact Ha. }
    assert (GS : gsame A A2).
    { constructor; unfold A2; cbn [a_active a_live a_ctx kmA ameta_upd set_meta cvA1 set_ctx]; auto.
      - intros x mtx aib sl Hx Hrx. apply (km_old_grp cvA1 m mt Hmt1 (or_introl Hrmt) x mtx aib sl); [exact Hx | exact Hrx].
      - intros x mtx aib sl Hx Hrx. exact (proj1 (km_group_inv cvA1 m mt x mtx aib sl Hx Hrx)).
      - intros x mtx Hx Hrx. apply (km_old cvA1 m mt x mtx); [exact Hx|]. intros ->. unfold cvA1, set_ctx in Hx. cbn in Hx.
        fold m in Hmt. rewrite Hmt in Hx. injection Hx as <-. rewrite Hrmt in Hrx. discriminate Hrx.
      - intros k Hk _. apply cv_ctx_other; intros ->; exact Hk. }
    apply (HK _ A2).
    - (* [comment removed for export] *) apply (IS_mem sp0 argv envp cb A A2 s m4 HI HW2 HR2).
      + intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. cbn [caddr] in X. unfold C_AM, C_AMC in X. unfold mzone, CTX, CTX_END. ceil. llia.
      + intros a Ha. destruct (FRM a) as [E | [X | X]]; [left; rewrite <- E; exact Ha | left | right; left; cbn [caddr] in X; unfold C_AM, C_AMC in X; llia].
        rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom A _ HR). replace (bv_unsigned a) with (m + (bv_unsigned a - m)) by llia. apply Hdom. llia.
    - (* [comment removed for export] *) cbn [ms_vm upd]. apply (VMok_kmA cvA1 m mt Hmt1 (or_introl Hrmt) (ms_vm s)). apply (VMok_set_ctx A cv_ctx (ms_vm s) HV).
      + rewrite cv_ctx_other by discriminate. exact (vm_brk_ok A _ HV).
      + rewrite !cv_ctx_other by discriminate. exact (vm_areas_res A _ HV).
      + rewrite cv_ctx_other by discriminate. exact (proj1 (vm_brk_span A _ HV)).
    - reflexivity.
    - (* [comment removed for export] *) apply (FR_memA A A2 s m4 HW).
      + intros x. apply (dom_kmA cvA1 m mt Hmt1 (or_introl Hrmt)).
      + reflexivity.
      + intros a. destruct (FRM a) as [E | [X | X]]; [left; exact E | right; right; right | right; left; cbn [caddr] in X; unfold C_AM, C_AMC in X; unfold LOCKA, CTX_END; llia].
        split; [replace (bv_unsigned a) with (m + (bv_unsigned a - m)) by llia; apply Hdom; llia|].
        intros p n Hp. apply (area_not_live A pg (bv_unsigned a) p n HW Hpg); [llia | exact Hp].
      + exact KEEP.
    - (* [comment removed for export] *) constructor.
      + exists (MT (mt_f mt) RDead). split; [unfold A2; apply km_meta_same|]. split; [reflexivity|].
        intros fl. destruct fl; cbn; assumption.
      + llia.
      + ceil. llia.
      + intros j Hj. apply (proj2 (dom_kmA cvA1 m mt Hmt1 (or_introl Hrmt) (m + j))). apply Hdom. exact Hj.
      + intros x. split.
        * intros (mtx & Hx & Hrx). destruct (km_meta_inv cvA1 m mt x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [left; reflexivity | right].
          apply (proj1 (HD x)). exists mtx. auto.
        * intros [<- | Hin]; [exists (MT (mt_f mt) RDead); split; [apply km_meta_same | reflexivity]|].
          destruct (proj2 (HD x) Hin) as (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx].
          apply (km_old cvA1 m mt x mtx Hx). intros ->. fold m in Hmt. unfold cvA1, set_ctx in Hx; cbn in Hx. rewrite Hmt in Hx. injection Hx as <-. rewrite Hrmt in Hrx. discriminate Hrx.
      + intros Hin. destruct (proj2 (HD m) Hin) as (mtx & Hx & Hrx). fold m in Hmt. rewrite Hmt in Hx. injection Hx as <-. rewrite Hrmt in Hrx. discriminate Hrx.
      + exact GS.
      + intros x mtx Hx Hrx. destruct (km_meta_inv cvA1 m mt x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrx; discriminate Hrx|].
        destruct (HAV x mtx Hx' Hrx) as (k & Hk & Ex). exists k. unfold A2. cbn [a_ctx a_areas kmA ameta_upd set_meta cvA1 set_ctx].
        rewrite cv_ctx_amc. fold pg. split; [| exact Ex].
        assert (k <> 101 - amc) by (intros ->; apply Hne; rewrite Ex; reflexivity). unfold amc in *. llia.
    - reflexivity.
    - unfold A2. cbn [a_ctx kmA ameta_upd set_meta cvA1 set_ctx]. apply cv_ctx_amc.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros k _ H1 H2. unfold A2. cbn [a_ctx kmA ameta_upd set_meta cvA1 set_ctx]. apply cv_ctx_other; assumption.
  Qed.
End Carve.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dll_kept_gen : forall (A A' : astate) l, dll A l ->
  (forall y mt, In y l -> a_meta A y = Some mt ->
     exists mt', a_meta A' y = Some mt' /\ mt_next mt' = mt_next mt /\ mt_prev mt' = mt_prev mt) ->
  dll A' l.
Proof using Type. pu_keep tt.
  intros A A' l Hd Hk k x Hk'. destruct (Hd k x Hk') as (mt & Hx & Hn & Hp).
  destruct (Hk x mt (nth_error_In _ _ Hk') Hx) as (mt' & Hx' & En & Ep). exists mt'. rewrite En, Ep. auto.
Qed.

Section Pop.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate).
  Hypothesis HI : IS sp0 argv envp cb A s.
  Hypothesis HV : VMok A (ms_vm s).
  Variables (m : Z) (rest : list Z).
  Hypothesis Hfl : a_freelist A = m :: rest.
  Variable D : list Z.
  Hypothesis HD : deads A D.
  Hypothesis HAV : AvOK A.
  Implicit Types (P : R -> mstate -> Prop).

  Let l := m :: rest.
  Let n := length l.
  Let xn := nth (1 mod n) l 0.
  Let xp := nth ((0 + n - 1) mod n)%nat l 0.

  Definition popP : Z -> option Z := fun x => if x =? xn then Some xp else None.
  Definition popN : Z -> option Z := fun x => if x =? xp then Some xn else None.
  Definition popA : astate := MallocInv_wf3.A' A popP popN (a_active A) rest (Some (m, mzero RDead)).

  Lemma HWp : WF A. Proof using HI. pu_keep (HI). exact (is_wf _ _ _ _ _ _ HI). Qed.

  Lemma fl_free : forall x, In x l -> exists mt, a_meta A x = Some mt /\ mt_role mt = RFree.
  Proof using HI Hfl. pu_keep (HI, Hfl). intros x Hx. apply (proj1 (wf_fl_mem A HWp x)). rewrite Hfl. exact Hx. Qed.

  Lemma m_meta : exists mt, a_meta A m = Some mt /\ mt_role mt = RFree /\ mt_next mt = xn /\ mt_prev mt = xp /\
    mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0.
  Proof using HI Hfl n. pu_keep (HI, Hfl, n).
    destruct (fl_free m ltac:(left; reflexivity)) as (mt & Hm & Hr).
    pose proof (wf_fl_dll A HWp) as Hd. rewrite Hfl in Hd. destruct (Hd 0%nat m eq_refl) as (mt' & Hm' & Hn & Hp).
    rewrite Hm in Hm'. injection Hm' as <-.
    destruct (wf_free_zero A HWp m mt Hm Hr) as (Z1 & Z2 & Z3 & Z4).
    exists mt. repeat split; auto.
  Qed.

  Lemma xn_in : In xn l.
  Proof using xp. pu_keep (xp). unfold xn. apply nth_In. apply Nat.mod_upper_bound. unfold n, l. cbn. llia. Qed.
  Lemma xp_in : In xp l.
  Proof using xn. pu_keep (xn). unfold xp. apply nth_In. apply Nat.mod_upper_bound. unfold n, l. cbn. llia. Qed.

  Lemma nodup_l : List.NoDup l.
  Proof using HI Hfl. pu_keep (HI, Hfl). apply (proj1 (NoDup_ListNoDup _)). unfold l. rewrite <- Hfl. exact (wf_fl_nodup A HWp). Qed.

  Lemma m_notin_rest : ~ In m rest.
  Proof using HI Hfl. pu_keep (HI, Hfl). pose proof nodup_l as ND. unfold l in ND. inversion ND; subst. exact H1. Qed.

  (* [comment removed for export] *)
  Lemma relink_nonfree : forall x mt, a_meta A x = Some mt -> mt_role mt <> RFree ->
    MallocInv_wf3.relink popP popN x mt = MT (mt_f mt) (mt_role mt).
  Proof using HI Hfl. pu_keep (HI, Hfl).
    intros x mt Hx Hr. unfold MallocInv_wf3.relink, popP, popN.
    assert (Hxn : x <> xn) by (intros ->; destruct (fl_free xn xn_in) as (mt' & H' & R'); rewrite Hx in H'; injection H' as <-; exact (Hr R')).
    assert (Hxp : x <> xp) by (intros ->; destruct (fl_free xp xp_in) as (mt' & H' & R'); rewrite Hx in H'; injection H' as <-; exact (Hr R')).
    rewrite (proj2 (Z.eqb_neq x xn) Hxn), (proj2 (Z.eqb_neq x xp) Hxp).
    (* [comment removed for export] *)
    apply meta_ext; [reflexivity | intros fl; destruct fl; reflexivity].
  Qed.

  Lemma g'_nonvictim : forall x, x <> m -> MallocInv_wf3.g' A popP popN (Some (m, mzero RDead)) x = option_map (MallocInv_wf3.relink popP popN x) (a_meta A x).
  Proof using Type. pu_keep tt. intros x Hx. unfold MallocInv_wf3.g'. destruct (Z.eq_dec x m); [contradiction | reflexivity]. Qed.

  Lemma g'_victim : MallocInv_wf3.g' A popP popN (Some (m, mzero RDead)) m = Some (mzero RDead).
  Proof using Type. pu_keep tt. unfold MallocInv_wf3.g'. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.

  Lemma popA_meta : forall x, a_meta popA x = MallocInv_wf3.g' A popP popN (Some (m, mzero RDead)) x.
  Proof using Type. pu_keep tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma pop_meta_inv : forall x mt', a_meta popA x = Some mt' -> x <> m ->
    exists mt, a_meta A x = Some mt /\ mt' = MallocInv_wf3.relink popP popN x mt.
  Proof using Type. pu_keep tt.
    intros x mt' Hx Hne. rewrite popA_meta, g'_nonvictim in Hx by exact Hne.
    destruct (a_meta A x) as [mt|]; [| discriminate Hx]. cbn in Hx. injection Hx as <-. exists mt. auto.
  Qed.

  Theorem WF_popA : WF popA.
  Proof using HI Hfl. pu_keep (HI, Hfl).
    pose proof HWp as HW. destruct m_meta as (mt & Hm & Hrm & Hnx & Hpv & Z1 & Z2 & Z3 & Z4).
    assert (RESTF : forall x, In x rest -> x <> m /\ exists mtx, a_meta A x = Some mtx /\ mt_role mtx = RFree).
    { intros x Hx. split; [intros ->; exact (m_notin_rest Hx)|]. apply fl_free. right. exact Hx. }
    apply WF_relists; try exact HW.
    - (* [comment removed for export] *) exists mt. split; [exact Hm|]. split; [right; exact Hrm | left; reflexivity].
    - (* [comment removed for export] *) apply (proj2 (NoDup_ListNoDup _)). pose proof nodup_l as ND. unfold l in ND. inversion ND; subst. exact H2.
    - (* [comment removed for export] *) intros x. split.
      + intros Hx. destruct (RESTF x Hx) as (Hne & mtx & Hmx & Hrx).
        exists (MallocInv_wf3.relink popP popN x mtx). rewrite g'_nonvictim by exact Hne. rewrite Hmx. split; [reflexivity | exact Hrx].
      + intros (mt' & Hx & Hr'). destruct (Z.eq_dec x m) as [-> | Hne].
        * rewrite g'_victim in Hx. injection Hx as <-. cbn in Hr'. discriminate Hr'.
        * rewrite g'_nonvictim in Hx by exact Hne. destruct (a_meta A x) as [mtx|] eqn:E; [| discriminate Hx]. cbn in Hx. injection Hx as <-.
          cbn in Hr'. assert (Hin : In x l) by (unfold l; rewrite <- Hfl; apply (proj2 (wf_fl_mem A HW x)); exists mtx; auto).
          destruct Hin as [E0 | Hin]; [exfalso; exact (Hne (eq_sym E0)) | exact Hin].
    - (* [comment removed for export] *) destruct (list_eq_dec Z.eq_dec rest []) as [Er | Er]; [rewrite Er; intros k x Hk; destruct k; discriminate Hk|].
      pose proof (dll_remove A popA [] m rest) as DR. cbn [app] in DR. apply DR.
      + exact nodup_l.
      + exact Er.
      + pose proof (wf_fl_dll A HW) as X. rewrite Hfl in X. exact X.
      + intros k y mty Hk Hy. pose proof (nth_error_In _ _ Hk) as Hin. destruct (RESTF y Hin) as (Hne & _).
        exists (MallocInv_wf3.relink popP popN y mty). rewrite popA_meta, g'_nonvictim, Hy by exact Hne. split; [reflexivity|].
        unfold MallocInv_wf3.relink, popP, popN, mt_next, mt_prev. cbn [mt_f].
        fold l. fold n. change (length []) with 0%nat. fold xn. fold xp.
        split; [destruct (y =? xp); reflexivity | destruct (y =? xn); reflexivity].
    - (* [comment removed for export] *) exact (wf_act_nodup A HW).
    - (* [comment removed for export] *) intros sc Hsc. apply (dll_kept_gen A popA (a_active A sc) (wf_act_dll A HW sc Hsc)).
      intros y mty Hin Hy. destruct (wf_act_mem A HW sc y Hin) as (mt0 & aib & sl & Hy0 & Hr0 & _). rewrite Hy in Hy0. injection Hy0 as <-.
      assert (Hne : y <> m) by (intros ->; rewrite Hm in Hy; injection Hy as <-; rewrite Hrm in Hr0; discriminate Hr0).
      exists (MallocInv_wf3.relink popP popN y mty). rewrite popA_meta, g'_nonvictim, Hy by exact Hne. split; [reflexivity|].
      rewrite (relink_nonfree y mty Hy) by (rewrite Hr0; discriminate). split; reflexivity.
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem A HW sc x Hin) as (mt0 & aib & sl & Hx & Hr0 & Hsc).
      exists (MallocInv_wf3.relink popP popN x mt0), aib, sl. split; [apply (MallocInv_wf3.g'_of_group A popP popN (Some (m, mzero RDead))) with (aib := aib) (slots := sl); [| exact Hx | exact Hr0]|].
      { exists mt. split; [exact Hm|]. split; [right; exact Hrm | left; reflexivity]. }
      rewrite (relink_nonfree x mt0 Hx) by (rewrite Hr0; discriminate). split; [exact Hr0 | exact Hsc].
    - (* [comment removed for export] *) intros x mt' aib sl Hx Hr'.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite g'_victim in Hx; injection Hx as <-; cbn in Hr'; discriminate Hr'|].
      destruct (pop_meta_inv x mt' Hx Hne) as (mt0 & Hx0 & ->). cbn in Hr'.
      rewrite (relink_nonfree x mt0 Hx0) by (rewrite Hr'; discriminate). cbn. intros Hnin.
      exact (wf_unlinked A HW x mt0 aib sl Hx0 Hr' Hnin).
    - (* [comment removed for export] *) intros sc x mt' Hin Hne Hx.
      destruct (wf_act_mem A HW sc x Hin) as (mt0 & aib & sl & Hx0 & Hr0 & _).
      assert (Hxm : x <> m) by (intros ->; rewrite Hm in Hx0; injection Hx0 as <-; rewrite Hrm in Hr0; discriminate Hr0).
      destruct (pop_meta_inv x mt' Hx Hxm) as (mt1 & Hx1 & ->). rewrite Hx0 in Hx1. injection Hx1 as <-.
      unfold mt_avail, mt_freed. cbn. exact (wf_act_nonhead A HW sc x mt0 Hin Hne Hx0).
    - (* [comment removed for export] *) intros x mt' aib sl Hx Hr'.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite g'_victim in Hx; injection Hx as <-; cbn in Hr'; discriminate Hr'|].
      destruct (pop_meta_inv x mt' Hx Hne) as (mt0 & Hx0 & ->). cbn in Hr'.
      rewrite (relink_nonfree x mt0 Hx0) by (rewrite Hr'; discriminate). cbn. exact (wf_act63 A HW x mt0 aib sl Hx0 Hr').
    - (* [comment removed for export] *) intros sc x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry.
      destruct (MallocInv_wf3.g'_group A popP popN (Some (m, mzero RDead))) with (x := x) (mt' := mtx) (aib := aibx) (slots := slx) as (mx0 & Hmx0 & Hrx0 & ->);
        [exists mt; split; [exact Hm|]; split; [right; exact Hrm | left; reflexivity] | exact Hx | exact Hrx |].
      destruct (MallocInv_wf3.g'_group A popP popN (Some (m, mzero RDead))) with (x := y) (mt' := mty) (aib := aiby) (slots := sly) as (my0 & Hmy0 & Hry0 & ->);
        [exists mt; split; [exact Hm|]; split; [right; exact Hrm | left; reflexivity] | exact Hy | exact Hry |].
      exact (wf_partial A HW sc x mx0 aibx slx y my0 aiby sly Hinx Hiny Hmx0 Hrx0 Hmy0 Hry0).
    - (* [comment removed for export] *) intros x mt' Hx Hr'.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite g'_victim in Hx; injection Hx as <-; cbn in Hr'; discriminate Hr'|].
      destruct (pop_meta_inv x mt' Hx Hne) as (mt0 & Hx0 & ->). cbn in Hr'.
      rewrite (relink_nonfree x mt0 Hx0) by (rewrite Hr'; discriminate). exact (wf_avail_zero A HW x mt0 Hx0 Hr').
    - (* [comment removed for export] *) intros x mt' Hx Hr'.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite g'_victim in Hx; injection Hx as <-; cbn; repeat split; reflexivity|].
      destruct (pop_meta_inv x mt' Hx Hne) as (mt0 & Hx0 & ->). cbn in Hr'.
      unfold mt_mem, mt_avail, mt_freed, mt_w32. cbn. exact (wf_free_zero A HW x mt0 Hx0 Hr').
  Qed.

  (* [comment removed for export] *)
  Lemma flm : forall x, In x l -> exists mtx, a_meta A x = Some mtx /\ mt_role mtx = RFree /\
    0x1000 <= x /\ x + 40 <= alloc_ceiling /\ (forall j, 0 <= j < 40 -> dom A (x + j)) /\
    exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ x = meta_addr pg k.
  Proof using HI Hfl xn xp. pu_keep (HI, Hfl, xn, xp).
    intros x Hx. destruct (fl_free x Hx) as (mtx & Hmx & Hrx). exists mtx. split; [exact Hmx|]. split; [exact Hrx|].
    destruct (proj1 (wf_meta_dom A HWp x) ltac:(rewrite Hmx; discriminate)) as (pg & k & Hpg & Hk & ->).
    destruct (wf_areas_al A HWp pg Hpg) as [Hpal Hph]. unfold heap_range in Hph.
    pose proof (meta_addr_range pg k Hk) as Hmr.
    split; [llia|]. split; [llia|]. split.
    - intros j Hj. left. exists pg. split; [exact Hpg | llia].
    - exists pg, k. auto.
  Qed.

  Lemma flm_img : forall x, In x l -> x + 40 <= IMG_LO \/ IMG_HI <= x.
  Proof using HI Hfl xn xp. pu_keep (HI, Hfl, xn, xp).
    intros x Hx. destruct (flm x Hx) as (_ & _ & _ & _ & _ & _ & pg & k & Hpg & Hk & ->).
    destruct (wf_areas_al A HWp pg Hpg) as [_ Hph]. unfold heap_range in Hph. pose proof (meta_addr_range pg k Hk). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma flm_apart : forall x y, In x l -> In y l -> x <> y -> x + 40 <= y \/ y + 40 <= x.
  Proof using HI Hfl xn xp. pu_keep (HI, Hfl, xn, xp).
    intros x y Hx Hy Hne. destruct (flm x Hx) as (mtx & Hmx & _). destruct (flm y Hy) as (mty & Hmy & _).
    destruct (other_meta_avoid_meta A HWp x mtx Hmx y mty FPrev Hmy ltac:(congruence)) as [H | H]; cbn in H; [right | left]; try llia.
    destruct (other_meta_avoid_meta A HWp y mty Hmy x mtx FPrev Hmx Hne) as [H' | H']; cbn in H'; llia.
  Qed.

  Lemma m_in : In m l. Proof using rest. pu_keep (rest). left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma single_links : rest = [] -> xn = m /\ xp = m.
  Proof using Type. pu_keep tt. intros Er. unfold xn, xp, n, l. rewrite Er. cbn. auto. Qed.

  Lemma multi_links : rest <> [] -> xn = hd 0 rest /\ In xn rest /\ In xp rest /\ xn <> m /\ xp <> m /\ (2 <= n)%nat.
  Proof using HI Hfl. pu_keep (HI, Hfl).
    intros Er. assert (E0' : exists r rest', rest = r :: rest').
    { clear - Er. destruct rest as [|r rest']; [exfalso; exact (Er eq_refl) | exists r, rest'; reflexivity]. }
    destruct E0' as (r & rest' & E0).
    assert (Hn : n = S (S (length rest'))) by (unfold n, l; rewrite E0; reflexivity).
    assert (Exn : xn = r).
    { unfold xn. rewrite Hn. rewrite Nat.mod_small by llia. unfold l. rewrite E0. reflexivity. }
    assert (Exp : In xp (r :: rest')).
    { unfold xp. rewrite Hn. replace ((0 + S (S (length rest')) - 1) mod S (S (length rest')))%nat with (S (length rest'))
        by (rewrite Nat.mod_small by llia; llia).
      unfold l. rewrite E0. destruct rest' as [|r1 rest'']; [left; reflexivity | right].
      change (In (nth (length rest'') (r1 :: rest'') 0) (r1 :: rest'')). apply nth_In. apply Nat.lt_succ_diag_r. }
    pose proof m_notin_rest as NI. rewrite E0 in NI.
    rewrite Exn, E0. cbn [hd]. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact Exp|].
    split; [intros E; apply NI; left; exact E|]. split; [intros E; apply NI; rewrite <- E; exact Exp | llia].
  Qed.

  (* [comment removed for export] *)
  Definition popCH (x : Z) : Prop :=
    m <= x < m + 16 \/ C_FMH <= x < C_FMH + 8 \/ (rest <> [] /\ (xn <= x < xn + 8 \/ xp + 8 <= x < xp + 16)).

  Lemma popV : exists mt0, a_meta A m = Some mt0 /\ (mt_role mt0 = RDead \/ mt_role mt0 = RFree) /\
    (mt_role (mzero RDead) = RDead \/ mt_role (mzero RDead) = RFree).
  Proof using HI Hfl xn xp. pu_keep (HI, Hfl, xn, xp). destruct m_meta as (mt & Hm & Hrm & _). exists mt. split; [exact Hm|]. split; [right; exact Hrm | left; reflexivity]. Qed.

  Lemma popA_victim : a_meta popA m = Some (mzero RDead).
  Proof using Type. pu_keep tt. rewrite popA_meta. apply g'_victim. Qed.

  Lemma popA_ctx : forall k, a_ctx popA k = MallocInv_wf3.c' A (a_active A) rest k.
  Proof using Type. pu_keep tt. reflexivity. Qed.

  Lemma c'_other : forall k, cvalid k -> k <> KFmh -> MallocInv_wf3.c' A (a_active A) rest k = a_ctx A k.
  Proof using HI. pu_keep (HI).
    intros k Hk Hne. destruct k; try reflexivity; [exfalso; exact (Hne eq_refl)|].
    cbn. symmetry. apply (wf_act_head A HWp). exact Hk.
  Qed.

  Lemma pop_commit : forall ws m4, RepW A (ms_mem s) ws m4 ->
    (forall x, wlook ws x <> None -> popCH x) ->
    (forall x, m <= x < m + 16 -> wlook ws x = Some 0) ->
    (forall x, C_FMH <= x < C_FMH + 8 -> wlook ws x = Some (byte_of (hd 0 rest) (x - C_FMH))) ->
    (rest <> [] -> forall x, xn <= x < xn + 8 -> wlook ws x = Some (byte_of xp (x - xn))) ->
    (rest <> [] -> forall x, xp + 8 <= x < xp + 16 -> wlook ws x = Some (byte_of xn (x - (xp + 8)))) ->
    Rep popA m4.
  Proof using HI Hfl MLok. pu_keep (HI, Hfl, MLok).
    intros ws m4 HRW HCH H0 H1 H2 H3.
    pose proof HWp as HW. pose proof WF_popA as HW2.
    destruct m_meta as (mt & Hm & Hrm & Hnx & Hpv & Z1 & Z2 & Z3 & Z4).
    apply (repw_commit A popA (ms_mem s) ws m4 HRW).
    - intros x b (f & Hf & Hfb).
      destruct (MallocInv_wf3.relists_has_inv A popP popN (a_active A) rest (Some (m, mzero RDead)) popV f Hf)
        as [(k & Hk & ->) | [Har | [(x0 & mt' & fl & Hx0 & ->) | Hg]]].
      + destruct (cslot_eq_dec k KFmh) as [-> | Hne].
        * right. destruct Hfb as [Hx _]. cbn in Hx. rewrite (H1 x) by (unfold C_FMH in *; llia). discriminate.
        * left. exists (FCT (caddr k) (clen k) (a_ctx A k)). split; [left; exists k; auto|].
          rewrite <- (c'_other k Hk Hne). exact Hfb.
      + left. exists f. split; [right; left; exact Har | exact Hfb].
      + destruct (Z.eq_dec x0 m) as [-> | Hne0].
        * rewrite g'_victim in Hx0. injection Hx0 as <-.
          destruct fl.
          1-2: right; destruct Hfb as [Hx _]; cbn in Hx; rewrite (H0 x) by llia; discriminate.
          all: left.
          -- exists (FCT (m + moff FMem) (mlen FMem) (mt_f mt FMem)). split; [right; right; left; exists m, mt, FMem; auto|].
             unfold mt_mem in Z1. rewrite Z1. exact Hfb.
          -- exists (FCT (m + moff FAvail) (mlen FAvail) (mt_f mt FAvail)). split; [right; right; left; exists m, mt, FAvail; auto|].
             unfold mt_avail in Z2. rewrite Z2. exact Hfb.
          -- exists (FCT (m + moff FFreed) (mlen FFreed) (mt_f mt FFreed)). split; [right; right; left; exists m, mt, FFreed; auto|].
             unfold mt_freed in Z3. rewrite Z3. exact Hfb.
          -- exists (FCT (m + moff FW32) (mlen FW32) (mt_f mt FW32)). split; [right; right; left; exists m, mt, FW32; auto|].
             unfold mt_w32 in Z4. rewrite Z4. exact Hfb.
        * destruct (pop_meta_inv x0 mt' Hx0 Hne0) as (mt0 & Hx0' & ->).
          assert (SAME : forall fl', fbyte (FCT (x0 + moff fl') (mlen fl') (mt_f mt0 fl')) x b -> facts A x b \/ wlook ws x <> None).
          { intros fl' Hfb'. left. exists (FCT (x0 + moff fl') (mlen fl') (mt_f mt0 fl')). split; [right; right; left; exists x0, mt0, fl'; auto | exact Hfb']. }
          destruct fl; [ | | apply (SAME FMem); exact Hfb | apply (SAME FAvail); exact Hfb | apply (SAME FFreed); exact Hfb | apply (SAME FW32); exact Hfb].
          -- unfold MallocInv_wf3.relink in Hfb. rewrite mt_f_MT in Hfb. cbn beta iota in Hfb. unfold popP in Hfb. destruct (Z.eqb_spec x0 xn) as [-> | Hnx'].
             ++ assert (Er : rest <> []) by (intros Er; destruct (single_links Er) as [E _]; exact (Hne0 E)).
                right. destruct Hfb as [Hx _]. cbn [moff mlen f_a f_n] in Hx. rewrite (H2 Er x) by llia. discriminate.
             ++ apply (SAME FPrev). exact Hfb.
          -- unfold MallocInv_wf3.relink in Hfb. rewrite mt_f_MT in Hfb. cbn beta iota in Hfb. unfold popN in Hfb. destruct (Z.eqb_spec x0 xp) as [-> | Hnp'].
             ++ assert (Er : rest <> []) by (intros Er; destruct (single_links Er) as [_ E]; exact (Hne0 E)).
                right. destruct Hfb as [Hx _]. cbn [moff mlen f_a f_n] in Hx. rewrite (H3 Er x) by llia. discriminate.
             ++ apply (SAME FNext). exact Hfb.
      + left. exists f. split; [right; right; right; exact Hg | exact Hfb].
    - intros x b (f & Hf & [Hx ->]) Hw. pose proof (HCH x Hw) as C.
      destruct C as [Cm | [Cf | (Er & [Cn | Cp])]].
      + rewrite (H0 x Cm). f_equal.
        destruct (Z.lt_ge_cases x (m + 8)) as [C0 | C8].
        * pose proof (fact_at_meta popA HW2 f m (mzero RDead) FPrev x Hf popA_victim Hx ltac:(cbn; llia)) as ->.
          cbn [f_a f_v]. rewrite mt_f_mzero, byte_of_zero. reflexivity.
        * pose proof (fact_at_meta popA HW2 f m (mzero RDead) FNext x Hf popA_victim Hx ltac:(cbn; llia)) as ->.
          cbn [f_a f_v]. rewrite mt_f_mzero, byte_of_zero. reflexivity.
      + rewrite (H1 x Cf). f_equal.
        pose proof (fact_at_ctx popA HW2 f KFmh x Hf I Hx ltac:(cbn; unfold C_FMH in *; llia)) as ->.
        cbn [f_a f_v caddr]. reflexivity.
      + rewrite (H2 Er x Cn). f_equal.
        destruct (multi_links Er) as (Exn & Hxn_in & Hxp_in & Hxnm & Hxpm & Hn2).
        destruct (flm xn xn_in) as (mtn & Hmn & _).
        assert (Hmn' : a_meta popA xn = Some (MallocInv_wf3.relink popP popN xn mtn)).
        { rewrite popA_meta, g'_nonvictim by exact Hxnm. rewrite Hmn. reflexivity. }
        pose proof (fact_at_meta popA HW2 f xn _ FPrev x Hf Hmn' Hx ltac:(cbn [moff mlen]; llia)) as ->.
        cbn [f_a f_v]. unfold MallocInv_wf3.relink. rewrite mt_f_MT. unfold popP. rewrite Z.eqb_refl. cbn [dflt moff]. f_equal. llia.
      + rewrite (H3 Er x Cp). f_equal.
        destruct (multi_links Er) as (Exn & Hxn_in & Hxp_in & Hxnm & Hxpm & Hn2).
        destruct (flm xp xp_in) as (mtp & Hmp & _).
        assert (Hmp' : a_meta popA xp = Some (MallocInv_wf3.relink popP popN xp mtp)).
        { rewrite popA_meta, g'_nonvictim by exact Hxpm. rewrite Hmp. reflexivity. }
        pose proof (fact_at_meta popA HW2 f xp _ FNext x Hf Hmp' Hx ltac:(cbn [moff mlen]; llia)) as ->.
        cbn [f_a f_v]. unfold MallocInv_wf3.relink. rewrite mt_f_MT. unfold popN. rewrite Z.eqb_refl. reflexivity.
    - intros x Hx. apply (proj1 (MallocInv_wf3.dom_relists A popP popN (a_active A) rest (Some (m, mzero RDead)) popV x)). exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma popCH_where : forall x, popCH x ->
    (C_FMH <= x < C_FMH + 8) \/ (dom A x /\ exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096).
  Proof using HI Hfl. pu_keep (HI, Hfl).
    assert (MLm : forall y x, In y l -> y <= x < y + 40 -> dom A x /\ exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096).
    { intros y x Hy Hx. destruct (flm y Hy) as (_ & _ & _ & _ & _ & Hd & pg & k & Hpg & Hk & ->).
      pose proof (meta_addr_range pg k Hk). split; [replace x with (meta_addr pg k + (x - meta_addr pg k)) by llia; apply Hd; llia|].
      exists pg. split; [exact Hpg | llia]. }
    intros x [Cm | [Cf | (Er & C2)]]; [right; apply (MLm m); [exact m_in | llia] | left; exact Cf |].
    destruct (multi_links Er) as (_ & Hxn_in & Hxp_in & _). right.
    destruct C2 as [Cn | Cp]; [apply (MLm xn); [exact (or_intror Hxn_in) | llia] | apply (MLm xp); [exact (or_intror Hxp_in) | llia]].
  Qed.

  Lemma pop_finish : forall (K : word -> M R) P m4,
    (forall s' A', IS sp0 argv envp cb A' s' -> VMok A' (ms_vm s') -> ms_vm s' = ms_vm s -> FR A s A' s' ->
       got_meta A D A' m -> a_areas A' = a_areas A -> a_ctx A' KAmc = a_ctx A KAmc -> a_freelist A' = rest ->
       (forall k, cvalid k -> k <> KFmh -> a_ctx A' k = a_ctx A k) ->
       a_pages A' = a_pages A -> a_mblocks A' = a_mblocks A -> a_xmaps A' = a_xmaps A ->
       tsafe (K (Z_to_bv 64 m) s') P) ->
    Rep popA m4 ->
    (forall a : word, m4 a = ms_mem s a \/ popCH (bv_unsigned a)) ->
    (forall a : word, ms_mem s a <> None -> m4 a <> None) ->
    tsafe (K (Z_to_bv 64 m) (upd s m4 (ms_vm s))) P.
  Proof using HAV HD HI HV Hfl MLok. pu_keep (HAV, HD, HI, HV, Hfl, MLok).
    intros K P m4 HK HR4 FRM KEEP. pose proof HI as [HW HR HC HWIN HE HG]. pose proof WF_popA as HW2.
    destruct m_meta as (mt & Hm & Hrm & Hnx & Hpv & Z1 & Z2 & Z3 & Z4).
    destruct (flm m m_in) as (mt_ & _ & _ & Hmlo & Hmhi & Hdom_m & _).
    pose proof alloc_ceiling_val as HCV.
    apply (HK _ popA).
    - (* [comment removed for export] *) apply (IS_mem sp0 argv envp cb A popA s m4 HI HW2 HR4).
      + intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. destruct (popCH_where _ X) as [Hc | (Hd & _)].
        * unfold mzone, C_FMH, CTX, CTX_END in *. llia.
        * destruct (dom_heap A (bv_unsigned a) HW Hd) as (lo & hi & Hh & Hx). unfold heap_range in Hh. unfold mzone. llia.
      + intros a Ha. destruct (FRM a) as [E | X]; [left; rewrite <- E; exact Ha|]. destruct (popCH_where _ X) as [Hc | (Hd & _)].
        * right; left. unfold C_FMH in Hc. llia.
        * left. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom A _ HR). exact Hd.
    - (* [comment removed for export] *) cbn [ms_vm upd]. apply (MallocInv_wf3.VMok_relists A popP popN (a_active A) rest (Some (m, mzero RDead)) popV). exact HV.
    - reflexivity.
    - (* [comment removed for export] *) apply (FR_memA A popA s m4 HW).
      + exact (MallocInv_wf3.dom_relists A popP popN (a_active A) rest (Some (m, mzero RDead)) popV).
      + reflexivity.
      + intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. destruct (popCH_where _ X) as [Hc | (Hd & pg & Hpg & Hx)].
        * left. unfold C_FMH, LOCKA, CTX_END in *. llia.
        * right; right. split; [exact Hd|]. intros p n0 Hp. exact (area_not_live A pg (bv_unsigned a) p n0 HW Hpg Hx Hp).
      + exact KEEP.
    - (* [comment removed for export] *) constructor.
      + exists (mzero RDead). split; [exact popA_victim|]. split; [reflexivity|]. intros fl; rewrite mt_f_mzero; reflexivity.
      + llia.
      + llia.
      + intros j Hj. apply (proj2 (MallocInv_wf3.dom_relists A popP popN (a_active A) rest (Some (m, mzero RDead)) popV (m + j))). apply Hdom_m. exact Hj.
      + intros x. split.
        * intros (mtx & Hx & Hrx). destruct (Z.eq_dec x m) as [-> | Hne]; [left; reflexivity | right].
          destruct (pop_meta_inv x mtx Hx Hne) as (mt0 & Hx0 & ->). cbn in Hrx. apply (proj1 (HD x)). exists mt0. auto.
        * intros [<- | Hin]; [exists (mzero RDead); split; [exact popA_victim | reflexivity]|].
          destruct (proj2 (HD x) Hin) as (mtx & Hx & Hrx).
          assert (Hne : x <> m) by (intros ->; rewrite Hm in Hx; injection Hx as <-; rewrite Hrm in Hrx; discriminate Hrx).
          exists (MallocInv_wf3.relink popP popN x mtx). rewrite popA_meta, g'_nonvictim by exact Hne. rewrite Hx. split; [reflexivity | exact Hrx].
      + intros Hin. destruct (proj2 (HD m) Hin) as (mtx & Hx & Hrx). rewrite Hm in Hx. injection Hx as <-. rewrite Hrm in Hrx. discriminate Hrx.
      + constructor.
        * intros x mtx aib sl Hx Hrx. rewrite popA_meta.
          rewrite (MallocInv_wf3.g'_of_group A popP popN (Some (m, mzero RDead)) popV x mtx aib sl Hx Hrx).
          rewrite (relink_nonfree x mtx Hx) by (rewrite Hrx; discriminate). destruct mtx; reflexivity.
        * intros x mtx aib sl Hx Hrx.
          destruct (MallocInv_wf3.g'_group A popP popN (Some (m, mzero RDead)) popV x mtx aib sl Hx Hrx) as (mt0 & Hx0 & Hr0 & ->).
          rewrite (relink_nonfree x mt0 Hx0) by (rewrite Hr0; discriminate). destruct mt0; exact Hx0.
        * intros x mtx Hx Hrx. assert (Hne : x <> m) by (intros ->; rewrite Hm in Hx; injection Hx as <-; rewrite Hrm in Hrx; discriminate Hrx).
          rewrite popA_meta, g'_nonvictim by exact Hne. rewrite Hx. cbn [option_map].
          rewrite (relink_nonfree x mtx Hx) by (rewrite Hrx; discriminate). destruct mtx; reflexivity.
        * intros sc. reflexivity.
        * reflexivity.
        * intros k Hk Hv. rewrite popA_ctx. apply c'_other; [exact Hv|]. destruct k; cbn in Hk; try contradiction; discriminate.
      + intros x mtx Hx Hrx. assert (Hne : x <> m) by (intros ->; rewrite popA_victim in Hx; injection Hx as <-; discriminate Hrx).
        destruct (pop_meta_inv x mtx Hx Hne) as (mt0 & Hx0 & ->). cbn in Hrx. destruct (HAV x mt0 Hx0 Hrx) as (k & Hk & Ex).
        exists k. exact (conj Hk Ex).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros k Hk Hne. rewrite popA_ctx. apply c'_other; assumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem pop_ok : forall (K : word -> M R) P,
    (forall s' A', IS sp0 argv envp cb A' s' -> VMok A' (ms_vm s') -> ms_vm s' = ms_vm s -> FR A s A' s' ->
       got_meta A D A' m -> a_areas A' = a_areas A -> a_ctx A' KAmc = a_ctx A KAmc -> a_freelist A' = rest ->
       (forall k, cvalid k -> k <> KFmh -> a_ctx A' k = a_ctx A k) ->
       a_pages A' = a_pages A -> a_mblocks A' = a_mblocks A -> a_xmaps A' = a_xmaps A ->
       tsafe (K (Z_to_bv 64 m) s') P) ->
    tsafe ((x <- (nx <- m_ld (at_ (Z_to_bv 64 m) 8) ;;
                  (if c_eq nx (Z_to_bv 64 m) then m_sd A_FREE_META_HEAD w0
                   else pv <- m_ld (Z_to_bv 64 m) ;;
                        m_sd (at_ pv 8) nx ;;
                        pv2 <- m_ld (Z_to_bv 64 m) ;;
                        nx2 <- m_ld (at_ (Z_to_bv 64 m) 8) ;;
                        m_sd nx2 pv2 ;;
                        h <- m_ld A_FREE_META_HEAD ;;
                        (if c_eq h (Z_to_bv 64 m) then n3 <- m_ld (at_ (Z_to_bv 64 m) 8) ;; m_sd A_FREE_META_HEAD n3
                         else mret tt)) ;;
                  m_sd (at_ (Z_to_bv 64 m) 8) w0 ;; m_sd (Z_to_bv 64 m) w0 ;;
                  mret (Z_to_bv 64 m)) ;; K x) s) P.
  Proof using HAV HD HI HV Hfl MLok. pu_keep (HAV, HD, HI, HV, Hfl, MLok).
    intros K P HK. pose proof HI as [HW HR HC HWIN HE HG].
    destruct m_meta as (mt & Hm & Hrm & Hnx & Hpv & Z1 & Z2 & Z3 & Z4).
    destruct (flm m m_in) as (mt_ & _ & _ & Hmlo & Hmhi & Hdom_m & _).
    pose proof (flm_img m m_in) as Hmimg.
    pose proof alloc_ceiling_val as HCV.
    assert (Hxn0 : 0 <= xn) by (destruct (flm xn xn_in) as (mt1 & H1 & H2 & H3 & H4); llia).
    assert (Hxp0 : 0 <= xp) by (destruct (flm xp xp_in) as (mt1 & H1 & H2 & H3 & H4); llia).
    assert (Hfn : has A (FCT (m + 8) 8 xn)).
    { right; right; left. exists m, mt, FNext. split; [exact Hm|]. unfold mt_next in Hnx. rewrite <- Hnx. reflexivity. }
    assert (Hfp : has A (FCT m 8 xp)).
    { right; right; left. exists m, mt, FPrev. split; [exact Hm|]. unfold mt_prev in Hpv. rewrite <- Hpv. cbn [moff mlen]. rewrite Z.add_0_r. reflexivity. }
    assert (Hfh : has A (FCT (caddr KFmh) 8 m)).
    { left. exists KFmh. split; [exact I|]. rewrite (wf_fl_head A HW), Hfl. reflexivity. }
    pose proof (repw_init A _ HW HR) as RW0.
    apply ts_assoc. rewrite at_Z.
    eapply (ts_ld_factw A HW s (ms_mem s) [] (m + 8) xn); [exact RW0 | exact HWIN | exact Hfn | apply wfree_range_nil | llia |].
    cbv beta.
    destruct (list_eq_dec Z.eq_dec rest []) as [Er | Er].
    - (* [comment removed for export] *)
      destruct (single_links Er) as [Exn Exp].
      replace (c_eq (Z_to_bv 64 xn) (Z_to_bv 64 m)) with true by (rewrite Exn, c_eq_Z by llia; rewrite Z.eqb_refl; reflexivity).
      cbv iota. apply ts_assoc.
      rewrite A_FREE_META_HEAD_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A s (ms_mem s) []); [exact RW0 | exact HWIN | exact I |].
      pose proof (repw_st_ctx A s (ms_mem s) [] KFmh w0 RW0 I) as RW1.
      set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (caddr KFmh)) (word_to_le_bytes (Z.to_nat (clen KFmh)) w0)) in RW1 |- *.
      apply ts_assoc. unfold m_sd at 1. rewrite ?at_Z.
      eapply (ts_st_domw A HW (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (m + 8 + j) with (m + (8 + j)) by llia; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m1 (ms_vm s)) (ms_mem s) _ 8 (m + 8) w0 RW1 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (m + 8 + j) with (m + (8 + j)) by llia; apply Hdom_m; llia)) as RW2.
      cbn [ms_mem upd] in RW2.
      set (m2 := wbytes m1 (Z_to_bv 64 (m + 8)) (word_to_le_bytes 8 w0)) in RW2 |- *.
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_domw A HW (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m2 (ms_vm s)) (ms_mem s) _ 8 m w0 RW2 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom_m; llia)) as RW3.
      cbn [ms_mem upd] in RW3.
      set (m3 := wbytes m2 (Z_to_bv 64 m) (word_to_le_bytes 8 w0)) in RW3 |- *.
      apply ts_bind_ret. apply (pop_finish K P m3 HK).
      + apply (pop_commit _ m3 RW3).
        * intros x Hw. unfold popCH.
          assert (DQrng : m <= x < (m + 16) \/ C_FMH <= x < (C_FMH + 8) \/
                         (~ (m <= x < (m + 16)) /\ ~ (C_FMH <= x < (C_FMH + 8)))) by lia.
          destruct DQrng as [DQrng | [DQrng | DQrng]];
            [ left; llia
            | right; left; llia |].
           
            exfalso; apply Hw; cbn [f_a f_n f_v caddr clen Z.of_nat Z.to_nat Pos.to_nat] in *; unfold C_FMH in *; rewrite !wlook_skip by (cbn [f_a f_n]; llia); reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_FMH in *.
          destruct (Z.lt_ge_cases x (m + 8)).
          -- rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
          -- rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
             replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_FMH in *.
          rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
          replace (bv_unsigned w0) with 0 by reflexivity. rewrite Er. cbn [hd]. reflexivity.
        * intros Er'. exfalso. exact (Er' Er).
        * intros Er'. exfalso. exact (Er' Er).
      + intros a. pose proof (u64_range a). unfold popCH.
        assert (DQrng : m <= (bv_unsigned a) < (m + 16) \/ C_FMH <= (bv_unsigned a) < (C_FMH + 8) \/
                       (~ (m <= (bv_unsigned a) < (m + 16)) /\ ~ (C_FMH <= (bv_unsigned a) < (C_FMH + 8)))) by lia.
        destruct DQrng as [DQrng | [DQrng | DQrng]];
          [ right; left; llia
          | right; right; left; llia |].
         
          left; unfold m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *; unfold C_FMH in *;
          rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn; llia); reflexivity.
      + intros a Ha. unfold m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat]. unfold C_FMH.
        repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|]). exact Ha.
    - (* [comment removed for export] *)
      destruct (multi_links Er) as (Exn & Hxn_in & Hxp_in & Hxnm & Hxpm & Hn2).
      destruct (flm xn xn_in) as (mtn & Hmn & Hrn & Hxnlo & Hxnhi & Hdom_xn & _).
      destruct (flm xp xp_in) as (mtp & Hmp & Hrp & Hxplo & Hxphi & Hdom_xp & _).
      pose proof (flm_img xn xn_in) as Hxnimg. pose proof (flm_img xp xp_in) as Hxpimg.
      pose proof (flm_apart m xn m_in xn_in ltac:(intros E; exact (Hxnm (eq_sym E)))) as Dmn.
      pose proof (flm_apart m xp m_in xp_in ltac:(intros E; exact (Hxpm (eq_sym E)))) as Dmp.
      assert (Dnp : xn = xp \/ xn + 40 <= xp \/ xp + 40 <= xn).
      { destruct (Z.eq_dec xn xp) as [E | Hne]; [left; exact E | right]. exact (flm_apart xn xp xn_in xp_in Hne). }
      replace (c_eq (Z_to_bv 64 xn) (Z_to_bv 64 m)) with false by (rewrite c_eq_Z by llia; symmetry; apply Z.eqb_neq; exact Hxnm).
      cbv iota. apply ts_assoc. apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW s (ms_mem s) [] m xp); [exact RW0 | exact HWIN | exact Hfp | apply wfree_range_nil | llia |].
      cbv beta. apply ts_assoc. unfold m_sd at 1. rewrite at_Z.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW s (ms_mem s) []); [exact RW0 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (xp + 8 + j) with (xp + (8 + j)) by llia; apply Hdom_xp; llia |].
      pose proof (repw_st_dom A HW s (ms_mem s) [] 8 (xp + 8) (Z_to_bv 64 xn) RW0 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (xp + 8 + j) with (xp + (8 + j)) by llia; apply Hdom_xp; llia)) as RW1.
      rewrite uZ in RW1 by llia.
      set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (xp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 xn))) in RW1 |- *.
      cbn [ms_mem ms_vm upd]. apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW (upd s m1 (ms_vm s)) (ms_mem s) _ m xp); [exact RW1 | apply WIN_upd; exact HWIN | exact Hfp | apply wfree_range_cons; [cbn [f_a f_n]; llia | apply wfree_range_nil] | llia |].
      cbv beta. apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW (upd s m1 (ms_vm s)) (ms_mem s) _ (m + 8) xn); [exact RW1 | apply WIN_upd; exact HWIN | exact Hfn | apply wfree_range_cons; [cbn [f_a f_n]; llia | apply wfree_range_nil] | llia |].
      cbv beta. apply ts_assoc. unfold m_sd at 1.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom_xn; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m1 (ms_vm s)) (ms_mem s) _ 8 xn (Z_to_bv 64 xp) RW1 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom_xn; llia)) as RW2.
      cbn [ms_mem upd] in RW2. rewrite uZ in RW2 by llia.
      set (m2 := wbytes m1 (Z_to_bv 64 xn) (word_to_le_bytes 8 (Z_to_bv 64 xp))) in RW2 |- *.
      apply ts_assoc.
      (* [comment removed for export] *)
      rewrite A_FREE_META_HEAD_eq.
      eapply (ts_ld_factw A HW (upd s m2 (ms_vm s)) (ms_mem s) _ (caddr KFmh) m); [exact RW2 | apply WIN_upd; exact HWIN | exact Hfh | | llia |].
      { apply wfree_range_cons; [cbn [f_a f_n caddr]; unfold C_FMH; llia|]. apply wfree_range_cons; [cbn [f_a f_n caddr]; unfold C_FMH; llia|]. apply wfree_range_nil. }
      cbv beta. rewrite c_eq_Z by llia. rewrite Z.eqb_refl. cbv iota. apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW (upd s m2 (ms_vm s)) (ms_mem s) _ (m + 8) xn); [exact RW2 | apply WIN_upd; exact HWIN | exact Hfn | | llia |].
      { apply wfree_range_cons; [cbn [f_a f_n]; llia|]. apply wfree_range_cons; [cbn [f_a f_n]; llia|]. apply wfree_range_nil. }
      cbv beta. unfold m_sd at 1.
      (* [comment removed for export] *)
      eapply (ts_st_ctxw A (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | apply WIN_upd; exact HWIN | exact I |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m2 (ms_vm s)) (ms_mem s) _ KFmh (Z_to_bv 64 xn) RW2 I) as RW3.
      cbn [ms_mem upd] in RW3. rewrite uZ in RW3 by llia.
      set (m3 := wbytes m2 (Z_to_bv 64 (caddr KFmh)) (word_to_le_bytes (Z.to_nat (clen KFmh)) (Z_to_bv 64 xn))) in RW3 |- *.
      apply ts_assoc. unfold m_sd at 1.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW (upd s m3 (ms_vm s)) (ms_mem s)); [exact RW3 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (m + 8 + j) with (m + (8 + j)) by llia; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m3 (ms_vm s)) (ms_mem s) _ 8 (m + 8) w0 RW3 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (m + 8 + j) with (m + (8 + j)) by llia; apply Hdom_m; llia)) as RW4.
      cbn [ms_mem upd] in RW4.
      set (m4 := wbytes m3 (Z_to_bv 64 (m + 8)) (word_to_le_bytes 8 w0)) in RW4 |- *.
      apply ts_assoc. unfold m_sd at 1.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW (upd s m4 (ms_vm s)) (ms_mem s)); [exact RW4 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m4 (ms_vm s)) (ms_mem s) _ 8 m w0 RW4 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom_m; llia)) as RW5.
      cbn [ms_mem upd] in RW5.
      set (m5 := wbytes m4 (Z_to_bv 64 m) (word_to_le_bytes 8 w0)) in RW5 |- *.
      apply ts_bind_ret. apply (pop_finish K P m5 HK).
      + apply (pop_commit _ m5 RW5).
        * intros x Hw. unfold popCH.
          assert (DQrng : m <= x < (m + 16) \/ C_FMH <= x < (C_FMH + 8) \/ xn <= x < (xn + 8) \/ (xp + 8) <= x < (xp + 16) \/
                         (~ (m <= x < (m + 16)) /\ ~ (C_FMH <= x < (C_FMH + 8)) /\ ~ (xn <= x < (xn + 8)) /\ ~ ((xp + 8) <= x < (xp + 16)))) by lia.
          destruct DQrng as [DQrng | [DQrng | [DQrng | [DQrng | DQrng]]]];
            [ left; llia
            | right; left; llia
            | right; right; split; [exact Er | left; llia]
            | right; right; split; [exact Er | right; llia] |].
           
            exfalso; apply Hw; cbn [f_a f_n f_v caddr clen Z.of_nat Z.to_nat Pos.to_nat] in *; unfold C_FMH in *; rewrite !wlook_skip by (cbn [f_a f_n]; llia); reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_FMH in *.
          destruct (Z.lt_ge_cases x (m + 8)).
          -- rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
          -- rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
             replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_FMH in *.
          rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite Exn. reflexivity.
        * intros _ x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_FMH in *.
          rewrite 3!wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
        * intros _ x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_FMH in *.
          rewrite 4!wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
      + intros a. pose proof (u64_range a). unfold popCH.
        assert (DQrng : m <= (bv_unsigned a) < (m + 16) \/ C_FMH <= (bv_unsigned a) < (C_FMH + 8) \/ xn <= (bv_unsigned a) < (xn + 8) \/ (xp + 8) <= (bv_unsigned a) < (xp + 16) \/
                       (~ (m <= (bv_unsigned a) < (m + 16)) /\ ~ (C_FMH <= (bv_unsigned a) < (C_FMH + 8)) /\ ~ (xn <= (bv_unsigned a) < (xn + 8)) /\ ~ ((xp + 8) <= (bv_unsigned a) < (xp + 16)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | [DQrng | DQrng]]]];
          [ right; left; llia
          | right; right; left; llia
          | right; right; right; split; [exact Er | left; llia]
          | right; right; right; split; [exact Er | right; llia] |].
         
          left; unfold m5, m4, m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *; unfold C_FMH in *;
          rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; llia); reflexivity.
      + intros a Ha. unfold m5, m4, m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat]. unfold C_FMH.
        repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by llia; llia|]). exact Ha.
  Qed.
End Pop.

End WithLayout.
