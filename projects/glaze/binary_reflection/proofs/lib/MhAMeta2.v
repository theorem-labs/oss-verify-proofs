(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition cx_set_avail (cx : ctx_rec) (am cnt : Z) : ctx_rec :=
  CX (c_secret cx) (c_mmap_ctr cx) (c_free_head cx) am cnt (c_area_cnt cx) (c_shift cx) (c_area_head cx) (c_area_tail cx)
     (c_cursor cx) (c_active cx) (c_usage cx) (c_unmap_seq cx) (c_bounces cx) (c_seq cx) (c_brk cx).

Section Fresh.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hfl : s_flist st = [].
  #[local] Notation cx := (s_ctx st).
  #[local] Notation cnt := (c_avail_cnt (s_ctx st)).
  #[local] Notation areas := (s_areas st).
  Hypothesis Hcnt : cnt > 0.
  Definition m : Z := meta_addr (last areas 0) (NSLOTS - cnt).

  Definition st' : mst :=
    MST (cx_set_avail cx (m + 40) (cnt - 1))
        areas (s_meta st) [] (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (m :: s_limbo st).

  Lemma am_val : c_avail_meta cx = m /\ areas <> [].
  Proof. destruct (wc_ameta st (WF_ctx st L HWF) Hcnt) as [A B]. split; [exact B | exact A]. Qed.
  Lemma cnt_rng : 0 < cnt <= NSLOTS - 1.
  Proof. pose proof (wc_acnt st (WF_ctx st L HWF)). lia. Qed.
  Lemma last_in : In (last areas 0) areas.
  Proof.
    destruct am_val as [_ NE]. rewrite (app_removelast_last 0 NE) at 2. apply in_app_iff. right. left. reflexivity.
  Qed.
  Lemma m_fresh : fresh st m.
  Proof. split; [exact Hcnt|]. exists (NSLOTS - cnt). split; [pose proof cnt_rng; lia | reflexivity]. Qed.
  Lemma m_U : metaU st m.
  Proof. exists (last areas 0), (NSLOTS - cnt). pose proof cnt_rng. split; [exact last_in|]. split; [lia | reflexivity]. Qed.
  Lemma m_zero : s_meta st m = meta_zero.
  Proof. exact (wG_fresh0 st L (WF_groups st L HWF) m m_fresh). Qed.
  Lemma m_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL.
  Proof. destruct (metaU_rng st L HWF m m_U) as (A & B & _). lia. Qed.
  Lemma o_in_flist : forall x, ~ in_flist st x. Proof. intros x H. unfold in_flist in H. rewrite Hfl in H. exact H. Qed.
  Lemma fresh_not_group : forall x, fresh st x -> ~ is_group st x.
  Proof. intros x F G. exact (wg_notfresh st L x (wG_each st L (WF_groups st L HWF) x G) F). Qed.
  Lemma fresh_not_listed : forall x, fresh st x -> ~ listed st x.
  Proof.
    intros x F [A|(sc & Hsc & Hin)]; [exact (o_in_flist x A)|].
    exact (fresh_not_group x F (proj1 (proj2 (alist_member st L HWF sc x Hin)))).
  Qed.

  Lemma e_fresh : forall x, fresh st' x <-> fresh st x /\ x <> m.
  Proof.
    intros x. unfold fresh. cbn [s_ctx st' c_avail_cnt cx_set_avail s_areas]. pose proof cnt_rng as CR. split.
    - intros [A (k & Hk & E)]. split; [split; [lia|]; exists k; split; [lia | exact E]|].
      intros ->. unfold m, meta_addr, META_SZ in E. lia.
    - intros [[A (k & Hk & E)] NE]. split.
      + destruct (Z.eq_dec k (NSLOTS - cnt)) as [->|Hk']; [exfalso; apply NE; rewrite E; reflexivity | lia].
      + exists k. split; [|exact E]. destruct (Z.eq_dec k (NSLOTS - cnt)) as [->|Hk']; [exfalso; apply NE; rewrite E; reflexivity | lia].
  Qed.

  Lemma SLf : same_layout st st'.
  Proof. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.

  Lemma e_listed : forall x, listed st' x <-> listed st x.
  Proof.
    intros x. unfold listed, in_flist, in_alist. cbn [s_flist s_alist st']. rewrite Hfl. tauto.
  Qed.

  Lemma t_WF : WF st' L.
  Proof.
    pose proof cnt_rng as CR. destruct am_val as [AM NE].
    split.
    { destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
      constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of Z.of_nat m]; try assumption.
      - rewrite A3, Hfl. reflexivity.
      - lia.
      - intros Hg. split; [exact NE|]. unfold m, meta_addr, META_SZ. lia. }
    split; [exact (wf_areas_ext st st' SLf (WF_areas st L HWF))|].
    split.
    { destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
      constructor; cbn [s_flist s_alist s_meta st']; try assumption.
      - intros k Hk. rewrite zlen_nil in Hk. lia.
      - constructor.
      - intros x [].
      - intros x U NL. apply LK; [exact U|]. rewrite <- e_listed. exact NL.
      - intros x Hl. apply LKD. rewrite <- e_listed. exact Hl. }
    split.
    { destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
      constructor; cbn [s_groups s_limbo s_regions s_meta s_kind s_slot s_ai st']; try assumption.
      - intros x Hx. pose proof (EACH x Hx) as WG.
        destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
        constructor; rewrite ?(x_gW st st' SLf), ?(x_gmem st st' SLf), ?(x_glast st st' SLf), ?(x_gcnt st st' SLf), ?(x_gsc st st' SLf),
          ?(x_gml st st' SLf), ?(x_gstride st st' SLf) by exact Hx; cbn [s_meta s_ai s_kind s_slot s_alist s_flist s_regions st']; try assumption.
        + rewrite e_fresh. intros [F _]. exact (NF F).
        + intros [].
        + intros H63 Hl. apply (S63 H63). apply e_listed. exact Hl.
        + intros Hall Hne Hl. apply (Full Hall Hne). apply e_listed. exact Hl.
      - intros x F. apply e_fresh in F. exact (FR0 x (proj1 F)).
      - intros x U NG NFL NFR. rewrite e_fresh in NFR.
        destruct (Z.eq_dec x m) as [->|Hxm]; [left; reflexivity|]. right.
        apply (OTH x U NG (o_in_flist x)). intros F. apply NFR. split; assumption.
      - intros x [<-|Hl].
        + rewrite e_fresh, e_listed. split; [exact m_U|]. split; [exact (fresh_not_group m m_fresh)|].
          split; [exact (fresh_not_listed m m_fresh)|]. intros [_ X]. exact (X eq_refl).
        + destruct (LIM x Hl) as (A & B & C & D). rewrite e_fresh, e_listed. repeat split; try assumption. intros [X _]. exact (D X). }
    split; [exact (wf_geom_ext st st' L SLf HWF (WF_geom st L HWF))|].
    split; [exact (wf_live_ext st st' L SLf (WF_live st L HWF)) |]. split; [exact (wf_regions_ext st st' L SLf HWF eq_refl (WF_regions st L HWF)) | exact (wf_img_ext st st' SLf (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition f_wr (a : Z) : Prop :=
    (sp - MSTK <= a < sp) \/ (m <= a < m + 16) \/ (ctx_avail_meta <= a < ctx_avail_meta + 16).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> f_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMm0 : cell M' m 8 0.
  Hypothesis HMm8 : cell M' (m + 8) 8 0.
  Hypothesis HMam : cell M' ctx_avail_meta 8 (m + 40).
  Hypothesis HMamc : cell M' ctx_avail_meta_count 8 (cnt - 1).

  Lemma t_REP : REP st' M'.
  Proof.
    pose proof m_rng as [MR1 MR2]. pose proof m_U as Um.
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[W|W]]; ceil; unfold MSTK, HEAPLO, ctx_avail_meta, CTX in *; lia.
    - pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
      assert (TR : forall a k v, CTX <= a -> a + Z.of_nat k <= CTX_END ->
                (a + Z.of_nat k <= ctx_avail_meta \/ ctx_avail_meta + 16 <= a) -> cell M a k v -> cell M' a k v).
      { intros a k v H1 H2 H3 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; cbn; lia | | exact C].
        intros b Hr Hb. destruct (decide (M' (Z_to_bv 64 b) = M (Z_to_bv 64 b))) as [E|NE]; [exact E|]. exfalso.
        destruct (HMwr b Hr NE) as [W|[W|W]]; ceil; unfold MSTK, HEAPLO, ctx_avail_meta, CTX_END, CTX in *; lia. }
      Ltac ctxg TR := eapply TR; [ cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
                 ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
                 ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
               | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
                 ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
                 ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
               | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
                 ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
                 ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
               | eauto ].
      constructor; cbn [s_ctx st' cx_set_avail c_secret c_mmap_ctr c_free_head c_avail_meta c_avail_cnt c_area_cnt c_shift c_area_head c_area_tail
                        c_cursor c_active c_usage c_unmap_seq c_bounces c_seq c_brk]; try assumption; try (ctxg TR).
      + intros sc Hsc. ctxg TR.
      + intros sc Hsc. ctxg TR.
      + intros i Hi. ctxg TR.
      + intros i Hi. ctxg TR.
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) (fun x => x =? m)); try reflexivity.
      + intros ar a Har Ha NE. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (HMwr a ltac:(ceil; unfold HEAPLO in *; lia) NE) as [W|[W|W]].
        * ceil; unfold MSTK in *; lia.
        * exists m. rewrite Z.eqb_refl. split; [exact m_U|]. split; [reflexivity | lia].
        * unfold ctx_avail_meta, CTX, HEAPLO in *; lia.
      + intros x Ux X. apply Z.eqb_eq in X. subst x. cbn [s_meta st']. rewrite m_zero.
        pose proof (metaU_area st L HWF m m_U) as (ar & k & Har & Hk & Hxa & _).
        pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hxa, m_zero in RM.
        destruct RM as [P N Me Av Fr Wc].
        assert (AG : agree_on (fun a => m + 16 <= a < m + 40) M M').
        { intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          destruct (HMwr a Hr NE) as [W|[W|W]]; ceil; unfold MSTK, HEAPLO, ctx_avail_meta, CTX in *; lia. }
        constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W meta_zero].
        * exact HMm0.
        * exact HMm8.
        * eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
        * eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
        * eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
        * eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)).
      + intros x Hx. exact Hx.
      + intros x Hx. repeat split; reflexivity.
      + intros x Hx E. apply (x_endb st st' L SLf HWF); [exact Hx | exact E].
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. apply (x_gcell st st' L SLf HWF) in G; [|exact Hx].
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (HMwr a ltac:(ceil; unfold HEAPLO in *; lia) NE) as [W|[W|W]].
        * ceil; unfold MSTK in *; lia.
        * exact (gcell_not_meta st L HWF x m a Hx G m_U ltac:(lia)).
        * unfold ctx_avail_meta, CTX, HEAPLO in *; lia.
      + intros x a Hx G. left. apply (x_gcell st st' L SLf HWF); [exact Hx | exact G].
  Qed.

  Theorem fresh_close : WF st' L /\ REP st' M'.
  Proof. split; [exact t_WF | exact t_REP]. Qed.
End Fresh.
