(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition cx_set_policy (cx : ctx_rec) (u q b : Z -> Z) (sq : Z) : ctx_rec :=
  CX (c_secret cx) (c_mmap_ctr cx) (c_free_head cx) (c_avail_meta cx) (c_avail_cnt cx)
     (c_area_cnt cx) (c_shift cx) (c_area_head cx) (c_area_tail cx) (c_cursor cx)
     (c_active cx) u q b sq (c_brk cx).

Section Policy.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (sp : Z).
  Variables (u' q' b' : Z -> Z) (seq' : Z).
  Variable WS : Z -> Prop.   (* [comment removed for export] *)
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hu : forall sc, 0 <= u' sc < 2 ^ 64.
  Hypothesis Hq : forall i, 0 <= q' i < 256.
  Hypothesis Hb : forall i, 0 <= b' i < 256.
  Hypothesis Hseq : 0 <= seq' < 256.
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    (sp - MSTK <= a < sp) \/ (CTX + 464 <= a < CTX + 913 /\ WS a).
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMu : forall sc, 0 <= sc < 48 ->
    cell M' (ctx_usage sc) 8 (u' sc) \/ (u' sc = c_usage (s_ctx st) sc /\ forall a, ctx_usage sc <= a < ctx_usage sc + 8 -> ~ WS a).
  Hypothesis HMq : forall i, 0 <= i < 32 ->
    cell M' (ctx_unmap_seq i) 1 (q' i) \/ (q' i = c_unmap_seq (s_ctx st) i /\ ~ WS (ctx_unmap_seq i)).
  Hypothesis HMb : forall i, 0 <= i < 32 ->
    cell M' (ctx_bounces i) 1 (b' i) \/ (b' i = c_bounces (s_ctx st) i /\ ~ WS (ctx_bounces i)).
  Hypothesis HMs : cell M' ctx_seq 1 seq' \/ (seq' = c_seq (s_ctx st) /\ ~ WS ctx_seq).

  Definition st' : mst :=
    MST (cx_set_policy (s_ctx st) u' q' b' seq')
        (s_areas st) (s_meta st) (s_flist st) (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).

  Lemma SLp : same_layout st st'.
  Proof. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.

  Lemma t_WF : WF st' L.
  Proof.
    pose proof HWF as (C & A & Ls & G & Ge & Lv & R & WI).
    split.
    { destruct C; constructor; assumption. }
    split; [exact (wf_areas_ext st st' SLp A)|].
    split.
    { destruct Ls; constructor; assumption. }
    split.
    { destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      intros x Hx. pose proof (EACH x Hx) as WG. destruct WG; constructor; assumption. }
    split; [exact (wf_geom_ext st st' L SLp HWF Ge)|].
    split; [exact (wf_live_ext st st' L SLp Lv) |]. split; [exact (wf_regions_ext st st' L SLp HWF eq_refl R) | exact (wf_img_ext st st' SLp (WF_img st L HWF))].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof.
    assert (WR : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> CEIL <= a \/ (CTX + 464 <= a < CTX + 913 /\ WS a)).
    { intros a Hr NE. destruct (HMwr a Hr NE) as [W|W]; [left; ceil; unfold MSTK in *; lia | right; exact W]. }
    assert (AGof : forall P : Z -> Prop, (forall a, P a -> CEIL <= a -> False) -> (forall a, P a -> CTX + 464 <= a < CTX + 913 -> WS a -> False) -> agree_on P M M').
    { intros P H1 H2 a Hr Pa. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (WR a Hr NE) as [W|[W1 W2]]; [exact (H1 a Pa W) | exact (H2 a Pa W1 W2)]. }
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      apply AGof; [intros a Pa C; ceil; unfold CTX in *; lia | intros a Pa W _; unfold CTX in *; lia].
    - pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
      assert (TR : forall a k v, CTX <= a -> (a + Z.of_nat k <= CTX + 464 \/ CTX + 913 <= a) -> a + Z.of_nat k <= CTX_END -> cell M a k v -> cell M' a k v).
      { intros a k v H1 H2 H3 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; lia | | exact C].
        apply AGof; [cbn; intros bb Hbb Cb; ceil; unfold CTX_END, CTX in *; lia | cbn; intros bb Hbb W _; lia]. }
      Ltac ctxf TR := eapply TR; [ cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_brk, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_brk, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_brk, CTX_END, CTX; lia
             | eauto ].
      constructor; cbn [s_ctx st' cx_set_policy c_secret c_mmap_ctr c_free_head c_avail_meta c_avail_cnt c_area_cnt c_shift
                        c_area_head c_area_tail c_cursor c_active c_usage c_unmap_seq c_bounces c_seq c_brk]; try (ctxf TR).
      + intros sc Hsc. ctxf TR.
      + intros sc Hsc. destruct (HMu sc Hsc) as [Cl|[E NW]]; [exact Cl|]. rewrite E.
        eapply cell_agree; [unfold ctx_usage, CTX; lia | unfold ctx_usage, CTX; cbn; lia | | exact (C13 sc Hsc)].
        apply AGof; [cbn; intros bb Hbb Cb; ceil; unfold ctx_usage, CTX in *; lia | cbn; intros bb Hbb _ W; exact (NW bb Hbb W)].
      + intros i Hi. destruct (HMq i Hi) as [Cl|[E NW]]; [exact Cl|]. rewrite E.
        eapply cell_agree; [unfold ctx_unmap_seq, CTX; lia | unfold ctx_unmap_seq, CTX; cbn; lia | | exact (C14 i Hi)].
        apply AGof; [cbn; intros bb Hbb Cb; ceil; unfold ctx_unmap_seq, CTX in *; lia | cbn; intros bb Hbb _ W].
        assert (bb = ctx_unmap_seq i) by (unfold ctx_unmap_seq in *; lia). subst bb. exact (NW W).
      + intros i Hi. destruct (HMb i Hi) as [Cl|[E NW]]; [exact Cl|]. rewrite E.
        eapply cell_agree; [unfold ctx_bounces, CTX; lia | unfold ctx_bounces, CTX; cbn; lia | | exact (C15 i Hi)].
        apply AGof; [cbn; intros bb Hb0 Cb; ceil; unfold ctx_bounces, CTX in *; lia | cbn; intros bb Hb0 _ W].
        assert (bb = ctx_bounces i) by (unfold ctx_bounces in *; lia). subst bb. exact (NW W).
      + destruct HMs as [Cl|[E NW]]; [exact Cl|]. rewrite E.
        eapply cell_agree; [unfold ctx_seq, CTX; lia | unfold ctx_seq, CTX; cbn; lia | | exact C16].
        apply AGof; [cbn; intros bb Hb0 Cb; ceil; unfold ctx_seq, CTX in *; lia | cbn; intros bb Hb0 _ W].
        assert (bb = ctx_seq) by (unfold ctx_seq in *; lia). subst bb. exact (NW W).
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (WR a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[W _]]; hsep; ceil; unfold HEAPLO, CTX in *; lia.
      + intros x Ux X. discriminate X.
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)); try (intros; assumption).
      + intros x Hx. repeat split; reflexivity.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. change (gcell st' x a) with (gcell st x a) in G. change (is_group st x) in Hx.
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (WR a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[W _]]; hsep; ceil; unfold HEAPLO, CTX in *; lia.
      + intros x a Hx G. left. exact G.
  Qed.

  Theorem policy_close : WF st' L /\ REP st' M'.
  Proof. split; [exact t_WF | exact t_REP]. Qed.
End Policy.
