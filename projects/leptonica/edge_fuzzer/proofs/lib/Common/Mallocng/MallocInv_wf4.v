(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep MallocInv_wf.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SetCtx.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variable c' : ctx_rec.

  Hypothesis C_init : c' KInit = 0 \/ c' KInit = 1.
  Hypothesis C_uninit : c' KInit = 0 -> a_areas A = [] /\ c' KFmh = 0 /\ c' KAmc = 0 /\
              c' KAac = 0 /\ c' KBrk = 0 /\ c' KAtail = 0 /\
              c' KShift = 0 /\ a_pages A = [] /\ (forall sc, c' (KActive sc) = 0).
  Hypothesis C_amc : 0 <= c' KAmc <= 100.
  Hypothesis C_am : c' KAmc > 0 ->
          exists pg, a_areas A <> [] /\ pg = last (a_areas A) 0 /\
          c' KAm = meta_addr pg (101 - c' KAmc) /\
          forall k, 101 - c' KAmc <= k < 101 ->
            exists mt, a_meta A (meta_addr pg k) = Some mt /\ mt_role mt = RAvail.
  Hypothesis C_atail : c' KAtail = last (a_areas A) 0.
  Hypothesis C_ahead : c' KAhead = hd 0 (a_areas A).
  Hypothesis C_fmh : c' KFmh = hd 0 (a_freelist A).
  Hypothesis C_act : forall sc, 0 <= sc < 48 -> c' (KActive sc) = hd 0 (a_active A sc).
  Hypothesis C_nonneg : forall k, 0 <= c' k.
  Hypothesis C_shift : c' KShift < 48.
  Hypothesis C_noarea : a_areas A = [] -> c' KAac = 0 -> c' KShift = 0.
  Hypothesis C_brk0 : c' KBrk = 0 -> a_areas A = [] /\ a_pages A = [] /\ c' KAac = 0.
  Hypothesis C_mblocks : Z.of_nat (length (a_mblocks A)) <= Z.of_nat (length (a_areas A)) + (if c' KAac =? 0 then 0 else 1).
  Hypothesis C_shift_mb : c' KShift <= Z.of_nat (length (a_mblocks A)).
  (* [comment removed for export] *)
  Hypothesis C_acct : 2 ^ (c' KShift + 1) <= Z.of_nat (length (a_areas A)) + c' KAac + c' KShift + 2 /\
                      2 ^ (c' KShift) <= Z.of_nat (length (a_areas A)) + c' KShift + 2 /\
                      Z.of_nat (length (a_mblocks A)) <= c' KShift.

  Theorem WF_set_ctx : WF (set_ctx A c').
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps set_ctx]; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma has_set_ctx : forall f, has (set_ctx A c') f ->
    (exists k, cvalid k /\ f = FCT (caddr k) (clen k) (c' k)) \/
    (has_area A f /\ c' KSecret = a_ctx A KSecret) \/
    (exists pg, In pg (a_areas A) /\ f = FCT pg 8 (c' KSecret)) \/
    has_meta A f \/ has_grp A f.
  Proof.
    intros f [Hcx | [Har | [Hm | Hg]]].
    - left. destruct Hcx as (k & Hk & ->). exists k. auto.
    - right; right; left. destruct Har as (pg & Hpg & ->). exists pg. auto.
    - right; right; right; left. exact Hm.
    - right; right; right; right. exact Hg.
  Qed.

  Lemma has_set_ctx_intro_ctx : forall k, cvalid k -> has (set_ctx A c') (FCT (caddr k) (clen k) (c' k)).
  Proof. intros k Hk. left. exists k. auto. Qed.

  Lemma has_set_ctx_kept : forall f, has A f -> ~ has_ctx A f -> ~ has_area A f -> has (set_ctx A c') f.
  Proof.
    intros f [Hcx | [Har | [Hm | Hg]]] Hn Ha; [exfalso; exact (Hn Hcx) | exfalso; exact (Ha Har) | |].
    - right; right; left. exact Hm.
    - right; right; right. exact Hg.
  Qed.

  Lemma has_set_ctx_area : forall pg, In pg (a_areas A) -> has (set_ctx A c') (FCT pg 8 (c' KSecret)).
  Proof. intros pg Hpg. right; left. exists pg. auto. Qed.

  Lemma dom_set_ctx : forall x, dom (set_ctx A c') x <-> dom A x.
  Proof. intros x. reflexivity. Qed.

  Lemma VMok_set_ctx : forall h, VMok A h ->
    (c' KBrk = 0 \/ c' KBrk = 2^64 - 1 \/
       (c' KBrk = bv_unsigned (vm_brk h) /\ 0 < bv_unsigned (vm_brk h) /\
        bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h) /\ page_aligned (bv_unsigned (vm_brk h)))) ->
    (c' KAac > 0 ->
       page_aligned (c' KAareas) /\ c' KAareas + 4096 * c' KAac <= alloc_ceiling /\
       map_contains (vm_maps h) (Z_to_bv 64 (c' KAareas)) (Z_to_bv 64 (4096 * c' KAac)) = true /\
       map_contains (vm_noaccess h) (Z_to_bv 64 (c' KAareas)) (Z_to_bv 64 (4096 * c' KAac)) = true) ->
    (c' KBrk = 0 -> vm_brk h = vm_start_brk h) ->
    VMok (set_ctx A c') h.
  Proof.
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vlim] Hb Hr Hs. constructor; cbn; auto.
    split; [exact Hs | exact (proj2 Vspan)].
  Qed.
End SetCtx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctx_heur (k : cslot) : Prop :=
  match k with KUsage _ | KSeq | KUseq _ | KBounce _ | KCtr => True | _ => False end.

Section CtxHeur.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variable c' : ctx_rec.
  Hypothesis Hc : forall k, ctx_heur k \/ c' k = a_ctx A k.
  Hypothesis Hnn : forall k, 0 <= c' k.

  Lemma hc_eq : forall k, ~ ctx_heur k -> c' k = a_ctx A k.
  Proof. intros k Hk. destruct (Hc k) as [H | H]; [exfalso; exact (Hk H) | exact H]. Qed.

  Theorem WF_ctx_heur : WF (set_ctx A c').
  Proof.
    assert (E : forall k, ~ ctx_heur k -> c' k = a_ctx A k) by (intros k Hk; destruct (Hc k) as [H | H]; [exfalso; exact (Hk H) | exact H]).
    apply WF_set_ctx; try exact HW; rewrite ?(E KInit), ?(E KFmh), ?(E KAmc), ?(E KAac), ?(E KBrk), ?(E KAtail), ?(E KShift), ?(E KAm), ?(E KAhead) by (cbn; tauto).
    - exact (wf_init A HW).
    - intros H0. destruct (wf_uninit A HW H0) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
      repeat split; auto. intros sc. rewrite (E (KActive sc)) by (cbn; tauto). apply E9.
    - exact (wf_amc A HW).
    - exact (wf_am A HW).
    - exact (wf_atail A HW).
    - exact (wf_ahead A HW).
    - exact (wf_fl_head A HW).
    - intros sc Hsc. rewrite (E (KActive sc)) by (cbn; tauto). exact (wf_act_head A HW sc Hsc).
    - exact Hnn.
    - exact (wf_shift A HW).
    - exact (wf_noarea_shift A HW).
    - exact (wf_brk0 A HW).
    - exact (wf_mblocks_len A HW).
    - exact (wf_shift_mblocks A HW).
    - exact (wf_shift_acct A HW).
  Qed.

  Lemma VMok_ctx_heur : forall h, VMok A h -> VMok (set_ctx A c') h.
  Proof.
    intros h HV. apply VMok_set_ctx; [exact HV | | |].
    - rewrite (hc_eq KBrk) by (cbn; tauto). exact (vm_brk_ok A h HV).
    - rewrite (hc_eq KAac), (hc_eq KAareas) by (cbn; tauto). exact (vm_areas_res A h HV).
    - rewrite (hc_eq KBrk) by (cbn; tauto). exact (proj1 (vm_brk_span A h HV)).
  Qed.
End CtxHeur.

End WithLayout.
