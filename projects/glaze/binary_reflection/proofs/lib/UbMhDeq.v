(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDissolve. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDissolve.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac case_bool t E :=
  let b := fresh "b" in set (b := t) in |- *; assert (E : t = b) by reflexivity; clearbody b; destruct b.

Section Deq.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (g : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st g.
  Hypothesis Hav0 : mr_avail (s_meta st g) = 0.
  Hypothesis Hfr0 : mr_freed (s_meta st g) = 0.
  #[local] Notation sc := (g_sc st g).
  #[local] Notation l := (s_alist st sc).
  #[local] Notation nxt := (mr_next (s_meta st g)).
  #[local] Notation prv := (mr_prev (s_meta st g)).
  Definition inl : bool := if in_dec Z.eq_dec g l then true else false.
  Definition multi : bool := inl && negb (zlen l =? 1).
  Definition l' : list Z := zremove g l.

  Definition d_next (x : Z) : Z :=
    if x =? g then 0 else if (multi && (x =? prv))%bool then nxt else mr_next (s_meta st x).
  Definition d_prev (x : Z) : Z :=
    if x =? g then 0 else if (multi && (x =? nxt))%bool then prv else mr_prev (s_meta st x).
  Definition d_meta (x : Z) : meta_rec := mr_set_links (s_meta st x) (d_prev x) (d_next x).
  Definition st' : mst :=
    MST (cx_set_active (s_ctx st) (fupd (c_active (s_ctx st)) sc (head_of l')))
        (s_areas st) d_meta (s_flist st) (fupd (s_alist st) sc l') (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma g_wfg : wf_group st L g. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) g Hgrp). Qed.
  Lemma g_U : metaU st g. Proof using Hgrp HWF L RN. exact (wg_U st L g g_wfg). Qed.
  Lemma g_rng : HEAPLO + 24 <= g /\ g + 40 <= CEIL.
  Proof using Hgrp HWF L st. destruct (metaU_rng st L HWF g g_U) as (A & B & _). lia. Qed.
  Lemma sc_rng : 0 <= sc < 64. Proof using. unfold g_sc, w_sizeclass. apply Z.mod_pos_bound. lia. Qed.
  (* [comment removed for export] *)
  Lemma g_full : forall k, 0 <= k <= g_lastidx st g -> s_slot st g k <> SAvail /\ s_slot st g k <> SFreed.
  Proof using Hfr0 Hav0 Hgrp HWF L RN.
    intros k Hk. split; intros E.
    - pose proof (proj2 (wg_av st L g g_wfg k ltac:(lia)) (conj (proj2 Hk) E)) as T. rewrite Hav0, Z.bits_0 in T. discriminate T.
    - pose proof (proj2 (wg_fr st L g g_wfg k ltac:(lia)) (conj (proj2 Hk) E)) as T. rewrite Hfr0, Z.bits_0 in T. discriminate T.
  Qed.
  Lemma g_ai_last : s_ai st g = g_lastidx st g.
  Proof using Hfr0 Hav0 Hgrp HWF L RN.
    pose proof (wg_ai st L g g_wfg) as A. destruct (Z.eq_dec (s_ai st g) (g_lastidx st g)) as [E|NE]; [exact E|]. exfalso.
    pose proof (wg_high st L g g_wfg (g_lastidx st g) ltac:(lia)) as F. exact (proj2 (g_full (g_lastidx st g) ltac:(lia)) F).
  Qed.

  Lemma inl_true : inl = true <-> In g l.
  Proof using. unfold inl. destruct (in_dec Z.eq_dec g l); split; auto; intros H; discriminate H. Qed.
  Lemma inl_false : inl = false <-> ~ In g l.
  Proof using. unfold inl. destruct (in_dec Z.eq_dec g l); split; auto; intros H; [discriminate H | contradiction]. Qed.

  (* [comment removed for export] *)
  Lemma g_listed_inl : listed st g -> inl = true.
  Proof using Hgrp HWF L RN.
    intros Hl. apply inl_true. destruct Hl as [Hf|Ha].
    - exfalso. exact (wg_notfree st L g g_wfg Hf).
    - exact (wg_listed_sc st L g g_wfg Ha).
  Qed.
  Lemma inl_sc48 : inl = true -> 0 <= sc < 48.
  Proof using HWF L RN. intros H. apply inl_true in H. exact (proj1 (alist_member st L HWF sc g H)). Qed.
  Lemma l_dll : inl = true -> dll st l.
  Proof using HWF L RN. intros H. exact (wl_adll st (WF_lists st L HWF) sc (inl_sc48 H)). Qed.
  Lemma l_nodup : List.NoDup l.
  Proof using HWF L RN. apply NoDup_ListNoDup. exact (wl_anodup st (WF_lists st L HWF) sc). Qed.
  Lemma l_mem : forall x, In x l -> is_group st x /\ g_sc st x = sc /\ metaU st x /\ listed st x.
  Proof using HWF L RN. intros x Hin. destruct (alist_member st L HWF sc x Hin) as (A & B & C & D & E). tauto. Qed.
  Lemma links_in : inl = true -> In nxt l /\ In prv l.
  Proof using HWF L RN. intros H. apply (dllf_links_In _ _ l g (proj1 (dll_dllf st l) (l_dll H))). apply inl_true. exact H. Qed.
  Lemma multi_iff : multi = true <-> inl = true /\ zlen l <> 1.
  Proof using.
    unfold multi. rewrite Bool.andb_true_iff, Bool.negb_true_iff, Z.eqb_neq. tauto.
  Qed.
  Lemma multi_nxt : inl = true -> (multi = true <-> nxt <> g).
  Proof using HWF L RN.
    intros H. rewrite multi_iff.
    pose proof (dllf_self_iff _ _ l g (proj1 (dll_dllf st l) (l_dll H)) l_nodup (proj1 inl_true H)) as SI.
    split; [intros [_ N] E; apply N; apply SI; exact E | intros N; split; [exact H|]; intros E; apply N; apply SI; exact E].
  Qed.
  Lemma multi_prv : inl = true -> (multi = true <-> prv <> g).
  Proof using HWF L RN.
    intros H. rewrite multi_iff.
    pose proof (dllf_prev_self_iff _ _ l g (proj1 (dll_dllf st l) (l_dll H)) l_nodup (proj1 inl_true H)) as SI.
    split; [intros [_ N] E; apply N; apply SI; exact E | intros N; split; [exact H|]; intros E; apply N; apply SI; exact E].
  Qed.
  Lemma nxt_facts : multi = true -> is_group st nxt /\ g_sc st nxt = sc /\ metaU st nxt /\ listed st nxt /\ nxt <> g /\ In nxt l.
  Proof using HWF L RN.
    intros Hm. pose proof (proj1 (proj1 multi_iff Hm)) as H. destruct (links_in H) as [N _].
    destruct (l_mem nxt N) as (A & B & C & D). repeat split; try assumption. apply (multi_nxt H). exact Hm.
  Qed.
  Lemma prv_facts : multi = true -> is_group st prv /\ g_sc st prv = sc /\ metaU st prv /\ listed st prv /\ prv <> g /\ In prv l.
  Proof using HWF L RN.
    intros Hm. pose proof (proj1 (proj1 multi_iff Hm)) as H. destruct (links_in H) as [_ P].
    destruct (l_mem prv P) as (A & B & C & D). repeat split; try assumption. apply (multi_prv H). exact Hm.
  Qed.
  Lemma unl_links : inl = false -> nxt = 0 /\ prv = 0.
  Proof using Hgrp HWF L RN.
    intros H. apply (wl_link st (WF_lists st L HWF) g g_U). intros Hl. apply g_listed_inl in Hl. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma l_split : inl = true -> exists l1 l2, l = l1 ++ g :: l2 /\ l' = l1 ++ l2 /\ ~ In g l1 /\ ~ In g l2.
  Proof using HWF L RN. intros H. unfold l'. apply zremove_split; [exact l_nodup | apply inl_true; exact H]. Qed.
  Lemma l'_notin : ~ In g l'.
  Proof using. unfold l'. rewrite zremove_In. tauto. Qed.
  Lemma l'_sub : forall x, In x l' <-> In x l /\ x <> g.
  Proof using. intros x. unfold l'. apply zremove_In. Qed.
  Lemma l'_unl : inl = false -> l' = l.
  Proof using. intros H. unfold l'. apply zremove_notin. apply inl_false. exact H. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_alist : forall s, s_alist st' s = if s =? sc then l' else s_alist st s. Proof using. reflexivity. Qed.
  Lemma e_alist_sc : s_alist st' sc = l'. Proof using. rewrite e_alist, Z.eqb_refl. reflexivity. Qed.
  Lemma e_alist_other : forall s, s <> sc -> s_alist st' s = s_alist st s.
  Proof using. intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc); [contradiction | reflexivity]. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_meta : forall x, s_meta st' x = d_meta x. Proof using. reflexivity. Qed.
  Lemma e_next : forall x, mr_next (s_meta st' x) = d_next x. Proof using. reflexivity. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = d_prev x. Proof using. reflexivity. Qed.
  Lemma e_avail : forall x, mr_avail (s_meta st' x) = mr_avail (s_meta st x). Proof using. reflexivity. Qed.
  Lemma e_freed : forall x, mr_freed (s_meta st' x) = mr_freed (s_meta st x). Proof using. reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof using. reflexivity. Qed.
  Lemma e_ctx_active : forall s, c_active (s_ctx st') s = if s =? sc then head_of l' else c_active (s_ctx st) s.
  Proof using. intros s. reflexivity. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using. intros; unfold metaU; cbn; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using. intros; unfold is_group; cbn; tauto. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using. intros; unfold in_flist; cbn; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using. intros; unfold fresh; cbn; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x /\ x <> g.
  Proof using HWF L RN.
    intros x. unfold in_alist. split.
    - intros (s & Hs & Hin). rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [->|Hne].
      + apply l'_sub in Hin. destruct Hin as [Hin Hx]. split; [exists sc; split; assumption | exact Hx].
      + split; [exists s; split; assumption|]. intros ->. apply Hne. symmetry. exact (proj2 (proj2 (wl_aU st (WF_lists st L HWF) s g Hin))).
    - intros [(s & Hs & Hin) Hx]. exists s. split; [exact Hs|]. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [apply l'_sub; split; assumption | exact Hin].
  Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x /\ x <> g.
  Proof using Hgrp HWF L RN.
    intros x. unfold listed. rewrite e_in_flist, e_in_alist. split.
    - intros [F|[A B]]; [|tauto]. split; [left; exact F|]. intros ->. exact (wg_notfree st L g g_wfg F).
    - tauto.
  Qed.
  Lemma SL : same_layout st st'.
  Proof using. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of Z.of_nat l']; try assumption.
    intros s Hs. unfold fupd. destruct (Z.eqb_spec s sc) as [->|Hne]; [reflexivity | exact (A4 s Hs)].
  Qed.

  Lemma head_l' : inl = true -> forall l1 l2, l = l1 ++ g :: l2 -> l' = l1 ++ l2 ->
    (l1 = [] /\ head_of l = g /\ head_of l' = head_of l2) \/ (l1 <> [] /\ head_of l' = head_of l /\ head_of l <> g).
  Proof using HWF L RN.
    intros H l1 l2 E E'. destruct l1 as [|a l1].
    - left. rewrite E'. rewrite E. cbn. repeat split; reflexivity.
    - right. rewrite E', E. cbn. split; [congruence|]. split; [reflexivity|].
      intros ->. pose proof l_nodup as ND. rewrite E in ND. apply (NoDup_remove_2 (g :: l1) l2 g ND). apply in_app_iff. left. left. reflexivity.
  Qed.

  Lemma t_dll_l' : dll st' l'.
  Proof using Hgrp HWF L RN.
    apply (proj2 (dll_dllf st' l')).
    change (dllf (fun x => mr_next (s_meta st' x)) (fun x => mr_prev (s_meta st' x)) l') with (dllf d_next d_prev l').
    case_bool inl Hi.
    - destruct (l_split Hi) as (l1 & l2 & E & E' & N1 & N2).
      case_bool multi Hm.
      + pose proof (proj1 (dll_dllf st l) (l_dll Hi)) as D. rewrite E in D. rewrite E'.
        assert (Hlen : 0 < zlen (l1 ++ l2)).
        { apply multi_iff in Hm. destruct Hm as [_ Hn]. rewrite E in Hn. rewrite zlen_app, zlen_cons in Hn. rewrite zlen_app.
          pose proof (zlen_nonneg l1). pose proof (zlen_nonneg l2). lia. }
        pose proof l_nodup as ND. rewrite E in ND.
        destruct (prv_facts Hm) as (_ & _ & _ & _ & Pg & _). destruct (nxt_facts Hm) as (_ & _ & _ & _ & Ng & _).
        apply (dllf_remove _ _ d_next d_prev l1 l2 g D ND Hlen).
        * intros x Hx Hne. unfold d_next. rewrite <- E' in Hx. apply l'_sub in Hx. destruct Hx as [_ Hxg].
          destruct (Z.eqb_spec x g); [contradiction|]. rewrite Hm. cbn. destruct (Z.eqb_spec x prv); [contradiction|reflexivity].
        * unfold d_next. destruct (Z.eqb_spec prv g); [contradiction|]. rewrite Hm, Z.eqb_refl. reflexivity.
        * intros x Hx Hne. unfold d_prev. rewrite <- E' in Hx. apply l'_sub in Hx. destruct Hx as [_ Hxg].
          destruct (Z.eqb_spec x g); [contradiction|]. rewrite Hm. cbn. destruct (Z.eqb_spec x nxt); [contradiction|reflexivity].
        * unfold d_prev. destruct (Z.eqb_spec nxt g); [contradiction|]. rewrite Hm, Z.eqb_refl. reflexivity.
      + (* [comment removed for export] *)
        assert (Hn : zlen l = 1).
        { destruct (Z.eq_dec (zlen l) 1) as [|Hne]; [assumption|]. exfalso.
          assert (multi = true) by (apply multi_iff; split; [exact Hi | exact Hne]). congruence. }
        assert (El : l' = []).
        { pose proof (zlen_zremove g l l_nodup (proj1 inl_true Hi)) as Z1. fold l' in Z1. rewrite Hn in Z1.
          destruct l' as [|a l0]; [reflexivity | rewrite zlen_cons in Z1; pose proof (zlen_nonneg l0); lia]. }
        rewrite El. intros k Hk. change (zlen []) with 0 in Hk. lia.
    - rewrite (l'_unl Hi). destruct (unl_links Hi) as [N0 P0].
      assert (Hm : multi = false) by (unfold multi; rewrite Hi; reflexivity).
      destruct (Z.lt_ge_cases sc 48) as [H48|H48].
      + intros k Hk. pose proof (wl_adll st (WF_lists st L HWF) sc ltac:(pose proof sc_rng; lia)) as D.
        destruct (D k Hk) as [N P]. unfold d_next, d_prev. rewrite Hm. cbn [andb].
        assert (Hin : In (znth l k) l) by (apply znth_In; exact Hk).
        assert (znth l k <> g) by (intros Eg; rewrite Eg in Hin; exact (proj1 inl_false Hi Hin)).
        destruct (Z.eqb_spec (znth l k) g); [contradiction|]. split; assumption.
      + rewrite (wl_anil st (WF_lists st L HWF) sc ltac:(lia)). intros k Hk. change (zlen []) with 0 in Hk. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma d_next_other : forall x, x <> g -> (multi = true -> x <> prv) -> d_next x = mr_next (s_meta st x).
  Proof using.
    intros x H1 H2. unfold d_next. destruct (Z.eqb_spec x g); [contradiction|].
    case_bool multi Hm; cbn; [|reflexivity]. destruct (Z.eqb_spec x prv); [exfalso; exact (H2 Hm e) | reflexivity].
  Qed.
  Lemma d_prev_other : forall x, x <> g -> (multi = true -> x <> nxt) -> d_prev x = mr_prev (s_meta st x).
  Proof using.
    intros x H1 H2. unfold d_prev. destruct (Z.eqb_spec x g); [contradiction|].
    case_bool multi Hm; cbn; [|reflexivity]. destruct (Z.eqb_spec x nxt); [exfalso; exact (H2 Hm e) | reflexivity].
  Qed.
  Lemma d_meta_other : forall x, x <> g -> (multi = true -> x <> prv) -> (multi = true -> x <> nxt) -> d_meta x = s_meta st x.
  Proof using. intros x H1 H2 H3. unfold d_meta. rewrite d_next_other, d_prev_other by assumption. apply mr_set_links_id. Qed.
  Lemma d_meta_nongroup : forall x, ~ is_group st x -> d_meta x = s_meta st x.
  Proof using Hgrp HWF L RN.
    intros x NG. apply d_meta_other.
    - intros ->. exact (NG Hgrp).
    - intros Hm ->. exact (NG (proj1 (prv_facts Hm))).
    - intros Hm ->. exact (NG (proj1 (nxt_facts Hm))).
  Qed.
  Lemma d_meta_offlist : forall x, x <> g -> ~ In x l -> d_meta x = s_meta st x.
  Proof using HWF L RN.
    intros x H1 H2. apply d_meta_other; [exact H1 | |].
    - intros Hm ->. exact (H2 (proj2 (proj2 (proj2 (proj2 (proj2 (prv_facts Hm))))))).
    - intros Hm ->. exact (H2 (proj2 (proj2 (proj2 (proj2 (proj2 (nxt_facts Hm))))))).
  Qed.
  Lemma d_meta_g : inl = false -> d_meta g = s_meta st g.
  Proof using Hgrp HWF L RN.
    intros Hi. destruct (unl_links Hi) as [N0 P0]. unfold d_meta, d_next, d_prev. rewrite Z.eqb_refl.
    rewrite <- N0 at 2. rewrite <- P0 at 1. apply mr_set_links_id.
  Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hgrp HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    pose proof g_rng as GR.
    constructor; rewrite ?e_flist.
    - apply (dll_ext st st'). 2: exact D1. intros x Hx. rewrite e_meta. rewrite d_meta_nongroup; [split; reflexivity|].
      exact (proj1 (proj2 (FU x Hx))).
    - exact ND1.
    - intros x Hx. destruct (FU x Hx) as (U & NG & NF & Me & Av & Fr & W).
      rewrite e_metaU, e_is_group, e_fresh, e_meta, d_meta_nongroup by exact NG. repeat split; assumption.
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [exact t_dll_l'|].
      apply (dll_ext st st'); [|exact (D2 s Hs)]. intros x Hx. rewrite e_meta. rewrite d_meta_offlist; [split; reflexivity| |].
      + intros ->. destruct (AU s g Hx) as (_ & _ & E). exact (Hne (eq_sym E)).
      + intros Hin. destruct (AU s x Hx) as (_ & _ & S1). destruct (AU sc x Hin) as (_ & _ & S2). congruence.
    - intros s. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (ND2 s)].
      unfold l'. apply (proj2 (NoDup_ListNoDup _)). apply zremove_NoDup. exact l_nodup.
    - intros s x Hin. rewrite e_is_group, e_gsc. rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [->|Hne].
      + apply l'_sub in Hin. destruct Hin as [Hin Hx]. exact (AU sc x Hin).
      + exact (AU s x Hin).
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (AN s Hs)].
      unfold l'. rewrite (AN sc Hs). reflexivity.
    - intros x U NL. rewrite e_metaU in U. rewrite e_listed in NL. rewrite e_next, e_prev.
      destruct (Z.eq_dec x g) as [->|Hxg].
      + unfold d_next, d_prev. rewrite Z.eqb_refl. split; reflexivity.
      + assert (NLx : ~ listed st x) by (intros Hl; apply NL; split; assumption).
        rewrite d_next_other, d_prev_other; [apply LK; [exact U | exact NLx] | exact Hxg | | exact Hxg |].
        * intros Hm ->. apply NLx. exact (proj1 (proj2 (proj2 (proj2 (nxt_facts Hm))))).
        * intros Hm ->. apply NLx. exact (proj1 (proj2 (proj2 (proj2 (prv_facts Hm))))).
    - intros x Hl. rewrite e_next, e_prev. apply e_listed in Hl. destruct Hl as [Hl Hxg].
      destruct (LKD x Hl) as [O1 O2].
      unfold d_next, d_prev. destruct (Z.eqb_spec x g); [contradiction|].
      case_bool multi Hm; cbn [andb]; [|split; assumption].
      pose proof (group_pos st L HWF nxt (proj1 (nxt_facts Hm))). pose proof (group_pos st L HWF prv (proj1 (prv_facts Hm))).
      destruct (Z.eqb_spec x prv); destruct (Z.eqb_spec x nxt); split; try assumption; hsep; unfold HEAPLO in *; lia.
    - intros s x Hin Hne. rewrite e_avail, e_freed. rewrite e_alist in Hin, Hne.
      destruct (Z.eqb_spec s sc) as [->|Hs]; [|exact (RS s x Hin Hne)].
      apply (RS sc x); [apply l'_sub in Hin; tauto|].
      intros Ex. apply Hne. rewrite Ex.
      case_bool inl Hi.
      + destruct (l_split Hi) as (l1 & l2 & E & E' & N1 & N2).
        destruct (head_l' Hi l1 l2 E E') as [(A & B & C)|(A & B & C)].
        * exfalso. apply l'_sub in Hin. destruct Hin as [_ Hxg]. apply Hxg. rewrite Ex. exact B.
        * symmetry. exact B.
      + rewrite (l'_unl Hi). reflexivity.
  Qed.

  Lemma t_wf_group_other : forall x, is_group st x -> x <> g -> wf_group st' L x.
  Proof using Hgrp HWF RN.
    intros x Hx Hxg. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gsc; try assumption.
    - intros Hal. rewrite e_alist. apply e_in_alist in Hal. destruct Hal as [Hal _].
      destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [apply l'_sub; split; [rewrite <- E; exact (Lsc Hal) | exact Hxg] | exact (Lsc Hal)].
    - intros H63 Hl. apply (S63 H63). apply e_listed in Hl. exact (proj1 Hl).
    - intros Hp. rewrite e_alist. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [apply l'_sub; split; [rewrite <- E; exact (Part Hp) | exact Hxg] | exact (Part Hp)].
    - intros Hall Hne Hl. apply e_listed in Hl. destruct Hl as [Hl _]. apply (Full Hall); [|exact Hl].
      rewrite e_alist in Hne. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hne].
      intros Exh. case_bool inl Hi.
      + destruct (l_split Hi) as (l1 & l2 & El & El' & N1 & N2).
        destruct (head_l' Hi l1 l2 El El') as [(A & B & C)|(A & B & C)].
        * apply Hxg. rewrite Exh, E. exact B.
        * apply Hne. rewrite B, <- E. exact Exh.
      + apply Hne. rewrite (l'_unl Hi), <- E. exact Exh.
    - intros Hall. destruct (FF Hall) as (K & S48 & Hin). split; [exact K|]. split; [exact S48|].
      rewrite e_alist. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hin]. apply l'_sub. split; [rewrite <- E; exact Hin | exact Hxg].
  Qed.

  Lemma g_notin_alist' : forall s, ~ In g (s_alist st' s).
  Proof using HWF L RN.
    intros s Hin. rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [E|Hne]; [exact (l'_notin Hin)|].
    apply Hne. symmetry. exact (proj2 (proj2 (wl_aU st (WF_lists st L HWF) s g Hin))).
  Qed.
  Lemma g_unlisted' : ~ listed st' g.
  Proof using Hgrp HWF L RN. intros Hl. apply e_listed in Hl. exact (proj2 Hl eq_refl). Qed.

  Lemma t_wf_group_g : wf_group st' L g.
  Proof using Hfr0 Hav0 Hgrp HWF RN.
    pose proof g_wfg as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gsc; try assumption.
    - intros (s & Hs & Hin). exfalso. exact (g_notin_alist' s Hin).
    - intros _. exact g_unlisted'.
    - intros Hp. exfalso. change (s_ai st' g) with (s_ai st g) in Hp. change (g_lastidx st' g) with (g_lastidx st g) in Hp. rewrite g_ai_last in Hp. lia.
    - intros _ _. exact g_unlisted'.
    - intros Hall. exfalso. assert (GL : 0 <= g_lastidx st g) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia).
      destruct (g_full 0 ltac:(lia)) as [A B]. destruct (Hall 0 ltac:(change (g_lastidx st' g) with (g_lastidx st g); lia)) as [E|E]; cbn [s_slot st'] in E; [exact (A E) | exact (B E)].
  Qed.

  Lemma t_WF : WF st' L.
  Proof using Hfr0 Hav0 Hgrp HWF.
    pose proof HWF as (C & A & Ls & G & Ge & Lv & R & WI).
    split; [exact t_wf_ctx|]. split; [exact (wf_areas_ext st st' SL A)|]. split; [exact t_wf_lists|].
    split.
    { destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      - intros x Hx. destruct (Z.eq_dec x g) as [->|Hxg]; [exact t_wf_group_g | exact (t_wf_group_other x Hx Hxg)].
      - intros x F. rewrite e_meta, d_meta_nongroup; [exact (FR0 x F)|]. intros Hx. exact (wg_notfresh st L x (EACH x Hx) F).
      - intros x Hlim. destruct (LIM x Hlim) as (A1 & B1 & C1 & D1). split; [exact A1|]. split; [exact B1|]. split; [|exact D1].
        intros Hl. apply C1. apply e_listed in Hl. exact (proj1 Hl). }
    split; [exact (wf_geom_ext st st' L SL HWF Ge)|].
    split; [exact (wf_live_ext st st' L SL Lv) |]. split; [exact (wf_regions_ext st st' L SL HWF eq_refl R) | exact (wf_img_ext st st' SL (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition d_wr (a : Z) : Prop :=
    (sp - MSTK <= a < sp) \/ (inl = true /\ g <= a < g + 16) \/
    (multi = true /\ ((prv + 8 <= a < prv + 16) \/ (nxt <= a < nxt + 8))) \/
    (inl = true /\ ctx_active sc <= a < ctx_active sc + 8).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> d_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMg0 : cell M' g 8 0.
  Hypothesis HMg8 : cell M' (g + 8) 8 0.
  Hypothesis HMprv : multi = true -> cell M' (prv + 8) 8 nxt.
  Hypothesis HMnxt : multi = true -> cell M' nxt 8 prv.
  Hypothesis HMact : inl = true -> cell M' (ctx_active sc) 8 (head_of l').

  Definition XMd (x : Z) : bool := (inl && (x =? g)) || (multi && ((x =? prv) || (x =? nxt))).
  Definition XAd (s : Z) : bool := inl && (s =? sc).



  (* [comment removed for export] *)
  Lemma wr_cases : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    CEIL <= a \/ (exists x, metaU st x /\ XMd x = true /\ x <= a < x + 40) \/ (inl = true /\ ctx_active sc <= a < ctx_active sc + 8).
  Proof using HMwr Hsp Hgrp HWF sp L.
    intros a Hr NE. destruct (HMwr a Hr NE) as [W|[[Hi W]|[[Hm [W|W]]|W]]].
    - left. ceil; unfold MSTK in *. lia.
    - right; left. exists g. split; [exact g_U|]. split; [unfold XMd; rewrite Hi, Z.eqb_refl; reflexivity | lia].
    - right; left. exists prv. split; [exact (proj1 (proj2 (proj2 (prv_facts Hm))))|].
      split; [unfold XMd; rewrite Hm, Z.eqb_refl; cbn; rewrite ?Bool.orb_true_r; reflexivity | lia].
    - right; left. exists nxt. split; [exact (proj1 (proj2 (proj2 (nxt_facts Hm))))|].
      split; [unfold XMd; rewrite Hm, !Z.eqb_refl; cbn; rewrite ?Bool.orb_true_r; reflexivity | lia].
    - right; right. exact W.
  Qed.

  Lemma t_rep_meta_g : inl = true -> rep_meta M' g (d_meta g).
  Proof using HMg8 HMg0 HMwr Hsp Hgrp HREP HWF sp M L RN.
    intros Hi. pose proof sc_rng as SR. pose proof (metaU_area st L HWF g g_U) as (ar & k & Har & Hk & Hm & _).
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hm in RM.
    destruct RM as [P N Me Av Fr Wc]. pose proof g_rng as [R1 R2].
    assert (AG : agree_on (fun a => g + 16 <= a < g + 40) M M').
    { intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[[_ W]|[[Hm' [W|W]]|[_ W]]]].
      - ceil; unfold MSTK in *; lia.
      - lia.
      - destruct (prv_facts Hm') as (_ & _ & Up & _ & Np & _). destruct (metaU_sep st L HWF g prv g_U Up (fun E => Np (eq_sym E))); lia.
      - destruct (nxt_facts Hm') as (_ & _ & Un & _ & Nn & _). destruct (metaU_sep st L HWF g nxt g_U Un (fun E => Nn (eq_sym E))); lia.
      - hsep; unfold ctx_active, CTX, HEAPLO in *. lia. }
    unfold d_meta, mr_set_links, d_next, d_prev. rewrite Z.eqb_refl.
    constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - exact HMg0.
    - exact HMg8.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma t_rep_meta_nb : forall x, multi = true -> (x = prv \/ x = nxt) -> rep_meta M' x (d_meta x).
  Proof using HMnxt HMprv HMwr Hsp Hgrp HREP HWF sp M L RN.
    intros x Hm Hx. pose proof sc_rng as SR.
    destruct (prv_facts Hm) as (_ & _ & Up & _ & Np & _). destruct (nxt_facts Hm) as (_ & _ & Un & _ & Nn & _).
    assert (Ux : metaU st x) by (destruct Hx as [-> | ->]; assumption).
    assert (Hxg : x <> g) by (destruct Hx as [-> | ->]; assumption).
    pose proof (metaU_area st L HWF x Ux) as (ar & k & Har & Hk & Hxa & _).
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hxa in RM.
    destruct RM as [P N Me Av Fr Wc]. destruct (metaU_rng st L HWF x Ux) as (R1 & R2 & _).
    pose proof (metaU_sep st L HWF x g Ux g_U Hxg) as SEPg.
    assert (AG : agree_on (fun a => x <= a < x + 40 /\ ~ (x = nxt /\ x <= a < x + 8) /\ ~ (x = prv /\ x + 8 <= a < x + 16)) M M').
    { intros a Hr (Ha & N1 & N2). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[[_ W]|[[_ [W|W]]|[_ W]]]].
      - ceil; unfold MSTK in *. lia.
      - lia.
      - destruct (Z.eq_dec x prv) as [E|NEp]; [apply N2; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x prv Ux Up NEp); lia.
      - destruct (Z.eq_dec x nxt) as [E|NEn]; [apply N1; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x nxt Ux Un NEn); lia.
      - hsep; unfold ctx_active, CTX, HEAPLO in *. lia. }
    unfold d_meta, mr_set_links, d_next, d_prev. destruct (Z.eqb_spec x g); [contradiction|]. rewrite Hm. cbn [andb].
    constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - destruct (Z.eqb_spec x nxt) as [E|NE].
      + rewrite E at 1. exact (HMnxt Hm).
      + eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact P]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - destruct (Z.eqb_spec x prv) as [E|NE].
      + rewrite E at 1. exact (HMprv Hm).
      + eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact N]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMact HMnxt HMprv HMg8 HMg0 HMgrow HMwr Hsp Hgrp HREP HWF sp M L RN.
    pose proof g_rng as [MR1 MR2]. pose proof sc_rng as SR.
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|[_ W]]].
      + ceil; unfold CTX in *; lia.
      + destruct (metaU_rng st L HWF x Ux). hsep; unfold HEAPLO, CTX in *; lia.
      + unfold ctx_active, CTX in *; lia.
    - apply (rep_ctx_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow) XAd false); try reflexivity.
      + intros a Hr (Ha & NA & NF). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|[Hi W]]].
        * ceil; unfold CTX_END, CTX in *; lia.
        * destruct (metaU_rng st L HWF x Ux). hsep; unfold HEAPLO, CTX_END, CTX in *; lia.
        * apply NA. exists sc. split; [exact (inl_sc48 Hi)|]. split; [unfold XAd; rewrite Hi, Z.eqb_refl; reflexivity | exact W].
      + intros s Hs. unfold XAd. rewrite e_ctx_active. destruct (Z.eqb_spec s sc) as [->|Hne].
        * case_bool inl Hi; cbn [andb].
          -- left. split; [reflexivity|]. exact (HMact Hi).
          -- right. split; [reflexivity|]. rewrite (l'_unl Hi). symmetry. exact (wc_active st (WF_ctx st L HWF) sc Hs).
        * right. rewrite Bool.andb_false_r. split; reflexivity.
      + right. split; reflexivity.
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) XMd); try reflexivity.
      + intros ar a Har Ha NE. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(x & Ux & Hx & W)|[_ W]]].
        * ceil; lia.
        * exists x. split; [exact Ux|]. split; [exact Hx | exact W].
        * hsep; unfold ctx_active, CTX, HEAPLO in *; lia.
      + intros x Ux X. unfold XMd in X. rewrite e_meta. apply Bool.orb_true_iff in X. destruct X as [X|X].
        * apply Bool.andb_true_iff in X. destruct X as [Hi Xg]. apply Z.eqb_eq in Xg. subst x. exact (t_rep_meta_g Hi).
        * apply Bool.andb_true_iff in X. destruct X as [Hm X]. apply t_rep_meta_nb; [exact Hm|].
          apply Bool.orb_true_iff in X. destruct X as [X|X]; apply Z.eqb_eq in X; [left | right]; exact X.
      + intros x Ux X. unfold XMd in X. rewrite e_meta. apply Bool.orb_false_iff in X. destruct X as [X1 X2].
        destruct (Z.eq_dec x g) as [->|Hxg].
        * rewrite Z.eqb_refl, Bool.andb_true_r in X1. exact (d_meta_g X1).
        * apply d_meta_other; [exact Hxg | |]; intros Hm ->; rewrite Hm, Z.eqb_refl in X2; cbn in X2;
            rewrite ?Bool.orb_true_r in X2; discriminate X2.
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)).
      + intros x Hx. exact Hx.
      + intros x Hx. repeat split; reflexivity.
      + intros x Hx E. exact E.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G.
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(y & Uy & _ & W)|[_ W]]].
        * ceil; lia.
        * exact (gcell_not_meta st L HWF x y a Hx G Uy W).
        * hsep; unfold ctx_active, CTX, HEAPLO in *; lia.
      + intros x a Hx G. left. exact G.
  Qed.

  Theorem deq_close : WF st' L /\ REP st' M'.
  Proof using HMact HMnxt HMprv HMg8 HMg0 HMgrow HMwr Hsp Hfr0 Hav0 Hgrp HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.

  Lemma deq_facts : s_alist st' sc = l' /\ (forall s, s <> sc -> s_alist st' s = s_alist st s) /\ c_active (s_ctx st') sc = head_of l' /\
    s_slot st' = s_slot st /\ s_groups st' = s_groups st /\ s_ai st' = s_ai st /\
    (forall x, mr_avail (s_meta st' x) = mr_avail (s_meta st x) /\ mr_freed (s_meta st' x) = mr_freed (s_meta st x) /\
               mr_mem (s_meta st' x) = mr_mem (s_meta st x) /\ mr_W (s_meta st' x) = mr_W (s_meta st x)).
  Proof using.
    split; [exact e_alist_sc|]. split; [exact e_alist_other|]. split; [rewrite e_ctx_active, Z.eqb_refl; reflexivity|].
    repeat split; reflexivity.
  Qed.
End Deq.
