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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma mr_set_links_id : forall r, mr_set_links r (mr_prev r) (mr_next r) = r.
Proof. intros [a b c d e f]; reflexivity. Qed.

Definition is_nilb (l : list Z) : bool := match l with [] => true | _ => false end.
Lemma is_nilb_true : forall l, is_nilb l = true <-> l = [].
Proof. intros [|a l]; split; intros H; try reflexivity; discriminate H. Qed.
Lemma is_nilb_false : forall l, is_nilb l = false <-> l <> [].
Proof. intros [|a l]; split; intros H; cbn in *; try congruence. Qed.

(* [comment removed for export] *)
Ltac case_bool t E :=
  let b := fresh "b" in set (b := t) in |- *; assert (E : t = b) by reflexivity; clearbody b; destruct b.

Section Queue.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (m sc : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hsc : g_sc st m = sc.
  Hypothesis Hsc48 : 0 <= sc < 48.
  Hypothesis Hunl : ~ listed st m.
  #[local] Notation l := (s_alist st sc).
  Definition q_nil : bool := is_nilb (s_alist st sc).
  #[local] Notation hd := (head_of l).
  #[local] Notation tl := (znth l (zlen l - 1)).
  Hypothesis Hrest : q_nil = false -> mr_avail (s_meta st m) = 0 /\ mr_freed (s_meta st m) <> 0.
  Hypothesis Hnotfull : exists k, 0 <= k <= g_lastidx st m /\ (s_slot st m k = SAvail \/ s_slot st m k = SFreed).
  Hypothesis Hff : (forall k, 0 <= k <= g_lastidx st m -> s_slot st m k = SAvail \/ s_slot st m k = SFreed) ->
                   s_kind st m = GTop /\ q_nil = true.

  Definition q_next (x : Z) : Z :=
    if x =? m then (if q_nil then m else hd)
    else if (negb q_nil && (x =? tl))%bool then m else mr_next (s_meta st x).
  Definition q_prev (x : Z) : Z :=
    if x =? m then (if q_nil then m else tl)
    else if (negb q_nil && (x =? hd))%bool then m else mr_prev (s_meta st x).
  Definition q_meta (x : Z) : meta_rec := mr_set_links (s_meta st x) (q_prev x) (q_next x).
  Definition l' : list Z := l ++ [m].
  Definition st' : mst :=
    MST (cx_set_active (s_ctx st) (fupd (c_active (s_ctx st)) sc (head_of l')))
        (s_areas st) q_meta (s_flist st) (fupd (s_alist st) sc l') (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma q_nil_iff : q_nil = true <-> l = [].
  Proof using. unfold q_nil. apply is_nilb_true. Qed.
  Lemma q_nnil_iff : q_nil = false <-> l <> [].
  Proof using. unfold q_nil. apply is_nilb_false. Qed.

  Lemma l_dll : dll st l. Proof using Hsc48 HWF L RN. exact (wl_adll st (WF_lists st L HWF) sc Hsc48). Qed.
  Lemma l_nodup : NoDup l. Proof using HWF L RN. exact (wl_anodup st (WF_lists st L HWF) sc). Qed.
  Lemma l_mem : forall x, In x l -> is_group st x /\ g_sc st x = sc /\ metaU st x /\ listed st x /\ x <> m.
  Proof using Hunl HWF L RN.
    intros x Hin. destruct (alist_member st L HWF sc x Hin) as (A & B & C & D & E).
    repeat split; try assumption. intros ->. exact (Hunl E).
  Qed.
  Lemma l_notin : ~ In m l.
  Proof using Hunl HWF L RN. intros Hin. destruct (l_mem m Hin) as (_ & _ & _ & _ & N). exact (N eq_refl). Qed.
  Lemma hd_in : q_nil = false -> In hd l.
  Proof using. intros H. apply head_of_In. apply q_nnil_iff. exact H. Qed.
  Lemma tl_in : q_nil = false -> In tl l.
  Proof using. intros H. apply last_In. apply q_nnil_iff. exact H. Qed.
  Lemma hd_znth : q_nil = false -> hd = znth l 0.
  Proof using. intros H. apply head_of_znth. apply q_nnil_iff. exact H. Qed.
  Lemma l_len : q_nil = false -> 0 < zlen l.
  Proof using. intros H. apply zlen_pos. apply q_nnil_iff. exact H. Qed.

  Lemma m_U : metaU st m. Proof using Hgrp HWF L RN. exact (group_metaU st L HWF m Hgrp). Qed.
  Lemma m_pos : HEAPLO + 24 <= m. Proof using Hgrp HWF L st RN. exact (group_pos st L HWF m Hgrp). Qed.
  Lemma hd_facts : q_nil = false -> is_group st hd /\ g_sc st hd = sc /\ metaU st hd /\ listed st hd /\ hd <> m.
  Proof using Hunl HWF L RN. intros H. exact (l_mem hd (hd_in H)). Qed.
  Lemma tl_facts : q_nil = false -> is_group st tl /\ g_sc st tl = sc /\ metaU st tl /\ listed st tl /\ tl <> m.
  Proof using Hunl HWF L RN. intros H. exact (l_mem tl (tl_in H)). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_areas : s_areas st' = s_areas st. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_alist : forall s, s_alist st' s = if s =? sc then l' else s_alist st s. Proof using. reflexivity. Qed.
  Lemma e_alist_sc : s_alist st' sc = l'. Proof using. rewrite e_alist, Z.eqb_refl. reflexivity. Qed.
  Lemma e_alist_other : forall s, s <> sc -> s_alist st' s = s_alist st s.
  Proof using. intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc); [contradiction | reflexivity]. Qed.
  Lemma e_groups : s_groups st' = s_groups st. Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_slot : s_slot st' = s_slot st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = s_regions st. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. reflexivity. Qed.
  Lemma e_limbo : s_limbo st' = s_limbo st. Proof using. reflexivity. Qed.
  Lemma e_meta : forall x, s_meta st' x = q_meta x. Proof using. reflexivity. Qed.
  Lemma e_next : forall x, mr_next (s_meta st' x) = q_next x. Proof using. reflexivity. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = q_prev x. Proof using. reflexivity. Qed.
  Lemma e_mem : forall x, mr_mem (s_meta st' x) = mr_mem (s_meta st x). Proof using. reflexivity. Qed.
  Lemma e_avail : forall x, mr_avail (s_meta st' x) = mr_avail (s_meta st x). Proof using. reflexivity. Qed.
  Lemma e_freed : forall x, mr_freed (s_meta st' x) = mr_freed (s_meta st x). Proof using. reflexivity. Qed.
  Lemma e_Wr : forall x, mr_W (s_meta st' x) = mr_W (s_meta st x). Proof using. reflexivity. Qed.
  Lemma e_gW : forall x, g_W st' x = g_W st x. Proof using. reflexivity. Qed.
  Lemma e_gmem : forall x, g_mem st' x = g_mem st x. Proof using. reflexivity. Qed.
  Lemma e_glast : forall x, g_lastidx st' x = g_lastidx st x. Proof using. reflexivity. Qed.
  Lemma e_gcnt : forall x, g_cnt st' x = g_cnt st x. Proof using. reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof using. reflexivity. Qed.
  Lemma e_gml : forall x, g_maplen st' x = g_maplen st x. Proof using. reflexivity. Qed.
  Lemma e_gstride : forall x, g_stride st' x = g_stride st x. Proof using. reflexivity. Qed.
  Lemma e_gss : forall x k, g_slot_start st' x k = g_slot_start st x k. Proof using. reflexivity. Qed.
  Lemma e_gse : forall x k, g_slot_end st' x k = g_slot_end st x k. Proof using. reflexivity. Qed.
  Lemma e_ctx_active : forall s, c_active (s_ctx st') s = if s =? sc then head_of l' else c_active (s_ctx st) s.
  Proof using. reflexivity. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using Hsc48. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using Hsc48. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using Hsc48. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using Hsc48. intros; unfold fresh; rewrite e_areas; cbn; tauto. Qed.

  Lemma SLq : same_layout st st'.
  Proof using. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.

  Lemma head_l' : head_of l' = if q_nil then m else hd.
  Proof using.
    unfold l'. case_bool q_nil E.
    - apply q_nil_iff in E. rewrite E. reflexivity.
    - apply head_of_app_nonnil. apply q_nnil_iff. exact E.
  Qed.

  Lemma in_l' : forall x, In x l' <-> In x l \/ x = m.
  Proof using.
    intros x. unfold l'. rewrite in_app_iff. cbn. split.
    - intros [H|[H|[]]]; [left; exact H | right; symmetry; exact H].
    - intros [H|H]; [left; exact H | right; left; symmetry; exact H].
  Qed.

  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x \/ x = m.
  Proof using Hsc48.
    intros x. unfold in_alist. split.
    - intros (s & Hs & Hin). rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [->|Hne].
      + apply in_l' in Hin. destruct Hin as [Hin| ->]; [left; exists sc; split; assumption | right; reflexivity].
      + left. exists s. split; assumption.
    - intros [(s & Hs & Hin)| ->].
      + exists s. split; [exact Hs|]. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact Hin].
        apply in_l'. left. exact Hin.
      + exists sc. split; [exact Hsc48|]. rewrite e_alist_sc. apply in_l'. right. reflexivity.
  Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x \/ x = m.
  Proof using Hsc48. intros x. unfold listed. rewrite e_in_flist, e_in_alist. tauto. Qed.
  Lemma e_listed_other : forall x, x <> m -> (listed st' x <-> listed st x).
  Proof using Hsc48. intros x Hx. rewrite e_listed. split; [intros [H| ->]; [exact H | congruence] | tauto]. Qed.
  Lemma alist_mono : forall s x, In x (s_alist st s) -> In x (s_alist st' s).
  Proof using. intros s x Hin. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|]; [apply in_l'; left; exact Hin | exact Hin]. Qed.

  (* [comment removed for export] *)
  Lemma q_next_other : forall x, x <> m -> (q_nil = false -> x <> tl) -> q_next x = mr_next (s_meta st x).
  Proof using.
    intros x H1 H2. unfold q_next. destruct (Z.eqb_spec x m); [contradiction|].
    case_bool q_nil E; cbn; [reflexivity|]. destruct (Z.eqb_spec x tl); [exfalso; exact (H2 E e) | reflexivity].
  Qed.
  Lemma q_prev_other : forall x, x <> m -> (q_nil = false -> x <> hd) -> q_prev x = mr_prev (s_meta st x).
  Proof using.
    intros x H1 H2. unfold q_prev. destruct (Z.eqb_spec x m); [contradiction|].
    case_bool q_nil E; cbn; [reflexivity|]. destruct (Z.eqb_spec x hd); [exfalso; exact (H2 E e) | reflexivity].
  Qed.
  Lemma q_meta_other : forall x, x <> m -> (q_nil = false -> x <> tl) -> (q_nil = false -> x <> hd) -> q_meta x = s_meta st x.
  Proof using.
    intros x H1 H2 H3. unfold q_meta. rewrite q_next_other, q_prev_other by assumption. apply mr_set_links_id.
  Qed.
  (* [comment removed for export] *)
  Lemma q_meta_nongroup : forall x, ~ is_group st x -> q_meta x = s_meta st x.
  Proof using Hunl Hgrp HWF L RN.
    intros x NG. apply q_meta_other.
    - intros ->. exact (NG Hgrp).
    - intros Hn ->. exact (NG (proj1 (tl_facts Hn))).
    - intros Hn ->. exact (NG (proj1 (hd_facts Hn))).
  Qed.
  (* [comment removed for export] *)
  Lemma q_meta_offlist : forall x, x <> m -> ~ In x l -> q_meta x = s_meta st x.
  Proof using.
    intros x H1 H2. apply q_meta_other; [exact H1 | intros Hn ->; exact (H2 (tl_in Hn)) | intros Hn ->; exact (H2 (hd_in Hn))].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[head_of l' fupd Z.pow NSLOTS AREAMAX HEAPLO CEIL]; try assumption.
    intros s Hs. unfold fupd. destruct (Z.eqb_spec s sc); [reflexivity | apply A4; exact Hs].
  Qed.

  Lemma t_dll_l' : dll st' l'.
  Proof using Hunl Hsc48 HWF L RN.
    apply (proj2 (dll_dllf st' l')). cbn [s_meta st'].
    change (dllf (fun x => mr_next (q_meta x)) (fun x => mr_prev (q_meta x)) l') with (dllf q_next q_prev l').
    unfold l'. case_bool q_nil E.
    - pose proof (proj1 q_nil_iff E) as El. rewrite El. cbn [app]. apply dllf_single.
      + unfold q_next. rewrite Z.eqb_refl, E. reflexivity.
      + unfold q_prev. rewrite Z.eqb_refl, E. reflexivity.
    - pose proof (l_len E) as Hn. pose proof (proj1 (NoDup_ListNoDup _) l_nodup) as ND. pose proof (proj1 (dll_dllf st l) l_dll) as D.
      apply (dllf_app_tail _ _ q_next q_prev l m D Hn ND l_notin).
      + intros k Hk. unfold q_next.
        assert (znth l k <> m) by (intros Em; apply l_notin; rewrite <- Em; apply znth_In; lia).
        assert (znth l k <> tl) by (intros Et; apply (NoDup_znth_inj l k (zlen l - 1) ND) in Et; lia).
        destruct (Z.eqb_spec (znth l k) m); [contradiction|]. rewrite E. cbn. destruct (Z.eqb_spec (znth l k) tl); [contradiction|reflexivity].
      + unfold q_next. destruct (Z.eqb_spec tl m) as [Em|]; [exfalso; exact (proj2 (proj2 (proj2 (proj2 (tl_facts E)))) Em)|].
        rewrite E, Z.eqb_refl. reflexivity.
      + unfold q_next. rewrite Z.eqb_refl, E. exact (hd_znth E).
      + intros k Hk. unfold q_prev.
        assert (znth l k <> m) by (intros Em; apply l_notin; rewrite <- Em; apply znth_In; lia).
        assert (znth l k <> hd) by (intros Et; rewrite (hd_znth E) in Et; apply (NoDup_znth_inj l k 0 ND) in Et; lia).
        destruct (Z.eqb_spec (znth l k) m); [contradiction|]. rewrite E. cbn. destruct (Z.eqb_spec (znth l k) hd); [contradiction|reflexivity].
      + unfold q_prev. rewrite <- (hd_znth E). destruct (Z.eqb_spec hd m) as [Em|]; [exfalso; exact (proj2 (proj2 (proj2 (proj2 (hd_facts E)))) Em)|].
        rewrite E, Z.eqb_refl. reflexivity.
      + unfold q_prev. rewrite Z.eqb_refl, E. reflexivity.
  Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hrest Hunl Hsc48 Hsc Hgrp HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist.
    - apply (dll_ext st st'). 2: exact D1. intros x Hx. rewrite e_meta. rewrite q_meta_nongroup; [split; reflexivity|].
      exact (proj1 (proj2 (FU x Hx))).
    - exact ND1.
    - intros x Hx. destruct (FU x Hx) as (U & NG & NF & Me & Av & Fr & W).
      rewrite e_metaU, e_is_group, e_fresh, e_meta, q_meta_nongroup by exact NG. repeat split; assumption.
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [exact t_dll_l'|].
      apply (dll_ext st st'); [|exact (D2 s Hs)]. intros x Hx. rewrite e_meta. rewrite q_meta_offlist; [split; reflexivity| |].
      + intros ->. apply Hunl. right. exists s. split; assumption.
      + intros Hin. destruct (AU s x Hx) as (_ & _ & S1). destruct (AU sc x Hin) as (_ & _ & S2). congruence.
    - intros s. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (ND2 s)].
      unfold l'. apply (proj2 (NoDup_ListNoDup _)). apply List.NoDup_app; [apply (proj1 (NoDup_ListNoDup _)); exact l_nodup | constructor; [intros [] | constructor] |].
      intros a Ha [<-|[]]. exact (l_notin Ha).
    - intros s x Hin. rewrite e_is_group, e_gsc. rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (AU s x Hin)].
      apply in_l' in Hin. destruct Hin as [Hin| ->]; [exact (AU sc x Hin)|]. split; [exact Hsc48|]. split; [exact Hgrp | exact Hsc].
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [exfalso; lia | exact (AN s Hs)].
    - intros x U NL. rewrite e_metaU in U. rewrite e_listed in NL. rewrite e_next, e_prev.
      assert (x <> m) by (intros ->; apply NL; right; reflexivity).
      rewrite q_next_other, q_prev_other; [apply LK; [exact U | intros Hl; apply NL; left; exact Hl] | exact H | | exact H |].
      + intros Hn ->. apply NL. left. exact (proj1 (proj2 (proj2 (proj2 (hd_facts Hn))))).
      + intros Hn ->. apply NL. left. exact (proj1 (proj2 (proj2 (proj2 (tl_facts Hn))))).
    - intros x Hl. rewrite e_next, e_prev. rewrite e_listed in Hl.
      pose proof m_pos as MP.
      assert (Hm0 : m <> 0) by (hsep; unfold HEAPLO in MP; lia).
      assert (Hhd0 : q_nil = false -> hd <> 0).
      { intros Hn E0. pose proof (group_pos st L HWF hd (proj1 (hd_facts Hn))). hsep; unfold HEAPLO in *. lia. }
      assert (Htl0 : q_nil = false -> tl <> 0).
      { intros Hn E0. pose proof (group_pos st L HWF tl (proj1 (tl_facts Hn))). hsep; unfold HEAPLO in *. lia. }
      assert (OLD : x <> m -> mr_next (s_meta st x) <> 0 /\ mr_prev (s_meta st x) <> 0).
      { intros Hxm. apply LKD. destruct Hl as [Hl| ->]; [exact Hl | congruence]. }
      unfold q_next, q_prev. destruct (Z.eqb_spec x m) as [->|Hxm].
      + case_bool q_nil En; split; auto.
      + specialize (OLD Hxm). destruct OLD as [O1 O2].
        case_bool q_nil En; cbn [negb andb]; [split; assumption|].
        destruct (Z.eqb_spec x tl); destruct (Z.eqb_spec x hd); split; assumption.
    - intros s x Hin Hne. rewrite e_avail, e_freed. rewrite e_alist in Hin, Hne.
      destruct (Z.eqb_spec s sc) as [->|Hs]; [|exact (RS s x Hin Hne)].
      rewrite head_l' in Hne. apply in_l' in Hin. destruct Hin as [Hin| ->].
      + revert Hne. case_bool q_nil En; intros Hne; [apply q_nil_iff in En; rewrite En in Hin; destruct Hin|]. exact (RS sc x Hin Hne).
      + revert Hne. case_bool q_nil En; intros Hne; [congruence|]. exact (Hrest En).
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L x.
  Proof using Hnotfull Hsc48 Hsc Hgrp HWF RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    pose proof (group_pos st L HWF x Hx) as XP.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_kind, ?e_slot, ?e_avail, ?e_freed;
      try assumption.
    - (* [comment removed for export] *) intros Hal. apply e_in_alist in Hal. destruct Hal as [Hal| ->].
      + apply alist_mono. exact (Lsc Hal).
      + rewrite Hsc, e_alist_sc. apply in_l'. right; reflexivity.
    - (* [comment removed for export] *) intros H63 Hl. apply e_listed in Hl. destruct Hl as [Hl| ->]; [exact (S63 H63 Hl)|]. rewrite Hsc in H63. lia.
    - (* [comment removed for export] *) intros Hp. apply alist_mono. exact (Part Hp).
    - (* [comment removed for export] *) intros Hall Hne Hl. apply e_listed in Hl. destruct Hl as [Hl| ->].
      + apply (Full Hall); [|exact Hl]. rewrite e_alist in Hne. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hne].
        rewrite head_l' in Hne. revert Hne. case_bool q_nil En; intros Hne.
        * apply q_nil_iff in En. rewrite E, En. cbn. hsep; unfold HEAPLO in XP. lia.
        * rewrite E. exact Hne.
      + destruct Hnotfull as (k & Hk & [HS|HS]); destruct (Hall k Hk) as [A B]; [exact (A HS) | exact (B HS)].
    - (* [comment removed for export] *) intros Hall. destruct (FF Hall) as (K & S48 & Hh). split; [exact K|]. split; [exact S48|].
      rewrite e_alist. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hh].
      unfold l'. apply in_app_iff. left. rewrite <- E. exact Hh.
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hnotfull Hunl Hsc48 Hsc Hgrp HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo.
    - exact ND.
    - intros x Hx. apply t_wf_group. exact Hx.
    - intros m1 m2 H1 H2. rewrite !e_ai, !e_glast, !e_gsc. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. rewrite e_regions in Hin. rewrite e_is_group, e_kind, e_gmem, e_gml. exact (REG b len x Hin).
    - intros x F. apply e_fresh in F. rewrite e_meta, q_meta_nongroup; [exact (FR0 x F)|].
      intros Hx. exact (wg_notfresh st L x (EACH x Hx) F).
    - intros x U NG NFL NFR. apply (OTH x); [apply e_metaU; exact U | rewrite <- e_is_group; exact NG
        | rewrite <- e_in_flist; exact NFL | rewrite <- e_fresh; exact NFR].
    - intros x Hl. destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_fresh, e_listed.
      repeat split; try assumption. intros [Hx| ->]; [exact (C Hx) | exact (B Hgrp)].
    - intros m1 m2 H1 H2 G1 G2 E. rewrite !e_gsc in E. rewrite !e_glast in G1, G2. rewrite !e_slot in G1, G2. exact (ONEFF m1 m2 H1 H2 G1 G2 E).
  Qed.

  Lemma t_WF : WF st' L.
  Proof using Hnotfull Hrest Hunl Hsc48 Hsc Hgrp HWF.
    split; [exact t_wf_ctx|]. split; [exact (wf_areas_ext st st' SLq (WF_areas st L HWF))|]. split; [exact t_wf_lists|].
    split; [exact t_wf_groups|]. split; [exact (wf_geom_ext st st' L SLq HWF (WF_geom st L HWF))|].
    split; [exact (wf_live_ext st st' L SLq (WF_live st L HWF)) |]. split; [exact (wf_regions_ext st st' L SLq HWF eq_refl (WF_regions st L HWF)) | exact (wf_img_ext st st' SLq (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition q_wr (a : Z) : Prop :=
    (sp - MSTK <= a < sp) \/ (m <= a < m + 16) \/
    (q_nil = false /\ ((tl + 8 <= a < tl + 16) \/ (hd <= a < hd + 8))) \/
    (q_nil = true /\ ctx_active sc <= a < ctx_active sc + 8).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> q_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMm0 : cell M' m 8 (q_prev m).
  Hypothesis HMm8 : cell M' (m + 8) 8 (q_next m).
  Hypothesis HMtl : q_nil = false -> cell M' (tl + 8) 8 m.
  Hypothesis HMhd : q_nil = false -> cell M' hd 8 m.
  Hypothesis HMact : q_nil = true -> cell M' (ctx_active sc) 8 m.

  (* [comment removed for export] *)
  Lemma hd_rng : q_nil = false -> HEAPLO + 24 <= hd /\ hd + 40 <= CEIL.
  Proof using Hunl HWF m L. intros Hn. destruct (metaU_rng st L HWF hd (proj1 (proj2 (proj2 (hd_facts Hn))))) as (A & B & _). lia. Qed.

  Lemma m_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL.
  Proof using Hgrp HWF L st. destruct (metaU_rng st L HWF m m_U) as (A & B & _). lia. Qed.

  (* [comment removed for export] *)
  Lemma wr_cases : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    CEIL <= a \/ (exists x, metaU st x /\ (x = m \/ (q_nil = false /\ (x = tl \/ x = hd))) /\ x <= a < x + 40)
    \/ (q_nil = true /\ ctx_active sc <= a < ctx_active sc + 8).
  Proof using HMwr Hsp Hunl Hgrp HWF sp L.
    intros a Hr NE. destruct (HMwr a Hr NE) as [W|[W|[[Hn [W|W]]|W]]].
    - left. ceil; unfold MSTK in *. lia.
    - right; left. exists m. split; [exact m_U|]. split; [left; reflexivity | lia].
    - right; left. exists tl. split; [exact (proj1 (proj2 (proj2 (tl_facts Hn))))|]. split; [right; split; [exact Hn | left; reflexivity] | lia].
    - right; left. exists hd. split; [exact (proj1 (proj2 (proj2 (hd_facts Hn))))|]. split; [right; split; [exact Hn | right; reflexivity] | lia].
    - right; right. exact W.
  Qed.

  Definition XMq (x : Z) : bool := (x =? m) || (negb q_nil && ((x =? tl) || (x =? hd))).
  Definition XAq (s : Z) : bool := q_nil && (s =? sc).

  Lemma t_rep_meta_m : rep_meta M' m (q_meta m).
  Proof using HMm8 HMm0 HMwr Hsp Hunl Hsc48 Hgrp HREP HWF sp M L RN.
    pose proof (metaU_area st L HWF m m_U) as (ar & k & Har & Hk & Hm & _).
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hm in RM.
    destruct RM as [P N Me Av Fr Wc]. pose proof m_rng as [R1 R2].
    assert (AG : agree_on (fun a => m + 16 <= a < m + 40) M M').
    { intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[W|[[Hn [W|W]]|[_ W]]]].
      - ceil; unfold MSTK in *; lia.
      - lia.
      - destruct (metaU_sep st L HWF m tl m_U (proj1 (proj2 (proj2 (tl_facts Hn)))) ltac:(intros E; exact (proj2 (proj2 (proj2 (proj2 (tl_facts Hn)))) (eq_sym E)))); lia.
      - destruct (metaU_sep st L HWF m hd m_U (proj1 (proj2 (proj2 (hd_facts Hn)))) ltac:(intros E; exact (proj2 (proj2 (proj2 (proj2 (hd_facts Hn)))) (eq_sym E)))); lia.
      - pose proof (metaU_img st L HWF m m_U). hsep; unfold ctx_active, CTX, HEAPLO in *. lia. }
    unfold q_meta, mr_set_links. constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - exact HMm0.
    - exact HMm8.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma t_rep_meta_end : forall x, q_nil = false -> (x = tl \/ x = hd) -> rep_meta M' x (q_meta x).
  Proof using HMhd HMtl HMwr Hsp Hunl Hgrp HREP HWF sp M L RN.
    intros x Hn Hx.
    assert (Ux : metaU st x) by (destruct Hx as [-> | ->]; [exact (proj1 (proj2 (proj2 (tl_facts Hn)))) | exact (proj1 (proj2 (proj2 (hd_facts Hn))))]).
    assert (Hxm : x <> m) by (destruct Hx as [-> | ->]; [exact (proj2 (proj2 (proj2 (proj2 (tl_facts Hn))))) | exact (proj2 (proj2 (proj2 (proj2 (hd_facts Hn)))))]).
    pose proof (metaU_area st L HWF x Ux) as (ar & k & Har & Hk & Hxa & _).
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hxa in RM.
    destruct RM as [P N Me Av Fr Wc]. destruct (metaU_rng st L HWF x Ux) as (R1 & R2 & _).
    pose proof (metaU_sep st L HWF x m Ux m_U Hxm) as SEPm.
    (* [comment removed for export] *)
    assert (AG : agree_on (fun a => x <= a < x + 40 /\ ~ (x = hd /\ x <= a < x + 8) /\ ~ (x = tl /\ x + 8 <= a < x + 16)) M M').
    { intros a Hr (Ha & N1 & N2). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[W|[[_ [W|W]]|[W _]]]].
      - ceil; unfold MSTK in *. lia.
      - lia.
      - destruct (Z.eq_dec x tl) as [E|NEt]; [apply N2; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x tl Ux (proj1 (proj2 (proj2 (tl_facts Hn)))) NEt); lia.
      - destruct (Z.eq_dec x hd) as [E|NEh]; [apply N1; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x hd Ux (proj1 (proj2 (proj2 (hd_facts Hn)))) NEh); lia.
      - congruence. }
    unfold q_meta, mr_set_links, q_next, q_prev. destruct (Z.eqb_spec x m); [contradiction|]. rewrite Hn. cbn [negb andb].
    constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - destruct (Z.eqb_spec x hd) as [E|NE].
      + rewrite E at 1. exact (HMhd Hn).
      + eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact P]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - destruct (Z.eqb_spec x tl) as [E|NE].
      + rewrite E at 1. exact (HMtl Hn).
      + eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact N]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMact HMhd HMtl HMm8 HMm0 HMgrow HMwr Hsp Hunl Hsc48 Hgrp HREP HWF sp M L RN.
    pose proof m_rng as [MR1 MR2].
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|[_ W]]].
      + ceil; unfold CTX in *; lia.
      + destruct (metaU_rng st L HWF x Ux). hsep; unfold HEAPLO, CTX in *; lia.
      + unfold ctx_active, CTX in *; lia.
    - apply (rep_ctx_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow) XAq false); try reflexivity.
      + intros a Hr (Ha & NA & NF). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|[Hn W]]].
        * ceil; unfold CTX_END, CTX in *; lia.
        * destruct (metaU_rng st L HWF x Ux). hsep; unfold HEAPLO, CTX_END, CTX in *; lia.
        * apply NA. exists sc. split; [exact Hsc48|]. split; [unfold XAq; rewrite Hn, Z.eqb_refl; reflexivity | exact W].
      + intros s Hs. unfold XAq. rewrite e_ctx_active. destruct (Z.eqb_spec s sc) as [->|Hne].
        * rewrite head_l'. case_bool q_nil En; cbn [andb].
          -- left. split; [reflexivity|]. exact (HMact En).
          -- right. split; [reflexivity|]. symmetry. exact (wc_active st (WF_ctx st L HWF) sc Hsc48).
        * right. rewrite Bool.andb_false_r. split; reflexivity.
      + right. split; reflexivity.
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) XMq); try reflexivity.
      + intros ar a Har Ha NE. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(x & Ux & Hx & W)|[Hn W]]].
        * ceil; lia.
        * exists x. split; [exact Ux|]. split; [|exact W]. unfold XMq.
          destruct Hx as [->|[Hn [->| ->]]]; rewrite ?Z.eqb_refl, ?Hn; cbn; rewrite ?Bool.orb_true_r; reflexivity.
        * hsep; unfold ctx_active, CTX, HEAPLO in *; lia.
      + intros x Ux X. unfold XMq in X. rewrite e_meta. destruct (Z.eqb_spec x m) as [->|Hxm]; [exact t_rep_meta_m|].
        cbn [orb] in X. revert X. case_bool q_nil En; intros X; [discriminate X|]. cbn [negb andb] in X.
        apply t_rep_meta_end; [exact En|].
        destruct (Z.eqb_spec x tl); [left; assumption|]. destruct (Z.eqb_spec x hd); [right; assumption|]. discriminate X.
      + intros x Ux X. unfold XMq in X. rewrite e_meta. apply Bool.orb_false_elim in X. destruct X as [X1 X2].
        apply q_meta_other.
        * intros ->. rewrite Z.eqb_refl in X1. discriminate X1.
        * intros Hn ->. rewrite Hn, Z.eqb_refl in X2. discriminate X2.
        * intros Hn ->. rewrite Hn, Z.eqb_refl, Bool.orb_true_r in X2. discriminate X2.
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)).
      + intros x Hx. apply e_is_group. exact Hx.
      + intros x Hx. repeat split; reflexivity.
      + intros x Hx E. apply (x_endb st st' L SLq HWF); [exact Hx|]. exact E.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. apply e_is_group in Hx. apply (x_gcell st st' L SLq HWF) in G; [|exact Hx].
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(y & Uy & _ & W)|[Hn W]]].
        * ceil; lia.
        * exact (gcell_not_meta st L HWF x y a Hx G Uy W).
        * hsep; unfold ctx_active, CTX, HEAPLO in *; lia.
      + intros x a Hx G. left. apply (x_gcell st st' L SLq HWF); [apply e_is_group; exact Hx|]. exact G.
  Qed.

  Theorem queue_close : WF st' L /\ REP st' M'.
  Proof using HMact HMhd HMtl HMm8 HMm0 HMgrow HMwr Hsp Hnotfull Hrest Hunl Hsc48 Hsc Hgrp HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.
End Queue.
