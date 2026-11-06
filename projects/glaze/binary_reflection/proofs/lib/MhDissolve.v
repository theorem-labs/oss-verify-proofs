(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rkind_eqb (a b : rkind) : bool :=
  match a, b with
  | RBrk, RBrk => true
  | RMeta e, RMeta e' => e =? e'
  | RGroup m, RGroup m' => m =? m'
  | _, _ => false
  end.
Definition region_eqb (r1 r2 : region) : bool :=
  (rg_base r1 =? rg_base r2) && (rg_len r1 =? rg_len r2) && rkind_eqb (rg_kind r1) (rg_kind r2).
Lemma region_eqb_eq : forall r1 r2, region_eqb r1 r2 = true <-> r1 = r2.
Proof.
  intros [b1 l1 k1] [b2 l2 k2]. unfold region_eqb. cbn. rewrite !Bool.andb_true_iff, !Z.eqb_eq.
  split.
  - intros [[-> ->] K]. destruct k1, k2; cbn in K; try discriminate K; try reflexivity; apply Z.eqb_eq in K; subst; reflexivity.
  - intros E. injection E. intros -> -> ->. repeat split. destruct k2; cbn; rewrite ?Z.eqb_refl; reflexivity.
Qed.
Definition rremove (r : region) (l : list region) : list region := List.filter (fun x => negb (region_eqb x r)) l.
Lemma rremove_In : forall r l x, In x (rremove r l) <-> In x l /\ x <> r.
Proof.
  intros r l x. unfold rremove. rewrite filter_In. destruct (region_eqb x r) eqn:E; cbn.
  - apply region_eqb_eq in E. split; [intros [_ H]; discriminate H | intros [_ H]; congruence].
  - split; [intros [H _]; split; [exact H|]; intros ->; rewrite (proj2 (region_eqb_eq r r) eq_refl) in E; discriminate E | tauto].
Qed.
Lemma rremove_notin : forall r l, ~ In r l -> rremove r l = l.
Proof.
  intros r l H. unfold rremove. induction l as [|a l IH]; [reflexivity|]. cbn.
  destruct (region_eqb a r) eqn:E; cbn.
  - apply region_eqb_eq in E. exfalso. apply H. left. exact E.
  - f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.
Lemma rremove_perm : forall r l, NoDup l -> In r l -> Permutation l (r :: rremove r l).
Proof.
  intros r l ND Hin. apply NoDup_ListNoDup in ND. destruct (in_split r l Hin) as (l1 & l2 & ->).
  pose proof (NoDup_remove_2 l1 l2 r ND) as NI. rewrite in_app_iff in NI.
  unfold rremove. rewrite filter_app. cbn. rewrite (proj2 (region_eqb_eq r r) eq_refl). cbn.
  fold (rremove r l1). fold (rremove r l2). rewrite !rremove_notin by tauto.
  apply Permutation_sym. apply Permutation_middle.
Qed.


Section Dissolve.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (g : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st g.
  Hypothesis Hfj : free_or_junk st g.
  #[local] Notation sc := (g_sc st g).
  #[local] Notation l := (s_alist st sc).
  #[local] Notation nxt := (mr_next (s_meta st g)).
  #[local] Notation prv := (mr_prev (s_meta st g)).
  (* [comment removed for export] *)
  Definition inl : bool := if in_dec Z.eq_dec g l then true else false.
  Definition multi : bool := inl && negb (zlen l =? 1).
  Definition l' : list Z := zremove g l.
  Definition rg : region := RG (g_mem st g) (4096 * g_maplen st g) (RGroup g).

  Definition d_next (x : Z) : Z :=
    if x =? g then 0 else if (multi && (x =? prv))%bool then nxt else mr_next (s_meta st x).
  Definition d_prev (x : Z) : Z :=
    if x =? g then 0 else if (multi && (x =? nxt))%bool then prv else mr_prev (s_meta st x).
  Definition d_meta (x : Z) : meta_rec := mr_set_links (s_meta st x) (d_prev x) (d_next x).
  Definition is_hslot (x k : Z) : bool :=
    match s_kind st g with GTop => false | GNest hm hi _ => (x =? hm) && (k =? hi) end.
  Definition hoff : Z := match s_kind st g with GTop => 0 | GNest _ _ o => o end.
  Definition d_slot (x k : Z) : slot_st := if is_hslot x k then SJunk hoff else s_slot st x k.
  Definition d_regions : list region :=
    match s_kind st g with GTop => rremove rg (s_regions st) | GNest _ _ _ => s_regions st end.
  Definition st' : mst :=
    MST (cx_set_active (s_ctx st) (fupd (c_active (s_ctx st)) sc (head_of l')))
        (s_areas st) d_meta (s_flist st) (fupd (s_alist st) sc l') (zremove g (s_groups st)) (s_ai st) (s_kind st)
        d_slot d_regions (s_brk st) (s_canary st) (s_errno st) (g :: s_limbo st).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma g_wfg : wf_group st L g. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) g Hgrp). Qed.
  Lemma g_U : metaU st g. Proof using Hgrp HWF L RN. exact (wg_U st L g g_wfg). Qed.
  Lemma g_rng : HEAPLO + 24 <= g /\ g + 40 <= CEIL.
  Proof using Hgrp HWF L st. destruct (metaU_rng st L HWF g g_U) as (A & B & _). lia. Qed.
  Lemma sc_rng : 0 <= sc < 64. Proof using. unfold g_sc, w_sizeclass. apply Z.mod_pos_bound. lia. Qed.
  Lemma g_childless : childless st g. Proof using Hfj. exact (free_or_junk_childless st g Hfj). Qed.
  Lemma g_nouser : forall k p n o r, 0 <= k <= g_lastidx st g -> s_slot st g k <> SUser p n o r.
  Proof using Hfj. intros k p n o r Hk E. destruct (Hfj k Hk) as [A|[A|[o' A]]]; rewrite E in A; discriminate A. Qed.

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
  Lemma e_areas : s_areas st' = s_areas st. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_alist : forall s, s_alist st' s = if s =? sc then l' else s_alist st s. Proof using. reflexivity. Qed.
  Lemma e_alist_sc : s_alist st' sc = l'. Proof using. rewrite e_alist, Z.eqb_refl. reflexivity. Qed.
  Lemma e_alist_other : forall s, s <> sc -> s_alist st' s = s_alist st s.
  Proof using. intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc); [contradiction | reflexivity]. Qed.
  Lemma e_groups : s_groups st' = zremove g (s_groups st). Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_slot : forall x k, s_slot st' x k = d_slot x k. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = d_regions. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. reflexivity. Qed.
  Lemma e_limbo : s_limbo st' = g :: s_limbo st. Proof using. reflexivity. Qed.
  Lemma e_meta : forall x, s_meta st' x = d_meta x. Proof using. reflexivity. Qed.
  Lemma e_next : forall x, mr_next (s_meta st' x) = d_next x. Proof using. reflexivity. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = d_prev x. Proof using. reflexivity. Qed.
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
  Lemma e_gspan : forall x, gspan st' x = gspan st x. Proof using. reflexivity. Qed.
  Lemma e_inband : forall x q, inband st' x q = inband st x q. Proof using. reflexivity. Qed.
  Lemma e_ptr_ok : forall x k q, ptr_ok st' x k q <-> ptr_ok st x k q. Proof using. intros. unfold ptr_ok. cbn -[Z.pow size_class Z.mul Z.add Z.sub]. tauto. Qed.
  Lemma e_endb : forall x, endb_own st' x <-> endb_own st x. Proof using. intros. unfold endb_own. cbn -[Z.sub Z.lt gspan g_slot_end]. tauto. Qed.
  Lemma e_ctx_active : forall s, c_active (s_ctx st') s = if s =? sc then head_of l' else c_active (s_ctx st) s.
  Proof using. reflexivity. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x /\ x <> g.
  Proof using. intros; unfold is_group; rewrite e_groups. apply zremove_In. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using. intros; unfold fresh; rewrite e_areas; cbn; tauto. Qed.
  Lemma e_areab : forall a, areab st' a <-> areab st a. Proof using. intros; unfold areab; rewrite e_areas; tauto. Qed.
  Lemma e_depth : forall f x, nest_depth_le st' f x <-> nest_depth_le st f x.
  Proof using. induction f as [|f IH]; intros x; cbn; change (s_kind st' x) with (s_kind st x); destruct (s_kind st x); try tauto. Qed.

  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x /\ x <> g.
  Proof using HWF L RN.
    intros x. unfold in_alist. split.
    - intros (s & Hs & Hin). rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [->|Hne].
      + apply l'_sub in Hin. destruct Hin as [Hin Hx]. split; [exists sc; split; assumption | exact Hx].
      + split; [exists s; split; assumption|]. intros ->.
        destruct (wl_aU st (WF_lists st L HWF) s g Hin) as (_ & _ & E). apply Hne. symmetry. exact E.
    - intros [(s & Hs & Hin) Hx]. exists s. split; [exact Hs|]. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact Hin].
      apply l'_sub. split; assumption.
  Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x /\ x <> g.
  Proof using Hgrp HWF L RN.
    intros x. unfold listed. rewrite e_in_flist, e_in_alist. split; [|tauto].
    intros [F|[A N]]; [|tauto]. split; [left; exact F|]. intros ->. exact (wg_notfree st L g g_wfg F).
  Qed.

  (* [comment removed for export] *)
  Lemma hslot_cases : forall x k, (is_hslot x k = false /\ d_slot x k = s_slot st x k)
    \/ (exists hm hi o, s_kind st g = GNest hm hi o /\ x = hm /\ k = hi /\ is_hslot x k = true /\ d_slot x k = SJunk o /\ s_slot st x k = SHost g o).
  Proof using Hgrp HWF L RN.
    intros x k. unfold d_slot, is_hslot, hoff. destruct (s_kind st g) as [|hm hi o] eqn:K; [left; split; reflexivity|].
    destruct (Z.eqb_spec x hm) as [->|]; destruct (Z.eqb_spec k hi) as [->|]; cbn; try (left; split; reflexivity).
    right. exists hm, hi, o. repeat split; try reflexivity.
    pose proof (wg_kind st L g g_wfg) as KD. rewrite K in KD. destruct KD as (_ & _ & _ & _ & _ & K6 & _). exact K6.
  Qed.
  Lemma d_slot_user : forall x k p n o r, d_slot x k = SUser p n o r <-> s_slot st x k = SUser p n o r.
  Proof using Hgrp HWF L RN.
    intros x k p n o r. destruct (hslot_cases x k) as [[_ E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E; [tauto|].
    rewrite S. split; intros H; discriminate H.
  Qed.
  Lemma d_slot_avail : forall x k, d_slot x k = SAvail <-> s_slot st x k = SAvail.
  Proof using Hgrp HWF L RN.
    intros x k. destruct (hslot_cases x k) as [[_ E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E; [tauto|].
    rewrite S. split; intros H; discriminate H.
  Qed.
  Lemma d_slot_freed : forall x k, d_slot x k = SFreed <-> s_slot st x k = SFreed.
  Proof using Hgrp HWF L RN.
    intros x k. destruct (hslot_cases x k) as [[_ E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E; [tauto|].
    rewrite S. split; intros H; discriminate H.
  Qed.


  Lemma e_gcell : forall x a, gcell st' x a <-> gcell st x a.
  Proof using Hgrp HWF L RN.
    intros x a. unfold gcell. rewrite e_gmem, e_gcnt, e_glast.
    assert (SP : forall k, slot_ptr st' x k = slot_ptr st x k).
    { intros k. unfold slot_ptr. rewrite e_slot, e_gss.
      destruct (hslot_cases x k) as [[_ E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E; [reflexivity|]. rewrite S. reflexivity. }
    assert (E2 : forall k, (k < g_cnt st x \/ endb_own st' x) <-> (k < g_cnt st x \/ endb_own st x)) by (intros; rewrite e_endb; tauto).
    split; intros [G|[G|[G|G]]].
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite e_gss in B. rewrite <- E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite SP in B. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite e_slot, d_slot_user in B. rewrite e_gse in C. tauto.
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite e_gss. rewrite E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite SP. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite e_slot, d_slot_user, e_gse. tauto.
  Qed.
  Lemma e_appb : forall a, appb st' a <-> appb st a.
  Proof using Hfj Hgrp HWF L RN.
    intros a. unfold appb. split; intros (x & k & q & n & o & r & A & B & C & D); exists x, k, q, n, o, r.
    - rewrite e_glast in B. rewrite e_slot, d_slot_user in C. apply e_is_group in A. tauto.
    - rewrite e_glast, e_slot, d_slot_user. split; [|tauto]. apply e_is_group. split; [exact A|].
      intros ->. exact (g_nouser k q n o r B C).
  Qed.

  (* [comment removed for export] *)
  Lemma d_regions_sub : forall r, In r d_regions -> In r (s_regions st).
  Proof using. intros r Hr. unfold d_regions in Hr. destruct (s_kind st g); [apply rremove_In in Hr; tauto | exact Hr]. Qed.
  Lemma d_regions_keep : forall r, In r (s_regions st) -> rg_kind r <> RGroup g -> In r d_regions.
  Proof using.
    intros r Hr Hk. unfold d_regions. destruct (s_kind st g); [|exact Hr]. apply rremove_In. split; [exact Hr|].
    intros ->. apply Hk. reflexivity.
  Qed.
  Lemma d_regions_nodup : NoDup d_regions.
  Proof using HWF L RN.
    pose proof (wr_nodup st (WF_regions st L HWF)) as ND. unfold d_regions. destruct (s_kind st g); [|exact ND].
    apply NoDup_ListNoDup. unfold rremove. apply NoDup_filter. apply NoDup_ListNoDup. exact ND.
  Qed.
  Lemma filter_count_le : forall (f : region -> bool), (length (List.filter f d_regions) <= length (List.filter f (s_regions st)))%nat.
  Proof using.
    intros f. unfold d_regions. destruct (s_kind st g); [|lia]. unfold rremove.
    induction (s_regions st) as [|a rs IH]; cbn; [lia|].
    destruct (region_eqb a rg); cbn; destruct (f a); cbn; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[head_of l' fupd Z.pow NSLOTS AREAMAX HEAPLO CEIL d_regions]; try assumption.
    - intros s Hs. unfold fupd. destruct (Z.eqb_spec s sc); [reflexivity | apply A4; exact Hs].
    - intros Hc. destruct (A8 Hc) as (b & len & e & Hin & He & C1 & C2). exists b, len, e.
      split; [apply d_regions_keep; [exact Hin | cbn; discriminate] | repeat split; assumption].
  Qed.

  Lemma t_wf_areas : wf_areas st'.
  Proof using HWF L.
    destruct (WF_areas st L HWF) as [A B C D]. constructor; rewrite ?e_areas, ?e_regions, ?e_brk; try assumption.
    intros a Ha. destruct (D a Ha) as [(b & len & Hin & X)|(b & len & e & Hin & X)].
    - left. exists b, len. split; [apply d_regions_keep; [exact Hin | cbn; discriminate] | exact X].
    - right. exists b, len, e. split; [apply d_regions_keep; [exact Hin | cbn; discriminate] | exact X].
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
      rewrite e_metaU, e_is_group, e_fresh, e_meta, d_meta_nongroup by exact NG. repeat split; try assumption. tauto.
    - intros s Hs. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [exact t_dll_l'|].
      apply (dll_ext st st'); [|exact (D2 s Hs)]. intros x Hx. rewrite e_meta. rewrite d_meta_offlist; [split; reflexivity| |].
      + intros ->. destruct (AU s g Hx) as (_ & _ & E). exact (Hne (eq_sym E)).
      + intros Hin. destruct (AU s x Hx) as (_ & _ & S1). destruct (AU sc x Hin) as (_ & _ & S2). congruence.
    - intros s. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|Hne]; [|exact (ND2 s)].
      unfold l'. apply (proj2 (NoDup_ListNoDup _)). apply zremove_NoDup. exact l_nodup.
    - intros s x Hin. rewrite e_is_group, e_gsc. rewrite e_alist in Hin. destruct (Z.eqb_spec s sc) as [->|Hne].
      + apply l'_sub in Hin. destruct Hin as [Hin Hx]. pose proof (AU sc x Hin). tauto.
      + pose proof (AU s x Hin) as (A & B & C). split; [exact A|]. split; [split; [exact B|] | exact C]. intros ->. apply Hne. symmetry. exact C.
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

  Lemma t_wf_ctx_groups_aux : forall x, is_group st x -> x <> g ->
    (forall s, In x (s_alist st s) -> In x (s_alist st' s)).
  Proof using.
    intros x Hx Hxg s Hin. rewrite e_alist. destruct (Z.eqb_spec s sc) as [->|]; [apply l'_sub; split; assumption | exact Hin].
  Qed.

  Lemma t_slot_wf : forall x k, is_group st x -> x <> g -> 0 <= k <= g_lastidx st x ->
    slot_wf st L x k (s_slot st x k) -> slot_wf st' L x k (d_slot x k).
  Proof using Hgrp HWF RN.
    intros x k Hx Hxg Hk SW.
    destruct (hslot_cases x k) as [[Hh E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E.
    - destruct (s_slot st x k) as [| |q n o r|c o|o] eqn:Sk; cbn [slot_wf] in *; try exact I.
      + rewrite e_gss, e_gstride. destruct SW as (A & B & C & D & E0 & F & G). conjs; try assumption; try lia. all: apply e_ptr_ok; exact F.
      + rewrite e_gss, e_kind. destruct SW as (A & B & C & D & E0).
        assert (HG : is_group st' c).
        { apply e_is_group. split; [exact B|]. intros ->. unfold is_hslot in Hh. rewrite D, !Z.eqb_refl in Hh. discriminate Hh. }
        conjs; try assumption. all: apply e_ptr_ok; exact E0.
      + rewrite e_gss, e_gstride. destruct SW as (A & B & C). conjs; try assumption. all: apply e_ptr_ok; exact C.
    - (* [comment removed for export] *)
      rewrite S in SW. cbn [slot_wf] in SW |- *. destruct SW as (A & B & C & D & E0). rewrite e_gss, e_gstride.
      assert (PO : ptr_ok st' hm hi (g_slot_start st hm hi + 16 * o')) by (apply e_ptr_ok; exact E0).
      conjs; [exact A| |exact PO].
      pose proof (wg_kind st L g g_wfg) as KD. rewrite K in KD.
      destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      pose proof (wg_stride st L g g_wfg) as [S16 _]. unfold UNIT, IB in *. nia.
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> x <> g -> wf_group st' L x.
  Proof using Hfj Hgrp HWF RN.
    intros x Hx Hxg. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    pose proof (group_pos st L HWF x Hx) as XP.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_kind, ?e_avail, ?e_freed;
      try assumption.
    - intros k Hk. rewrite e_slot, d_slot_avail. exact (Av k Hk).
    - intros k Hk. rewrite e_slot, d_slot_freed. exact (Fr k Hk).
    - intros k Hk. rewrite e_slot, d_slot_avail. exact (Avai k Hk).
    - intros k Hk. rewrite e_slot. apply (proj2 (d_slot_freed x k)). exact (High k Hk).
    - (* [comment removed for export] *) intros Hal. apply e_in_alist in Hal. destruct Hal as [Hal _]. apply t_wf_ctx_groups_aux; [exact Hx | exact Hxg | exact (Lsc Hal)].
    - (* [comment removed for export] *) intros H63 Hl. apply e_listed in Hl. exact (S63 H63 (proj1 Hl)).
    - (* [comment removed for export] *) intros Hp. apply t_wf_ctx_groups_aux; [exact Hx | exact Hxg | exact (Part Hp)].
    - (* [comment removed for export] *) intros Hall Hne Hl. apply e_listed in Hl. destruct Hl as [Hl _].
      assert (Hall0 : forall i, 0 <= i <= g_lastidx st x -> s_slot st x i <> SAvail /\ s_slot st x i <> SFreed).
      { intros k Hk. destruct (Hall k Hk) as [A B]. rewrite e_slot, d_slot_avail in A. rewrite e_slot, d_slot_freed in B. split; assumption. }
      apply (Full Hall0); [|exact Hl]. rewrite e_alist in Hne. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hne].
      (* [comment removed for export] *)
      intros Exh. rewrite E in Exh. case_bool inl Hi.
      + destruct (l_split Hi) as (l1 & l2 & El & El' & N1 & N2).
        destruct (head_l' Hi l1 l2 El El') as [(A & B & C)|(A & B & C)].
        * (* [comment removed for export] *)
          destruct Hl as [Hf|(s & Hs & Hin)]; [exact (Nfr Hf)|].
          destruct (wl_aU st (WF_lists st L HWF) s x Hin) as (_ & _ & Es). rewrite <- Es, E in Hin.
          destruct (wl_rest st (WF_lists st L HWF) sc x Hin ltac:(rewrite B; exact Hxg)) as [_ FRx].
          (* [comment removed for export] *)
          apply FRx. apply Z.bits_inj_0. intros j. destruct (Z.lt_ge_cases j 0) as [Hj|Hj]; [apply Z.testbit_neg_r; exact Hj|].
          destruct (Z.testbit (mr_freed (s_meta st x)) j) eqn:T; [|reflexivity]. exfalso.
          apply (proj1 (Fr j Hj)) in T. destruct T as [T1 T2]. exact (proj2 (Hall0 j ltac:(lia)) T2).
        * apply Hne. rewrite B. exact Exh.
      + apply Hne. rewrite (l'_unl Hi). exact Exh.
    - (* [comment removed for export] *) pose proof Kind as KD. destruct (s_kind st x) as [|hm j o] eqn:Kx.
      + destruct KD as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [|split; assumption].
        apply d_regions_keep; [exact K2 | cbn; intros E; injection E; intros; exact (Hxg ltac:(assumption))].
      + destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride, e_slot.
        assert (Hhg : hm <> g) by (intros ->; exact (g_childless j x o K4 K6)).
        split; [exact K1|]. split; [apply e_is_group; split; [exact K2 | exact Hhg]|].
        repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); assumption].
        destruct (hslot_cases hm j) as [[_ E]|(hm' & hi' & o' & K' & E1 & E2 & _ & E & S)]; rewrite E; [exact K6|].
        exfalso. rewrite K6 in S. injection S. intros _ Exg. exact (Hxg Exg).
    - (* [comment removed for export] *) intros Hall.
      assert (Hall0 : forall k, 0 <= k <= g_lastidx st x -> s_slot st x k = SAvail \/ s_slot st x k = SFreed).
      { intros k Hk. destruct (Hall k Hk) as [A|A]; rewrite e_slot in A; [apply d_slot_avail in A | apply d_slot_freed in A]; tauto. }
      destruct (FF Hall0) as (K & S48 & Hh). split; [exact K|]. split; [exact S48|].
      rewrite e_alist. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hh]. rewrite E in Hh.
      unfold l'. apply zremove_In. split; [exact Hh | exact Hxg].
    - (* [comment removed for export] *) intros k Hk. rewrite e_slot. apply t_slot_wf; [exact Hx | exact Hxg | exact Hk | exact (Slots k Hk)].
    - (* [comment removed for export] *) intros Hsc Hst k Hk. rewrite e_slot, d_slot_avail, d_slot_freed. exact (Fit Hsc Hst k Hk).
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hfj Hgrp HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo.
    - apply NoDup_ListNoDup. apply zremove_NoDup. apply NoDup_ListNoDup. exact ND.
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [Hx Hxg]. apply t_wf_group; assumption.
    - intros m1 m2 H1 H2. apply e_is_group in H1. apply e_is_group in H2. rewrite !e_ai, !e_glast, !e_gsc. apply ONE; tauto.
    - intros b len x Hin. rewrite e_regions in Hin. rewrite e_is_group, e_kind, e_gmem, e_gml.
      pose proof (REG b len x (d_regions_sub _ Hin)) as (A & B & C & D).
      assert (x <> g).
      { intros ->. unfold d_regions in Hin. rewrite B in Hin. apply rremove_In in Hin. destruct Hin as [_ NE]. apply NE.
        unfold rg. rewrite C, D. reflexivity. }
      tauto.
    - intros x F. apply e_fresh in F. rewrite e_meta, d_meta_nongroup; [exact (FR0 x F)|].
      intros Hx. exact (wg_notfresh st L x (EACH x Hx) F).
    - intros x U NG NFL NFR. rewrite e_metaU in U. rewrite e_in_flist in NFL. rewrite e_fresh in NFR.
      destruct (Z.eq_dec x g) as [->|Hxg]; [left; reflexivity | right].
      apply (OTH x U); [| exact NFL | exact NFR]. intros Hx. apply NG. apply e_is_group. split; assumption.
    - intros x [<-|Hl].
      + split; [apply e_metaU; exact g_U|]. split; [intros Hx; apply e_is_group in Hx; exact (proj2 Hx eq_refl)|].
        split; [intros Hx; apply e_listed in Hx; exact (proj2 Hx eq_refl)|]. rewrite e_fresh. exact (wg_notfresh st L g g_wfg).
      + destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_listed, e_fresh. repeat split; try assumption; tauto.
    - intros m1 m2 H1 H2 G1 G2 E. apply e_is_group in H1. apply e_is_group in H2. destruct H1 as [H1 _]. destruct H2 as [H2 _].
      rewrite !e_gsc in E. rewrite !e_glast in G1, G2.
      apply (ONEFF m1 m2 H1 H2); [intros k Hk | intros k Hk | exact E].
      * destruct (G1 k Hk) as [A|A]; rewrite e_slot in A; [apply d_slot_avail in A | apply d_slot_freed in A]; tauto.
      * destruct (G2 k Hk) as [A|A]; rewrite e_slot in A; [apply d_slot_avail in A | apply d_slot_freed in A]; tauto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma span_nonempty : forall x, is_group st x -> g_mem st x + 16 <= gspan st x.
  Proof using HWF L RN.
    intros x Hx. pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
    pose proof (glast_rng st x). unfold gspan, g_span_end, g_cnt, UNIT, IB. nia.
  Qed.

  Lemma e_garbage : forall x k a, is_group st x -> garbage st' x k a ->
    garbage st x k a \/ (s_kind st g = GNest x k hoff /\ g_mem st g <= a < gspan st g /\ a < g_slot_end st x k).
  Proof using Hgrp HWF L RN.
    intros x k a Hx G. unfold garbage in G |- *. rewrite e_glast, e_slot, e_gss, e_gse in G.
    destruct G as [Hk G].
    destruct (hslot_cases x k) as [[_ E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E in G.
    - left. split; [exact Hk|]. destruct (s_slot st x k); rewrite ?e_gspan in G; exact G.
    - rewrite S. pose proof (wg_kind st L g g_wfg) as KD. rewrite K in KD.
      destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      assert (Eh : hoff = o') by (unfold hoff; rewrite K; reflexivity).
      destruct G as [G|G]; [left; split; [exact Hk | left; exact G]|].
      destruct (Z.lt_ge_cases a (gspan st g)) as [A|A].
      + right. rewrite Eh. split; [exact K|]. rewrite K9. lia.
      + left. split; [exact Hk|]. right. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma g_bytes : forall a x2, g_mem st g <= a < gspan st g ->
    (a < gspan st g - 1 \/ endb_own st g) ->
    is_group st x2 -> x2 <> g -> (gcell st x2 a -> False) /\ (appb st a -> False) /\ (areab st a -> False).
  Proof using Hfj Hgrp HWF L RN.
    intros a x2 Ha Hend Hx2 Hne.
    destruct (span_cover st L HWF g a Hgrp Hfj ltac:(lia) ltac:(destruct Hend as [H|H]; [left; exact H | destruct (Z.eq_dec a (gspan st g - 1)); [right; split; assumption | left; lia]])) as [GC|(k & GG)].
    - split; [intros C; exact (ge_cells st (WF_geom st L HWF) g x2 a Hgrp Hx2 (fun E => Hne (eq_sym E)) GC C)|].
      split; [intros Ap; exact (ge_app_cell st (WF_geom st L HWF) g a Hgrp GC Ap)|].
      intros Ar. exact (ge_area st (WF_geom st L HWF) g a Hgrp (gcell_in_span st L HWF g a Hgrp GC) Ar).
    - split; [intros C; exact (ge_garb_cell st (WF_geom st L HWF) g k a x2 Hgrp GG Hx2 C)|].
      split; [intros Ap; exact (ge_garb_app st (WF_geom st L HWF) g k a Hgrp GG Ap)|].
      intros Ar. exact (ge_garb_area st (WF_geom st L HWF) g k a Hgrp GG Ar).
  Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof using Hfj Hgrp HWF L RN.
    pose proof (WF_geom st L HWF) as WG0. destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN].
    constructor.
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [Hx Hxg]. rewrite e_gmem, e_gspan, e_regions.
      destruct (INR x Hx) as (r & Hr & B1 & B2). exists r. split; [|split; assumption].
      unfold d_regions. destruct (s_kind st g) eqn:Kg; [|exact Hr]. apply rremove_In. split; [exact Hr|].
      intros ->. unfold rg in B1, B2. cbn [rg_base rg_len] in B1, B2.
      pose proof (span_nonempty x Hx).
      destruct (top_range_free8 st L HWF g x Hgrp Kg g_childless Hx Hxg) as [A|A]; unfold g_map_end in *; lia.
    - intros m1 m2 a H1 H2 Hne G1 G2. apply e_is_group in H1. apply e_is_group in H2. apply e_gcell in G1. apply e_gcell in G2.
      exact (CELLS m1 m2 a (proj1 H1) (proj1 H2) Hne G1 G2).
    - intros x a Hx R Ar. apply e_is_group in Hx. rewrite e_gmem, e_gspan in R. apply e_areab in Ar. exact (AREA x a (proj1 Hx) R Ar).
    - intros x a Hx G Ap. apply e_is_group in Hx. apply e_gcell in G. apply e_appb in Ap. exact (APC x a (proj1 Hx) G Ap).
    - intros a Ap Ar. apply e_appb in Ap. apply e_areab in Ar. exact (APA a Ap Ar).
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply e_is_group in H1. apply e_is_group in H2. rewrite e_glast in Hk1, Hk2. rewrite e_slot, d_slot_user in S1, S2.
      exact (APD m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 (proj1 H1) (proj1 H2) Hk1 Hk2 S1 S2 Hne).
    - intros x k a x2 Hx G H2 C. apply e_is_group in Hx. destruct Hx as [Hx Hxg]. apply e_is_group in H2. destruct H2 as [H2 H2g].
      apply e_gcell in C. destruct (e_garbage x k a Hx G) as [G0|(K & R & Re)]; [exact (GC x k a x2 Hx G0 H2 C)|].
      refine (proj1 (g_bytes a x2 R _ H2 H2g) C).
      destruct (Z.lt_ge_cases a (gspan st g - 1)); [left; assumption | right]. unfold endb_own. rewrite K. lia.
    - intros x k a Hx G Ap. apply e_is_group in Hx. destruct Hx as [Hx Hxg]. apply e_appb in Ap.
      destruct (e_garbage x k a Hx G) as [G0|(K & R & Re)]; [exact (GA x k a Hx G0 Ap)|].
      (* [comment removed for export] *)
      refine (proj1 (proj2 (g_bytes a x R _ Hx Hxg)) Ap).
      destruct (Z.lt_ge_cases a (gspan st g - 1)); [left; assumption | right]. unfold endb_own. rewrite K. lia.
    - intros x k a Hx G Ar. apply e_is_group in Hx. destruct Hx as [Hx Hxg]. apply e_areab in Ar.
      destruct (e_garbage x k a Hx G) as [G0|(K & R & Re)]; [exact (GAR x k a Hx G0 Ar)|].
      refine (proj2 (proj2 (g_bytes a x R _ Hx Hxg)) Ar).
      destruct (Z.lt_ge_cases a (gspan st g - 1)); [left; assumption | right]. unfold endb_own. rewrite K. lia.
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [Hx _]. rewrite e_kind, e_gspan, e_gmem, e_gml.
      pose proof (SPAN x Hx) as SP. destruct (s_kind st x); [exact SP|]. rewrite e_gss, e_gse. exact SP.
  Qed.

  Lemma t_wf_live : wf_live st' L.
  Proof using Hfj Hgrp HWF RN.
    destruct (WF_live st L HWF) as [IN ND FUN LEN]. constructor.
    - intros p n Hin. destruct (IN p n Hin) as (x & k & o & r & A & B & C). exists x, k, o, r.
      rewrite e_glast, e_slot, d_slot_user. split; [|tauto]. apply e_is_group. split; [exact A|]. intros ->. exact (g_nouser k p n o r B C).
    - exact ND.
    - intros m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      apply e_is_group in H1. apply e_is_group in H2. rewrite e_glast in Hk1, Hk2. rewrite e_slot, d_slot_user in S1, S2.
      exact (FUN m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2 (proj1 H1) (proj1 H2) Hk1 Hk2 S1 S2).
    - exact LEN.
  Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof using Hgrp HWF L.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL]. constructor; rewrite ?e_regions, ?e_brk.
    - intros r Hr. exact (RNG r (d_regions_sub r Hr)).
    - intros r1 r2 H1 H2 Hne. exact (DISJ r1 r2 (d_regions_sub r1 H1) (d_regions_sub r2 H2) Hne).
    - exact d_regions_nodup.
    - intros r Hr. exact (LEN r (d_regions_sub r Hr)).
    - intros b len x Hin. rewrite e_gsc. exact (GB b len x (d_regions_sub _ Hin)).
    - intros b len x Hin H63. rewrite e_gsc in H63. rewrite !e_slot.
      destruct (G63 b len x (d_regions_sub _ Hin) H63) as [(p & n & o & r & A & B)|(o & A)].
      + left. exists p, n, o, r. rewrite d_slot_user. tauto.
      + right. destruct (hslot_cases x 0) as [[_ E]|(hm & hi & o' & K & -> & E0 & _ & E & S)]; rewrite E; [exists o; exact A | exists o'; reflexivity].
    - intros b len e Hin. exact (MT b len e (d_regions_sub _ Hin)).
    - eapply Z.le_trans; [|exact MC]. apply inj_le. apply filter_count_le.
    - destruct (s_brk st) as [|b0 b gk|gd].
      + intros b len Hin. exact (BRK b len (d_regions_sub _ Hin)).
      + destruct BRK as (B1 & B2 & B3). split; [intros b' len Hin; exact (B1 b' len (d_regions_sub _ Hin))|].
        split; [eapply Z.le_trans; [|exact B2]; apply inj_le; apply filter_count_le|].
        apply d_regions_keep; [exact B3 | destruct gk; cbn; discriminate].
      + destruct BRK as [B1 B2]. split; [eapply Z.le_trans; [|exact B1]; apply inj_le; apply filter_count_le|].
        destruct gd as [[b0 gk]|]; [|exact I]. apply d_regions_keep; [exact B2 | destruct gk; cbn; discriminate].
    - intros b len Hin. exact (BL b len (d_regions_sub _ Hin)).
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof using HWF L RN. apply (wf_img_sub st L HWF); [intros a Ha; left; exact Ha | intros r Hr; left; exact (d_regions_sub _ Hr)]. Qed.

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

  (* [comment removed for export] *)
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
      + intros x Hx. apply e_is_group in Hx. exact (proj1 Hx).
      + intros x Hx. repeat split; reflexivity.
      + intros x Hx E. apply e_endb. exact E.
      + intros x k Hx Hk. rewrite e_slot. destruct (hslot_cases x k) as [[_ E]|(hm & hi & o' & K & -> & -> & _ & E & S)]; rewrite E.
        * left. reflexivity.
        * right; right; right. exists g, o'. split; [exact S | reflexivity].
      + intros x a Hx G. apply e_is_group in Hx. destruct Hx as [Hx Hxg]. apply e_gcell in G.
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(y & Uy & _ & W)|[_ W]]].
        * ceil; lia.
        * exact (gcell_not_meta st L HWF x y a Hx G Uy W).
        * hsep; unfold ctx_active, CTX, HEAPLO in *; lia.
      + intros x a Hx G. left. apply e_gcell. exact G.
  Qed.

  Lemma t_WF : WF st' L.
  Proof using Hfj Hgrp HWF.
    split; [exact t_wf_ctx|]. split; [exact t_wf_areas|]. split; [exact t_wf_lists|]. split; [exact t_wf_groups|].
    split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.

  Theorem dissolve_close : WF st' L /\ REP st' M'.
  Proof using HMact HMnxt HMprv HMg8 HMg0 HMgrow HMwr Hsp Hfj Hgrp HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.

  (* [comment removed for export] *)
  Lemma dissolve_top : s_kind st g = GTop -> Permutation (s_regions st) (rg :: s_regions st').
  Proof using Hgrp HWF L RN.
    intros K. rewrite e_regions. unfold d_regions. rewrite K. apply rremove_perm; [exact (wr_nodup st (WF_regions st L HWF))|].
    pose proof (wg_kind st L g g_wfg) as KD. rewrite K in KD. destruct KD as (_ & K2 & _). exact K2.
  Qed.
  Lemma dissolve_nest : forall hm hi o, s_kind st g = GNest hm hi o -> s_regions st' = s_regions st.
  Proof using. intros hm hi o K. rewrite e_regions. unfold d_regions. rewrite K. reflexivity. Qed.


  Lemma dissolve_hostslot : forall hm hi o, s_kind st g = GNest hm hi o ->
    is_group st' hm /\ 0 <= hi <= g_lastidx st' hm /\ s_slot st' hm hi = SJunk o /\ g_mem st g = g_slot_start st' hm hi + 16 * o.
  Proof using Hfj Hgrp HWF L RN.
    intros hm hi o K. pose proof (wg_kind st L g g_wfg) as KD. rewrite K in KD.
    destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    split; [apply e_is_group; split; [exact K2 | intros ->; exact (g_childless hi g o K4 K6)]|].
    split; [rewrite e_glast; exact K4|]. split; [|rewrite e_gss; exact K9].
    rewrite e_slot. unfold d_slot, is_hslot, hoff. rewrite K, !Z.eqb_refl. reflexivity.
  Qed.
End Dissolve.
