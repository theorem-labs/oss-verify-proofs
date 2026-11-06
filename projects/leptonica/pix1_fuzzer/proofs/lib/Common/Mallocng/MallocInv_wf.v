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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint list_set {T} (l : list T) (i : nat) (x : T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S i' => h :: list_set t i' x
  end.

Lemma list_set_length : forall {T} (l : list T) i x, length (list_set l i x) = length l.
Proof using Type. pu_keep tt. induction l; intros [|i] x; cbn; auto. Qed.

Lemma list_set_nth_same : forall {T} (l : list T) i x, (i < length l)%nat -> nth_error (list_set l i x) i = Some x.
Proof using Type. pu_keep tt. induction l; intros [|i] x H; cbn in *; try llia; auto. apply IHl. llia. Qed.

Lemma list_set_nth_other : forall {T} (l : list T) i j x, i <> j -> nth_error (list_set l i x) j = nth_error l j.
Proof using Type. pu_keep tt. induction l; intros [|i] [|j] x H; cbn in *; try congruence; auto. Qed.

Lemma list_set_nth_inv : forall {T} (l : list T) i j x y,
  nth_error (list_set l i x) j = Some y -> (j = i /\ y = x /\ (i < length l)%nat) \/ (j <> i /\ nth_error l j = Some y).
Proof using Type. pu_keep tt.
  intros T l i j x y H. destruct (Nat.eq_dec j i) as [-> | Hne].
  - left. assert (Hi : (i < length l)%nat).
    { rewrite <- (list_set_length l i x). apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate. }
    rewrite list_set_nth_same in H by exact Hi. injection H as <-. auto.
  - right. rewrite list_set_nth_other in H by congruence. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_live (A : astate) (L : Z -> option Z) : astate :=
  AST (a_ctx A) (a_areas A) (a_meta A) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) L (a_mblocks A) (a_xmaps A).

Definition slot_set (A : astate) (ma : Z) (i : Z) (st : slot_st) (L : Z -> option Z) : astate :=
  match a_meta A ma with
  | Some mt =>
      match mt_role mt with
      | RGroup aib slots => set_live (ameta_upd A ma (MT (mt_f mt) (RGroup aib (list_set slots (Z.to_nat i) st)))) L
      | _ => A
      end
  | None => A
  end.

(* [comment removed for export] *)
Lemma live_in_span_unique : forall A ma mt aib slots i off n ma' mt' aib' slots' i' st',
  WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i -> nth_error slots (Z.to_nat i) = Some (SLive off n) ->
  a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> 0 <= i' -> nth_error slots' (Z.to_nat i') = Some st' ->
  (forall ch, st' <> SNested ch) ->
  slot_start mt' i' <= slot_start mt i + 16 * off < slot_end mt' i' ->
  ma = ma' /\ i = i'.
Proof using Type. pu_keep tt.
  intros A ma mt aib slots i off n ma' mt' aib' slots' i' st' HW Hma Hr Hi0 Hi Hma' Hr' Hi0' Hi' Hst' Hin'.
  destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32 & _ & Hsc & Hlen & _).
  destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as (Hw32' & _ & Hsc' & Hlen' & _).
  pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS. pose proof (stride_ge16 mt' ltac:(llia) Hsc') as HS'.
  pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hfit & _).
  assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
  assert (Hilt' : (Z.to_nat i' < length slots')%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi'; discriminate).
  destruct (stride_16 mt) as [q Hq]. destruct (stride_16 mt') as [q' Hq'].
  assert (Hin : slot_start mt i <= slot_start mt i + 16 * off < slot_end mt i) by (unfold slot_start, slot_end, slot_start_g, slot_end_g in *; llia).
  set (p := slot_start mt i + 16 * off) in *.
  assert (Hg : gext_lo mt <= slot_start mt i /\ slot_end mt i <= gext_hi mt).
  { unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g.
    assert (0 <= i * mt_stride mt /\ i * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by lnia. llia. }
  assert (Hg' : gext_lo mt' <= slot_start mt' i' /\ slot_end mt' i' <= gext_hi mt').
  { unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g.
    assert (0 <= i' * mt_stride mt' /\ i' * mt_stride mt' + mt_stride mt' <= mt_cnt mt' * mt_stride mt') by lnia. llia. }
  destruct (Z.eq_dec ma ma') as [-> | Hne].
  - split; [reflexivity|]. rewrite Hma in Hma'. injection Hma' as <-.
    destruct (Z.lt_total i i') as [Hlt | [-> | Hgt]]; [| reflexivity |]; exfalso;
      unfold slot_start, slot_end, slot_start_g, slot_end_g in Hin, Hin'.
    + pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i i' HS Hi0 Hi0' Hlt). llia.
    + pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i' i HS Hi0' Hi0 Hgt). llia.
  - exfalso.
    destruct (wf_laminar A HW ma mt aib slots ma' mt' aib' slots' Hma Hr Hma' Hr' Hne)
      as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
    + llia.
    + llia.
    + (* [comment removed for export] *)
      assert (Hji : j = i).
      { destruct (Z.lt_total j i) as [Hlt | [E | Hgt]]; [| exact E |]; exfalso;
          unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
        - pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) j i HS Hj0 Hi0 Hlt). llia.
        - pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i j HS Hi0 Hj0 Hgt). llia. }
      subst j. rewrite Hi in Hj. discriminate.
    + assert (Hji : j = i').
      { destruct (Z.lt_total j i') as [Hlt | [E | Hgt]]; [| exact E |]; exfalso;
          unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
        - pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') j i' HS' Hj0 Hi0' Hlt). llia.
        - pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') i' j HS' Hi0' Hj0 Hgt). llia. }
      subst j. rewrite Hi' in Hj. injection Hj as E. exact (Hst' ch E).
Qed.

(* [comment removed for export] *)
Lemma live_slot_unique : forall A ma mt aib slots i off n ma' mt' aib' slots' i' off' n',
  WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i -> nth_error slots (Z.to_nat i) = Some (SLive off n) ->
  a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> 0 <= i' -> nth_error slots' (Z.to_nat i') = Some (SLive off' n') ->
  slot_start mt i + 16 * off = slot_start mt' i' + 16 * off' ->
  ma = ma' /\ i = i'.
Proof using Type. pu_keep tt.
  intros A ma mt aib slots i off n ma' mt' aib' slots' i' off' n' HW Hma Hr Hi0 Hi Hma' Hr' Hi0' Hi' Hp.
  apply (live_in_span_unique A ma mt aib slots i off n ma' mt' aib' slots' i' (SLive off' n') HW Hma Hr Hi0 Hi Hma' Hr' Hi0' Hi').
  - intros ch E. discriminate.
  - rewrite Hp. destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as (Hw32' & _ & Hsc' & _).
    pose proof (stride_ge16 mt' ltac:(llia) Hsc') as HS'.
    pose proof (wf_live A HW ma' mt' aib' slots' i' off' n' Hma' Hr' Hi' Hi0') as (Ho' & Hn' & Hfit' & _).
    destruct (stride_16 mt') as [q' Hq'].
    unfold slot_start, slot_end, slot_start_g, slot_end_g in *. llia.
Qed.

(* [comment removed for export] *)
Definition plain_inuse (st : slot_st) : Prop :=
  st = STaken \/ exists off n, st = SLive off n.

Section SlotSet.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z) (st0 st1 : slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some st0.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hst0 : plain_inuse st0.
  Hypothesis Hst1 : plain_inuse st1.
  Hypothesis Hlive1 : forall off n, st1 = SLive off n -> 0 <= off /\ 0 <= n /\ 16 * off + n <= mt_stride mt - 4 /\ off < 2^16 /\ off <= 255 /\ mt_stride mt - n < 2^20.
  Variable L : Z -> option Z.
  (* [comment removed for export] *)
  Hypothesis HL : forall q k, L q = Some k <->
    (exists off, st1 = SLive off k /\ q = slot_start mt i + 16 * off) \/
    (a_live A q = Some k /\ forall off n, st0 = SLive off n -> q <> slot_start mt i + 16 * off).

  Let mt' := MT (mt_f mt) (RGroup aib (list_set slots (Z.to_nat i) st1)).
  Let A' := slot_set A ma i st1 L.

  Lemma A'_eq : A' = set_live (ameta_upd A ma mt') L.
  Proof using Hma Hr i st1. pu_keep (Hma, Hr, i, st1). unfold A', slot_set. rewrite Hma, Hr. reflexivity. Qed.

  Lemma A'_meta : forall x, a_meta A' x = if Z.eq_dec x ma then Some mt' else a_meta A x.
  Proof using Hma Hr L i st1. pu_keep (Hma, Hr, L, i, st1). intros x. rewrite A'_eq. unfold set_live, ameta_upd, set_meta, aupd. cbn. reflexivity. Qed.

  Lemma A'_live : a_live A' = L. Proof using Hma Hr mt'. pu_keep (Hma, Hr, mt'). rewrite A'_eq. reflexivity. Qed.

  Lemma A'_meta_other : forall x, x <> ma -> a_meta A' x = a_meta A x.
  Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). intros x Hx. rewrite A'_meta. destruct (Z.eq_dec x ma); [contradiction | reflexivity]. Qed.

  Lemma A'_meta_same : a_meta A' ma = Some mt'.
  Proof using Hma Hr L i st1. pu_keep (Hma, Hr, L, i, st1). rewrite A'_meta. destruct (Z.eq_dec ma ma); [reflexivity | contradiction]. Qed.

  Lemma A'_ctx : a_ctx A' = a_ctx A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.
  Lemma A'_areas : a_areas A' = a_areas A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.
  Lemma A'_freelist : a_freelist A' = a_freelist A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.
  Lemma A'_active : a_active A' = a_active A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.
  Lemma A'_blocks : a_pages A' = a_pages A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.
  Lemma A'_mblocks : a_mblocks A' = a_mblocks A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.
  Lemma A'_xmaps : a_xmaps A' = a_xmaps A. Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt'). rewrite A'_eq. reflexivity. Qed.

  Lemma mt'_f : mt_f mt' = mt_f mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.
  Lemma mt'_mem : mt_mem mt' = mt_mem mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.
  Lemma mt'_w32 : mt_w32 mt' = mt_w32 mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.
  Lemma mt'_stride : mt_stride mt' = mt_stride mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.
  Lemma mt'_cnt : mt_cnt mt' = mt_cnt mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.
  Lemma mt'_maplen : mt_maplen mt' = mt_maplen mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.
  Lemma mt'_sc : mt_sc mt' = mt_sc mt. Proof using aib i slots st1. pu_keep (aib, i, slots, st1). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma A'_group_inv : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    (x = ma /\ mtx = mt' /\ aibx = aib /\ slx = list_set slots (Z.to_nat i) st1) \/
    (x <> ma /\ a_meta A x = Some mtx).
  Proof using Hma Hr L. pu_keep (Hma, Hr, L).
    intros x mtx aibx slx Hx Hrx. rewrite A'_meta in Hx. destruct (Z.eq_dec x ma) as [-> | Hne].
    - left. injection Hx as <-. cbn in Hrx. injection Hrx as <- <-. auto.
    - right. auto.
  Qed.

  Lemma A'_meta_inv : forall x mtx, a_meta A' x = Some mtx ->
    (x = ma /\ mtx = mt') \/ (x <> ma /\ a_meta A x = Some mtx).
  Proof using Hma Hr L i st1. pu_keep (Hma, Hr, L, i, st1).
    intros x mtx Hx. rewrite A'_meta in Hx. destruct (Z.eq_dec x ma) as [-> | Hne].
    - left. injection Hx as <-. auto.
    - right. auto.
  Qed.

  Lemma Hilt : (Z.to_nat i < length slots)%nat.
  Proof using Hi. pu_keep (Hi). apply (proj1 (nth_error_Some _ _)). rewrite Hi. discriminate. Qed.

  (* [comment removed for export] *)
  Lemma slots'_inv : forall j stj, nth_error (list_set slots (Z.to_nat i) st1) j = Some stj ->
    (j = Z.to_nat i /\ stj = st1) \/ (j <> Z.to_nat i /\ nth_error slots j = Some stj).
  Proof using Type. pu_keep tt.
    intros j stj H. destruct (list_set_nth_inv _ _ _ _ _ H) as [(-> & -> & _) | (Hne & Hj)]; auto.
  Qed.

  Lemma slots'_nested : forall j ch, nth_error (list_set slots (Z.to_nat i) st1) j = Some (SNested ch) ->
    j <> Z.to_nat i /\ nth_error slots j = Some (SNested ch).
  Proof using Hst1. pu_keep (Hst1).
    intros j ch H. destruct (slots'_inv j _ H) as [(-> & E) | HH]; [|exact HH].
    exfalso. destruct Hst1 as [E1 | (off & n & E1)]; rewrite E1 in E; discriminate.
  Qed.

  Lemma slots_nested_kept : forall j ch, nth_error slots j = Some (SNested ch) ->
    nth_error (list_set slots (Z.to_nat i) st1) j = Some (SNested ch).
  Proof.
    intros j ch H. destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
    - rewrite Hi in H. injection H as E. exfalso. destruct Hst0 as [E1 | (off & n & E1)]; rewrite E1 in E; discriminate.
    - rewrite list_set_nth_other by congruence. exact H.
  Qed.

  Lemma dll_kept : forall l, dll A l -> dll A' l.
  Proof using HL Hlive1 Hma Hr mt'. pu_keep (HL, Hlive1, Hma, Hr, mt').
    intros l Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & Hn & Hp).
    rewrite A'_meta. destruct (Z.eq_dec x ma) as [-> | Hne].
    - exists mt'. rewrite Hma in Hx. injection Hx as ->. auto.
    - exists mtx. auto.
  Qed.

  Theorem WF_slot_set : WF A'.
  Proof using HL HW Hi Hi0 Hlive1 Hma Hr Hst0 Hst1 mt'. pu_keep (HL, HW, Hi, Hi0, Hlive1, Hma, Hr, Hst0, Hst1, mt').
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0]. pose proof Hilt as Hlt.
    assert (Hgrp0 := wf_grp0 ma mt aib slots Hma Hr).
    constructor; rewrite ?A'_ctx, ?A'_areas, ?A'_freelist, ?A'_active, ?A'_blocks, ?A'_live, ?A'_mblocks, ?A'_xmaps; try assumption.
    - (* [comment removed for export] *) intros x. rewrite <- wf_meta_dom0. rewrite A'_meta.
      destruct (Z.eq_dec x ma) as [-> | Hne]; [rewrite Hma; split; discriminate | tauto].
    - (* [comment removed for export] *) intros Hc. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). rewrite A'_meta.
      destruct (Z.eq_dec (meta_addr pg k) ma) as [E | Hne].
      + exfalso. rewrite E, Hma in Hmk. injection Hmk as ->. rewrite Hr in Hrk. discriminate.
      + exists mtk. auto.
    - (* [comment removed for export] *) intros x mtx Hx Hrx.
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrx; discriminate | eauto].
    - (* [comment removed for export] *) intros x mtx Hx Hrx.
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrx; discriminate | eauto].
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). rewrite A'_meta.
      destruct (Z.eq_dec x ma) as [-> | Hne]; [|tauto].
      rewrite Hma. split; intros (mtx & E & Hrx); injection E as <-; [rewrite Hr in Hrx | cbn in Hrx]; discriminate.
    - (* [comment removed for export] *) apply dll_kept. exact wf_fl_dll0.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_grp0; eauto].
      destruct Hgrp0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
      rewrite mt'_w32, mt'_cnt, mt'_sc, mt'_maplen, mt'_stride, mt'_mem. unfold mt_last, mt_avail, mt_freed in *. rewrite mt'_f.
      rewrite list_set_length.
      repeat (split; [assumption|]).
      split; [|exact G12].
      intros j stj Hj Hj0. destruct (slots'_inv _ _ Hj) as [(Ej & ->) | (Hnej & Hj')].
      + rewrite <- (Z2Nat.id j) by llia. rewrite Ej, Z2Nat.id by llia.
        rewrite (G11 i st0 Hi Hi0).
        destruct Hst0 as [E0 | (o0 & n0 & E0)]; destruct Hst1 as [E1 | (o1 & n1 & E1)]; subst; split; intros; try discriminate; auto.
      + apply G11; auto.
    - (* [comment removed for export] *) intros x mtx aibx slx j off n Hx Hrx Hj Hj0.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_live0; eauto].
      rewrite mt'_stride. destruct (slots'_inv _ _ Hj) as [(Ej & E) | (Hnej & Hj')].
      + apply (Hlive1 off n). symmetry. exact E.
      + eapply (wf_live0 ma mt aib slots j); eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx j ch Hx Hrx Hj Hj0.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + destruct (slots'_nested _ _ Hj) as [Hnej Hj'].
        destruct (wf_nested0 ma mt aib slots j ch Hma Hr Hj' Hj0) as (mc & aibc & slc & Hmc & Hrc & H1 & H2 & H3).
        assert (Hcne : ch <> ma).
        { intros ->. rewrite Hma in Hmc. injection Hmc as <-.
          (* [comment removed for export] *)
          destruct Hgrp0 as (G1 & G2 & G3 & G4 & _). pose proof (stride_ge16 mt ltac:(llia) G3).
          unfold slot_start, slot_start_g in H2. lnia. }
        exists mc, aibc, slc. rewrite A'_meta_other by exact Hcne. unfold slot_start in *. rewrite mt'_mem, mt'_stride. auto 10.
      + destruct (wf_nested0 x mtx aibx slx j ch Hx' Hrx Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & H1 & H2 & H3).
        destruct (Z.eq_dec ch ma) as [-> | Hcne].
        * rewrite Hma in Hmc. injection Hmc as <-. rewrite Hr in Hrc. injection Hrc as <- <-.
          exists mt', aib, (list_set slots (Z.to_nat i) st1). rewrite A'_meta_same. rewrite mt'_maplen, mt'_mem, mt'_cnt, mt'_stride. auto 10.
        * exists mc, aibc, slc. rewrite A'_meta_other by exact Hcne. auto 10.
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hml.
      destruct (A'_group_inv ch mc aibc slc Hch Hrc) as [(-> & -> & -> & ->) | (Hne & Hch')].
      + rewrite mt'_maplen in Hml.
        destruct (wf_nested_parent0 ma mt aib slots Hma Hr Hml) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
        destruct (Z.eq_dec x ma) as [-> | Hxne].
        * rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          exists ma, mt', aib, (list_set slots (Z.to_nat i) st1), j. rewrite A'_meta_same.
          repeat split; auto. apply slots_nested_kept. exact Hj.
        * exists x, mtx, aibx, slx, j. rewrite A'_meta_other by exact Hxne. auto 10.
      + destruct (wf_nested_parent0 ch mc aibc slc Hch' Hrc Hml) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
        destruct (Z.eq_dec x ma) as [-> | Hxne].
        * rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          exists ma, mt', aib, (list_set slots (Z.to_nat i) st1), j. rewrite A'_meta_same.
          repeat split; auto. apply slots_nested_kept. exact Hj.
        * exists x, mtx, aibx, slx, j. rewrite A'_meta_other by exact Hxne. auto 10.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      assert (Hx0 : exists mt0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx (if Z.eq_dec x ma then slots else slx) /\
                      mt_mem mt0 = mt_mem mtx /\ mt_w32 mt0 = mt_w32 mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt. destruct (Z.eq_dec ma ma); [|contradiction]. auto.
        - exists mtx. destruct (Z.eq_dec x ma); [contradiction|]. auto. }
      destruct Hx0 as (mt0 & Hx0 & Hr0 & Hm0 & Hw0).
      destruct (wf_grp_root0 x mt0 aibx _ Hx0 Hr0) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & Hself).
      destruct (gext_ext mt0 mtx ltac:(symmetry; exact Hm0) ltac:(symmetry; exact Hw0)) as [Elo Ehi].
      destruct (Z.eq_dec mr ma) as [-> | Hrne].
      + rewrite Hma in Hmr. injection Hmr as <-. rewrite Hr in Hrr. injection Hrr as <- <-.
        exists ma, mt', aib, (list_set slots (Z.to_nat i) st1). rewrite A'_meta_same.
        rewrite mt'_maplen, mt'_mem. unfold grp_map_len in *. rewrite mt'_maplen. rewrite Elo, Ehi.
        repeat split; auto. intros Hmx. apply Hself. unfold mt_maplen in *. rewrite Hw0. exact Hmx.
      + exists mr, mtr, aibr, slr. rewrite A'_meta_other by exact Hrne. rewrite Elo, Ehi.
        repeat split; auto. intros Hmx. apply Hself. unfold mt_maplen in *. rewrite Hw0. exact Hmx.
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hy Hry Hxy.
      (* [comment removed for export] *)
      assert (KX : exists mt0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\
               mt_mem mt0 = mt_mem mtx /\ mt_w32 mt0 = mt_w32 mtx /\
               (forall j ch, nth_error sl0 j = Some (SNested ch) -> nth_error slx j = Some (SNested ch))).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt, slots. repeat split; auto. apply slots_nested_kept.
        - exists mtx, slx. repeat split; auto. }
      assert (KY : exists mt0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aiby sl0 /\
               mt_mem mt0 = mt_mem mty /\ mt_w32 mt0 = mt_w32 mty /\
               (forall j ch, nth_error sl0 j = Some (SNested ch) -> nth_error sly j = Some (SNested ch))).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')].
        - exists mt, slots. repeat split; auto. apply slots_nested_kept.
        - exists mty, sly. repeat split; auto. }
      destruct KX as (mx0 & slx0 & Hx0 & Hrx0 & Emx & Ewx & Nx).
      destruct KY as (my0 & sly0 & Hy0 & Hry0 & Emy & Ewy & Ny).
      destruct (gext_ext mx0 mtx ltac:(symmetry; exact Emx) ltac:(symmetry; exact Ewx)) as [Exlo Exhi].
      destruct (gext_ext my0 mty ltac:(symmetry; exact Emy) ltac:(symmetry; exact Ewy)) as [Eylo Eyhi].
      assert (Esx : forall j, slot_start mtx j = slot_start mx0 j /\ slot_end mtx j = slot_end mx0 j).
      { intros j. unfold slot_start, slot_end. rewrite (stride_ext mx0 mtx) by (symmetry; assumption). rewrite Emx. auto. }
      assert (Esy : forall j, slot_start mty j = slot_start my0 j /\ slot_end mty j = slot_end my0 j).
      { intros j. unfold slot_start, slot_end. rewrite (stride_ext my0 mty) by (symmetry; assumption). rewrite Emy. auto. }
      rewrite Exlo, Exhi, Eylo, Eyhi.
      destruct (wf_laminar0 x mx0 aibx slx0 y my0 aiby sly0 Hx0 Hrx0 Hy0 Hry0 Hxy)
        as [Hd | [Hd | [(j & ch & Hj0 & Hj & H1 & H2) | (j & ch & Hj0 & Hj & H1 & H2)]]].
      + left. exact Hd.
      + right; left. exact Hd.
      + right; right; left. exists j, ch. destruct (Esx j) as [-> ->]. auto.
      + right; right; right. exists j, ch. destruct (Esy j) as [-> ->]. auto.
    - (* [comment removed for export] *) intros sc Hsc. apply dll_kept. apply wf_act_dll0. exact Hsc.
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mtx & aibx & slx & Hx & Hrx & Hscx).
      rewrite A'_meta. destruct (Z.eq_dec x ma) as [-> | Hne].
      + rewrite Hma in Hx. injection Hx as ->. rewrite Hr in Hrx. injection Hrx as <- <-.
        exists mt', aib, (list_set slots (Z.to_nat i) st1). auto.
      + exists mtx, aibx, slx. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hnin.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + unfold mt_prev, mt_next. rewrite mt'_f. eapply (wf_unlinked0 ma mt aib slots); eauto.
      + eapply wf_unlinked0; eauto.
    - (* [comment removed for export] *) intros sc x mtx Hin Hnh Hx.
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')].
      + unfold mt_avail, mt_freed. rewrite mt'_f. eapply (wf_act_nonhead0 sc ma mt); eauto.
      + eapply wf_act_nonhead0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + unfold mt_prev, mt_next. rewrite mt'_f. eapply (wf_act630 ma mt aib slots); eauto.
      + eapply wf_act630; eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + rewrite mt'_mem. unfold grp_map_len. rewrite mt'_maplen. eapply (wf_disj_area_grp0 pg ma mt aib slots); eauto.
      + eapply wf_disj_area_grp0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hmlx Hy Hry Hmly Hxy.
      assert (KX : exists mt0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\ mt_mem mt0 = mt_mem mtx /\ mt_w32 mt0 = mt_w32 mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [exists mt, slots | exists mtx, slx]; auto. }
      assert (KY : exists mt0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aiby sl0 /\ mt_mem mt0 = mt_mem mty /\ mt_w32 mt0 = mt_w32 mty).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')]; [exists mt, slots | exists mty, sly]; auto. }
      destruct KX as (mx0 & slx0 & Hx0 & Hrx0 & Emx & Ewx). destruct KY as (my0 & sly0 & Hy0 & Hry0 & Emy & Ewy).
      unfold grp_map_len, mt_maplen in *. rewrite <- Emx, <- Ewx, <- Emy, <- Ewy in *.
      eapply (wf_disj_grp_grp0 x mx0 aibx slx0 y my0 aiby sly0); eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hy Hry Hmm.
      assert (KX : exists mt0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\ mt_mem mt0 = mt_mem mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [exists mt, slots | exists mtx, slx]; auto. }
      assert (KY : exists mt0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aiby sl0 /\ mt_mem mt0 = mt_mem mty).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')]; [exists mt, slots | exists mty, sly]; auto. }
      destruct KX as (mx0 & slx0 & Hx0 & Hrx0 & Emx). destruct KY as (my0 & sly0 & Hy0 & Hry0 & Emy).
      eapply (wf_grp_mem_inj0 x mx0 aibx slx0 y my0 aiby sly0); eauto. congruence.
    - (* [comment removed for export] *) intros q k. rewrite HL. split.
      + intros [(off & E1 & Eq) | (Hold & Hnot)].
        * exists ma, mt', aib, (list_set slots (Z.to_nat i) st1), i, off. rewrite A'_meta_same.
          repeat split; auto. rewrite list_set_nth_same by exact Hlt. rewrite E1. reflexivity.
        * apply (proj1 (wf_live_map0 q k)) in Hold.
          destruct Hold as (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
          destruct (Z.eq_dec x ma) as [-> | Hne].
          -- rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
             assert (Hji : Z.to_nat j <> Z.to_nat i).
             { intros E. rewrite E, Hi in Hj. injection Hj as E0. apply (Hnot off k); [exact E0|].
               replace i with j by llia. exact Eq. }
             exists ma, mt', aib, (list_set slots (Z.to_nat i) st1), j, off. rewrite A'_meta_same.
             repeat split; auto. rewrite list_set_nth_other by congruence. exact Hj.
          -- exists x, mtx, aibx, slx, j, off. rewrite A'_meta_other by exact Hne. repeat split; auto.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
        destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        * destruct (slots'_inv _ _ Hj) as [(Ej & E1) | (Hnej & Hj')].
          -- left. exists off. split; [symmetry; exact E1|]. replace i with j by llia. change (slot_start mt j) with (slot_start mt' j). exact Eq.
          -- right. split.
             ++ apply (proj2 (wf_live_map0 q k)). exists ma, mt, aib, slots, j, off. repeat split; auto.
             ++ intros off0 n0 E0 Eq0. subst st0. change (slot_start mt' j) with (slot_start mt j) in Eq.
                destruct (live_slot_unique A ma mt aib slots j off k ma mt aib slots i off0 n0 W Hma Hr Hj0 Hj' Hma Hr Hi0 Hi ltac:(llia)) as [_ Eji].
                apply Hnej. rewrite Eji. reflexivity.
        * right. split.
          -- apply (proj2 (wf_live_map0 q k)). exists x, mtx, aibx, slx, j, off. repeat split; auto.
          -- intros off0 n0 E0 Eq0. subst st0.
             destruct (live_slot_unique A x mtx aibx slx j off k ma mt aib slots i off0 n0 W Hx' Hrx Hj0 Hj Hma Hr Hi0 Hi ltac:(llia)) as [Exm _].
             exact (Hne Exm).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_span0; eauto].
      change (mt_last mt') with (mt_last mt). rewrite mt'_cnt, mt'_stride. eapply wf_span0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_single0; eauto].
      change (mt_last mt') with (mt_last mt). rewrite mt'_maplen, mt'_sc, mt'_stride. eapply wf_single0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_inactive0; eauto].
      change (mt_last mt') with (mt_last mt). change (mt_freed mt') with (mt_freed mt). eapply wf_inactive0; eauto.
    - (* [comment removed for export] *) intros sc x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry Hpx Hpy.
      assert (KX : exists mt0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\ mt_last mt0 = mt_last mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [exists mt, slots | exists mtx, slx]; auto. }
      assert (KY : exists mt0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aiby sl0 /\ mt_last mt0 = mt_last mty).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')]; [exists mt, slots | exists mty, sly]; auto. }
      destruct KX as (mx0 & slx0 & Hx0 & Hrx0 & Elx). destruct KY as (my0 & sly0 & Hy0 & Hry0 & Ely).
      eapply (wf_partial0 sc x mx0 aibx slx0 y my0 aiby sly0); eauto; llia.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_nested_small0; eauto].
      change (mt_last mt') with (mt_last mt). rewrite mt'_maplen, mt'_cnt, mt'_stride. eapply wf_nested_small0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_reusable0; eauto].
      rewrite mt'_sc, mt'_stride. change (mt_avail mt') with (mt_avail mt). change (mt_freed mt') with (mt_freed mt). eapply wf_reusable0; eauto.
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      assert (KP : exists pm0 psl0, a_meta A pa = Some pm0 /\ mt_role pm0 = RGroup paib psl0 /\
                 mt_mem pm0 = mt_mem pm /\ mt_w32 pm0 = mt_w32 pm /\ nth_error psl0 (Z.to_nat j) = Some (SNested ch)).
      { destruct (A'_group_inv pa pm paib psl Hpa Hpr) as [(-> & -> & -> & ->) | (Hne & Hpa')].
        - exists mt, slots. repeat split; auto. apply slots'_nested. exact Hj.
        - exists pm, psl. repeat split; auto. }
      assert (KX : exists mx0 slx0, a_meta A x = Some mx0 /\ mt_role mx0 = RGroup aibx slx0 /\ mt_mem mx0 = mt_mem mtx /\ mt_w32 mx0 = mt_w32 mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt, slots. repeat split; auto.
        - exists mtx, slx. repeat split; auto. }
      destruct KP as (pm0 & psl0 & Hpa0 & Hpr0 & Epm & Epw & Hjj).
      destruct KX as (mx0 & slx0 & Hx0 & Hrx0 & Emx & Ewx).
      assert (Esp : slot_start pm j = slot_start pm0 j /\ slot_end pm j = slot_end pm0 j).
      { unfold slot_start, slot_end. rewrite (stride_ext pm0 pm) by (symmetry; assumption). rewrite Epm. auto. }
      destruct (gext_ext mx0 mtx ltac:(symmetry; exact Emx) ltac:(symmetry; exact Ewx)) as [Exlo Exhi].
      destruct Esp as [Es1 Es2]. rewrite Exlo, Exhi. rewrite Exlo, Es1 in Hlo. rewrite Exhi, Es2 in Hhi.
      destruct (wf_cover0 pa pm0 paib psl0 j ch x mx0 aibx slx0 Hpa0 Hpr0 Hj0 Hjj Hx0 Hrx0 Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & H1 & H2).
      rewrite A'_meta. destruct (Z.eq_dec ch ma) as [-> | Hnc].
      + rewrite Hma in Hch. injection Hch as E. subst mtc. rewrite Hr in Hrc. injection Hrc as <- <-.
        exists mt', aib, (list_set slots (Z.to_nat i) st1). destruct (gext_ext mt mt' mt'_mem mt'_w32) as [-> ->]. repeat split; auto.
      + exists mtc, aibc, slc. rewrite Hch. repeat split; auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_stride200; eauto].
      rewrite mt'_stride. rewrite mt'_sc in Hsc. eapply wf_stride200; eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_disj_page_grp0; eauto].
      rewrite mt'_mem. unfold grp_map_len. rewrite mt'_maplen. rewrite mt'_maplen in Hml.
      eapply (wf_disj_page_grp0 pg ma mt aib slots); eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_partial_sc0; eauto].
      change (mt_last mt') with (mt_last mt). rewrite mt'_sc. eapply wf_partial_sc0; eauto.
  Qed.


  (* [comment removed for export] *)
  Lemma has_slot_set : forall f, has A' f ->
    has A f \/ In f (slot_fields mt i st1).
  Proof using Hi0 Hma Hr L mt'. pu_keep (Hi0, Hma, Hr, L, mt').
    intros f Hf. destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - left. left. unfold has_ctx in *. rewrite A'_ctx in Hc. exact Hc.
    - left. right; left. unfold has_area in *. rewrite A'_areas, A'_ctx in Har. exact Har.
    - left. right; right; left. destruct Hm as (x & mtx & fl & Hx & ->).
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')].
      + exists ma, mt, fl. rewrite mt'_f. auto.
      + exists x, mtx, fl. auto.
    - destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & Hin).
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + destruct Hin as [Hin | (j & stj & Hj & Hin)].
        * left. right; right; right. exists ma, mt, aib, slots. unfold grp_hdr_fields in *. rewrite mt'_mem in Hin. auto.
        * rewrite (slot_fields_ext mt mt' (Z.of_nat j) stj mt'_mem mt'_w32) in Hin.
          destruct (slots'_inv j stj Hj) as [(-> & ->) | (Hnej & Hj')].
          -- right. rewrite Z2Nat.id in Hin by exact Hi0. exact Hin.
          -- left. right; right; right. exists ma, mt, aib, slots. split; [exact Hma | split; [exact Hr|]].
             right. exists j, stj. auto.
      + left. right; right; right. exists x, mtx, aibx, slx. auto.
  Qed.

  Lemma dom_slot_set : forall x, dom A' x -> dom A x.
  Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt').
    intros x [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | Hp]].
    - left. rewrite A'_areas in Ha. exact Ha.
    - right; left. destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')].
      + exists ma, mt, aib, slots. rewrite mt'_maplen, mt'_mem in *. unfold grp_map_len in *. rewrite mt'_maplen in Hx. auto.
      + exists y, mty, aiby, sly. auto.
    - right; right. rewrite A'_blocks in Hp. exact Hp.
  Qed.

  Lemma Rep_slot_set : forall m, Rep A m ->
    (forall f x b, In f (slot_fields mt i st1) -> fbyte f x b -> mbyte m x = Some b) ->
    Rep A' m.
  Proof using Hi0 Hma Hr L mt'. pu_keep (Hi0, Hma, Hr, L, mt').
    intros m HR Hnew. apply (rep_restate A A' m HR).
    - intros x b (f & Hf & Hfb). destruct (has_slot_set f Hf) as [Hold | Hin].
      + left. exists f. auto.
      + right. exact (Hnew f x b Hin Hfb).
    - intros x Hx. left. exact (dom_slot_set x Hx).
  Qed.
End SlotSet.

End WithLayout.
