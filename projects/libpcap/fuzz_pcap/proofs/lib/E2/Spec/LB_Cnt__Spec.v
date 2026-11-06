(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module LB_Cnt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma zrange_nodup lo n : List.NoDup (zrange lo n).
Proof.
  unfold zrange. apply Finite.Injective_map_NoDup; [| apply seq_NoDup]. intros a b E. lia.
Qed.

#[using="Type"] Lemma nodup_map_inj' {A B} (f : A -> B) (l : list A) x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND Hx Hy E; [destruct Hx|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [->|Hx]; destruct Hy as [->|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

#[using="Type"] Lemma zlen_zrange lo n : 0 <= n -> zlen (zrange lo n) = n.
Proof. intros Hn. unfold zlen, zrange. rewrite length_map, length_seq. lia. Qed.

#[using="Type"] Lemma zcount_flat_map {A B} (g : A -> list B) (p : B -> bool) l : zcount p (flat_map g l) = zsum (map (fun x => zcount p (g x)) l).
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [flat_map map]. rewrite zcount_app, zsum_cons, IH. reflexivity. Qed.

#[using="Type"] Lemma zcount_mapf {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

#[using="Type"] Lemma zcount_true {A} (l : list A) : zcount (fun _ => true) l = zlen l.
Proof. induction l as [|a l IH]; [reflexivity|]. rewrite zcount_cons, zlen_cons, IH. reflexivity. Qed.

#[using="Type"] Lemma zcount_const {A} (b : bool) (l : list A) : zcount (fun _ => b) l = if b then zlen l else 0.
Proof. destruct b; [apply zcount_true| apply zcount_false; auto]. Qed.

Section SLOTS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Let IM : inv_M X st LS := proj1 (proj2 (proj2 INV)).
Let IL : inv_L st LS := proj1 (proj2 (proj2 (proj2 INV))).
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Definition slots_of : list (aptr * Z) :=
  flat_map (fun mb => map (fun i => (fst mb, i)) (zrange 0 (cnt_of (MR st (fst mb))))) (gmetas st).

#[using="CE X L BL LS INV IG"] Lemma in_slots_of m i : In (m, i) slots_of <-> (exists b, hosts st b m) /\ 0 <= i <= m_last_idx (MR st m).
Proof.
  unfold slots_of. rewrite in_flat_map. split.
  - intros ([m' b] & Hin & Hmi). apply in_map_iff in Hmi as (i' & E & Hi). inversion E. subst. cbn in Hi.
    apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
    apply in_zrange in Hi; [| unfold cnt_of; lia]. split; [exists b, ai; exact Hb| unfold cnt_of in Hi; lia].
  - intros ([b [ai Hb]] & Hi). exists (m, b). split; [apply gmetas_in; exists ai; exact Hb|]. cbn.
    apply in_map_iff. exists i. split; [reflexivity|]. apply in_zrange; unfold cnt_of; [pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)); lia| lia].
Qed.

#[using="CE X L BL LS INV"] Lemma slots_of_nodup : List.NoDup slots_of.
Proof.
  unfold slots_of. pose proof (gmetas_nodup st) as ND.
  assert (INJ : forall m b1 b2, In (m, b1) (gmetas st) -> In (m, b2) (gmetas st) -> b1 = b2) by (intros; eapply (gmetas_meta_inj X st L BL LS INV); eauto).
  revert ND INJ. generalize (gmetas st). intros l ND INJ.
  induction l as [|[m b] l IH]; cbn; [constructor|].
  inversion ND as [|? ? NI ND']; subst. apply List.NoDup_app.
  - apply Finite.Injective_map_NoDup; [intros x y E; inversion E; reflexivity| apply zrange_nodup].
  - apply IH; [assumption| intros; eapply INJ; right; eassumption].
  - intros [m' i] Q1 Q2. apply in_map_iff in Q1 as (i' & E & _). inversion E. subst.
    apply in_flat_map in Q2 as ([m2 b2] & Hin2 & Hmi). apply in_map_iff in Hmi as (i2 & E2 & _). inversion E2. subst.
    pose proof (INJ m' b b2 (or_introl eq_refl) (or_intror Hin2)) as <-. exact (NI Hin2).
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV IG"] Lemma gcnt_slots c : gcnt st c = zcount (fun mi => m_sizeclass (MR st (fst mi)) =? c) slots_of.
Proof.
  rewrite gcnt_gmetas. unfold slots_of. rewrite zcount_flat_map. f_equal. apply map_ext_in. intros [m b] Hin. cbn.
  rewrite zcount_mapf. cbn. rewrite zcount_const. destruct (m_sizeclass (MR st m) =? c); [| reflexivity].
  apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
  rewrite zlen_zrange; unfold cnt_of; lia.
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV IG"] Lemma nsc_le_gcnt c : nsc st c <= gcnt st c.
Proof.
  unfold nsc. rewrite gcnt_gmetas. apply zsum_map_le. intros [m b] Hin. cbn. unfold cls.
  apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
  destruct (m_sizeclass (MR st m) =? c); cbn; [destruct (stdg st m); cbn; unfold cnt_of; lia| lia].
Qed.
#[using="CE X L BL LS INV IG"] Lemma nsc_nonneg c : 0 <= nsc st c.
Proof.
  unfold nsc. apply zsum_map_nonneg. intros [m b] Hin. cbn. apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
  destruct (_ && _); unfold cnt_of; lia.
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV IG"] Lemma nstd_le_gcnt c : 0 <= c < 48 -> nstd st c * cmax c <= gcnt st c.
Proof.
  intros Hc. unfold nstd. rewrite zcount_eq_zsum, gcnt_gmetas.
  transitivity (zsum (map (fun mb => if (cls st (fst mb) =? c) && stdg st (fst mb) then cmax c else 0) (gmetas st))).
  - induction (gmetas st) as [|mb l IH]; [cbn; lia|]. cbn [map]. rewrite !zsum_cons. destruct (_ && _); lia.
  - apply zsum_map_le. intros [m b] Hin. cbn. unfold cls, stdg, cls.
    apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
    destruct (Z.eqb_spec (m_sizeclass (MR st m)) c) as [E|NE]; cbn; [| lia]. subst c.
    destruct (Z.eqb_spec (cnt_of (MR st m)) (cmax (m_sizeclass (MR st m)))) as [E2|NE2]; cbn; [| unfold cnt_of in *; lia].
    destruct (get_stride (MR st m) =? S_ (m_sizeclass (MR st m))); unfold cnt_of in *; lia.
Qed.
#[using="Type"] Lemma nstd_nonneg c : 0 <= nstd st c.
Proof. unfold nstd. apply zcount_nonneg. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dec_mi : forall x y : aptr * Z, {x = y} + {x <> y}.
Proof. intros x y. apply (decide (x = y)). Qed.

Definition slot_of_blk (k : blk) : aptr * Z := match s_slots st !! bslot k with Some mi => mi | None => ((0%N, 0), 0) end.

#[using="CE X L LS INV IG IS"] Lemma LS_le_gcnt c : LB_Inv.LS st BL c <= gcnt st c.
Proof.
  rewrite gcnt_slots. unfold LB_Inv.LS.
  apply (zcount_inj_le dec_mi _ _ slot_of_blk).
  - apply (List.NoDup_map_inv bslot). apply NoDup_ListNoDup. exact (is_nodup _ _ _ IS).
  - intros k Hk Hp. unfold slotcls in Hp. unfold slot_of_blk. destruct (s_slots st !! bslot k) as [[m i]|] eqn:Es; rewrite Es in Hp; [| discriminate].
    destruct (is_valid _ _ _ IS _ _ _ Es) as (LG & Hi & E). split; [apply in_slots_of; auto| exact Hp].
  - intros x y Hx Hy Px Py E. unfold slot_of_blk in E. unfold slotcls in Px, Py.
    destruct (s_slots st !! bslot x) as [[mx ix]|] eqn:Ex; rewrite Ex in Px; [| discriminate]. destruct (s_slots st !! bslot y) as [[my iy]|] eqn:Ey; rewrite Ey in Py; [| discriminate].
    inversion E. subst.
    destruct (is_valid _ _ _ IS _ _ _ Ex) as (_ & _ & Ex2). destruct (is_valid _ _ _ IS _ _ _ Ey) as (_ & _ & Ey2).
    assert (EB : bslot x = bslot y) by (rewrite Ex2, Ey2; reflexivity).
    pose proof (is_nodup _ _ _ IS) as ND. apply NoDup_ListNoDup in ND. exact (nodup_map_inj' bslot BL x y ND Hx Hy EB).
Qed.
End SLOTS.

Section INUSE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Let IM : inv_M X st LS := proj1 (proj2 (proj2 INV)).
Let IL : inv_L st LS := proj1 (proj2 (proj2 (proj2 INV))).
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Definition addr (mi : aptr * Z) : aptr := slot_start' (MR st (fst mi)) (snd mi).

#[using="CE X L BL LS INV IS"] Lemma addr_slot m i : In (m, i) (slots_of st) -> s_slots st !! addr (m, i) = Some (m, i).
Proof. intros H. apply (in_slots_of X st L BL LS INV) in H as [[b Hb] Hi]. exact (is_total _ _ _ IS b m i Hb Hi). Qed.

#[using="CE X L BL LS INV IS"] Lemma addr_inj mi1 mi2 : In mi1 (slots_of st) -> In mi2 (slots_of st) -> addr mi1 = addr mi2 -> mi1 = mi2.
Proof.
  destruct mi1 as [m1 i1], mi2 as [m2 i2]. intros H1 H2 E.
  pose proof (addr_slot _ _ H1) as S1. pose proof (addr_slot _ _ H2) as S2. rewrite E in S1. rewrite S1 in S2. congruence.
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV IG"] Lemma stride_nonneg m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> 0 <= get_stride (MR st m).
Proof.
  intros Hb. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_maplen _ _ _ _ _ _ GO) as ML0.
  unfold get_stride.
  destruct (Z.eqb_spec (m_last_idx (MR st m)) 0) as [LZ|LNZ]; destruct (Z.eqb_spec (m_maplen (MR st m)) 0) as [MZ|MNZ]; cbn [andb negb].
  all: try (unfold UNIT; lia).
  all: destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(SC & LI0 & ML & _)]; [pose proof (size_class_pos _ SC); unfold UNIT; lia| first [congruence| lia]].
Qed.

#[using="CE X L BL LS INV IM IG"] Lemma addr_pos m i : In (m, i) (slots_of st) -> 0 < snd (addr (m, i)).
Proof.
  intros H. apply (in_slots_of X st L BL LS INV) in H as [[b [ai Hb]] Hi]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  unfold addr, slot_start', sstart. cbn. pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
  unfold gbase. rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ ai Hb)). cbn.
  pose proof (stride_nonneg m b ai Hb). assert (0 <= get_stride (MR st m) * i) by (apply Z.mul_nonneg_nonneg; lia). unfold UNIT. lia.
Qed.

#[using="Type"] Lemma zcount_cover3 {A} (p q1 q2 q3 : A -> bool) l :
  (forall x, In x l -> p x = true -> q1 x = true \/ q2 x = true \/ q3 x = true) ->
  zcount p l <= zcount q1 l + zcount q2 l + zcount q3 l.
Proof.
  induction l as [|x l IH]; intros H; [rewrite !zcount_nil; lia|]. rewrite !zcount_cons.
  specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)).
  destruct (p x) eqn:Px; [| destruct (q1 x), (q2 x), (q3 x); lia].
  destruct (H x (or_introl eq_refl) Px) as [-> |[-> | ->]]; destruct (q1 x), (q2 x), (q3 x); lia.
Qed.

Definition isblk (mi : aptr * Z) : bool := existsb (fun k => aptr_eqb (bslot k) (addr mi)) BL.
Definition isgrp (mi : aptr * Z) : bool := match s_groups st !! addr mi with Some _ => true | None => false end.
Definition ispend (mi : aptr * Z) : bool := match x_pend X with Some s => aptr_eqb s (addr mi) | None => false end.

Definition blk_of (mi : aptr * Z) : blk := match find (fun k => aptr_eqb (bslot k) (addr mi)) BL with Some k => k | None => ((0%N, 0), 0, 0) end.
Definition grp_of (mi : aptr * Z) : aptr * aptr :=
  (match s_groups st !! addr mi with Some h => default (0%N, 0) (g_meta h) | None => (0%N, 0) end, addr mi).

#[using="Type"] Lemma dec_blk : forall x y : blk, {x = y} + {x <> y}. Proof. intros x y. apply (decide (x = y)). Qed.
#[using="Type"] Lemma dec_mb : forall x y : aptr * aptr, {x = y} + {x <> y}. Proof. intros x y. apply (decide (x = y)). Qed.
#[using="Type"] Lemma dec_ap : forall x y : aptr, {x = y} + {x <> y}. Proof. intros x y. apply (decide (x = y)). Qed.

#[using="Type"] Lemma find_some {A} (p : A -> bool) l x : find p l = Some x -> In x l /\ p x = true.
Proof. induction l as [|a l IH]; cbn; [discriminate|]. destruct (p a) eqn:E; [intros H; inversion H; subst; auto| intros H; destruct (IH H); auto]. Qed.
#[using="Type"] Lemma existsb_find {A} (p : A -> bool) l : existsb p l = true -> exists x, find p l = Some x.
Proof. induction l as [|a l IH]; cbn; [discriminate|]. destruct (p a); [intros _; eexists; reflexivity| exact IH]. Qed.

(* [comment removed for export] *)
#[using="CE L LS INV IM IL IG IS"] Theorem all_in_use c : 0 <= c < 48 -> x_fresh X = None -> active st c = None ->
  gcnt st c <= LB_Inv.LS st BL c + hosted st c + match x_pend X with Some _ => 1 | None => 0 end.
Proof.
  intros Hc HF HA.
  assert (EMP : LS (LActive c) = []).
  { pose proof (il_head _ _ IL (LActive c)) as HH. change (get_head st (LActive c)) with (active st c) in HH. rewrite HA in HH.
    destruct (LS (LActive c)); [reflexivity| cbn in HH; discriminate]. }
  rewrite (gcnt_slots X st L BL LS INV).
  set (Pc := fun mi : aptr * Z => m_sizeclass (MR st (fst mi)) =? c).
  (* [comment removed for export] *)
  assert (COV : forall mi, In mi (slots_of st) -> Pc mi = true -> isblk mi = true \/ isgrp mi = true \/ ispend mi = true).
  { intros [m i] Hin Hp. unfold Pc in Hp. cbn in Hp. apply Z.eqb_eq in Hp.
    apply (in_slots_of X st L BL LS INV) in Hin as [[b [ai Hb]] Hi]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
    assert (NL : ~ in_list LS m).
    { intros [h Hh]. destruct h as [sc'|].
      - destruct (il_active _ _ IL sc' m Hh) as (_ & _ & E). rewrite Hp in E. subst sc'. rewrite EMP in Hh. destruct Hh.
      - pose proof (il_free _ _ IL m Hh) as Z0. pose proof (hosts_mem _ _ _ IM _ _ (ex_intro _ ai Hb)) as MM. rewrite Z0 in MM. cbn in MM. discriminate. }
    destruct (g_unlisted _ _ _ _ _ _ GO ltac:(rewrite HF; discriminate) ltac:(lia) NL) as [A0 F0].
    pose proof (is_part _ _ _ IS b m ai i Hb Hi) as P5. cbn zeta in P5. destruct P5 as [CASES _].
    unfold tbit in CASES. rewrite A0, F0, !Z.bits_0 in CASES.
    destruct CASES as [D|[D|[D|[D|D]]]]; try discriminate.
    - left. unfold isblk. apply existsb_exists. apply in_map_iff in D as (k & Ek & Hk). exists k. split; [exact Hk|]. apply aptr_eqb_eq. exact Ek.
    - right. left. unfold isgrp, addr. cbn. destruct (s_groups st !! slot_start' (MR st m) i); [reflexivity| exfalso; exact (D eq_refl)].
    - right. right. unfold ispend, addr. cbn. rewrite D. apply aptr_eqb_eq. reflexivity. }
  etransitivity; [apply (zcount_cover3 Pc (fun mi => Pc mi && isblk mi) (fun mi => Pc mi && isgrp mi) (fun mi => Pc mi && ispend mi))|].
  { intros mi Hin Hp. rewrite Hp. cbn. exact (COV mi Hin Hp). }
  assert (B1 : zcount (fun mi => Pc mi && isblk mi) (slots_of st) <= LB_Inv.LS st BL c).
  { unfold LB_Inv.LS. apply (zcount_inj_le dec_blk _ _ blk_of); [apply (slots_of_nodup X st L BL LS INV)| |].
    - intros mi Hin Hq. apply andb_prop in Hq as [Hp Hb]. unfold blk_of. destruct (existsb_find _ _ Hb) as [k Hk]. rewrite Hk.
      apply find_some in Hk as [Hk Ek]. apply aptr_eqb_eq in Ek. split; [exact Hk|].
      unfold slotcls. rewrite Ek. destruct mi as [m i]. rewrite (addr_slot m i Hin). unfold cls. exact Hp.
    - intros x y Hx Hy Qx Qy E. apply andb_prop in Qx as [_ Bx]. apply andb_prop in Qy as [_ By]. unfold blk_of in E.
      destruct (existsb_find _ _ Bx) as [kx Hkx]. destruct (existsb_find _ _ By) as [ky Hky]. rewrite Hkx, Hky in E. subst ky.
      apply find_some in Hkx as [_ Ex]. apply find_some in Hky as [_ Ey]. apply aptr_eqb_eq in Ex. apply aptr_eqb_eq in Ey.
      apply addr_inj; [exact Hx| exact Hy| congruence]. }
  assert (B2 : zcount (fun mi => Pc mi && isgrp mi) (slots_of st) <= hosted st c).
  { unfold hosted. apply (zcount_inj_le dec_mb _ _ grp_of); [apply (slots_of_nodup X st L BL LS INV)| |].
    - intros [m i] Hin Hq. apply andb_prop in Hq as [Hp Hg]. unfold isgrp in Hg. unfold grp_of.
      destruct (s_groups st !! addr (m, i)) as [h|] eqn:Eg; [| discriminate].
      destruct (im_hdr _ _ _ IM _ _ Eg) as (m' & Em' & MEM & _). rewrite Em'. cbn [default fst snd].
      destruct h as [gm gai]. cbn in Em'. subst gm.
      split; [apply gmetas_in; exists gai; exact Eg|].
      apply andb_true_intro. split.
      + apply Z.eqb_eq. pose proof (ig_ok _ _ _ IG _ _ _ Eg) as GO'.
        destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [|NZ]; [assumption|]. exfalso.
        destruct (g_top _ _ _ _ _ _ GO' NZ) as [Z0 _]. pose proof (addr_pos m i Hin). lia.
      + unfold slotcls. rewrite (addr_slot m i Hin). unfold cls. exact Hp.
    - intros x y Hx Hy _ _ E. unfold grp_of in E. apply addr_inj; [exact Hx| exact Hy| congruence]. }
  assert (B3 : zcount (fun mi => Pc mi && ispend mi) (slots_of st) <= match x_pend X with Some _ => 1 | None => 0 end).
  { destruct (x_pend X) as [s|] eqn:EP.
    - transitivity (zcount (fun _ : aptr => true) [s]); [| rewrite zcount_true, zlen_cons, zlen_nil; lia].
      apply (zcount_inj_le dec_ap _ _ addr); [apply (slots_of_nodup X st L BL LS INV)| |].
      + intros mi Hin Hq. apply andb_prop in Hq as [_ Hq]. unfold ispend in Hq. rewrite EP in Hq. apply aptr_eqb_eq in Hq. split; [left; exact Hq| reflexivity].
      + intros x y Hx Hy _ _ E. exact (addr_inj x y Hx Hy E).
    - rewrite zcount_false; [lia|]. intros mi _. unfold ispend. rewrite EP. apply andb_false_r. }
  lia.
Qed.
End INUSE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma zcount_cover2 {A} (p q1 q2 : A -> bool) l :
  (forall x, In x l -> p x = true -> q1 x = true \/ q2 x = true) -> zcount p l <= zcount q1 l + zcount q2 l.
Proof.
  intros H. pose proof (zcount_cover3 p q1 q2 (fun _ => false) l ltac:(intros x Hx Hp; destruct (H x Hx Hp); auto)) as C.
  rewrite (zcount_false (fun _ => false)) in C by auto. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zcount_by_class {A} (cf : A -> Z) (p : A -> bool) (l : list A) :
  (forall x, In x l -> p x = true -> 0 <= cf x < 48) ->
  zcount p l = zsum (map (fun c => zcount (fun x => p x && (cf x =? c)) l) classes).
Proof.
  intros H. rewrite zcount_eq_zsum.
  rewrite (zsum_by_class (fun x => if p x then cf x else 0) (fun x => if p x then 1 else 0) l).
  2:{ intros x Hx. destruct (p x) eqn:E; [apply H; assumption| lia]. }
  apply zsum_map_ext. intros c Hc. rewrite zcount_eq_zsum. apply zsum_map_ext. intros x Hx.
  destruct (p x); cbn; [reflexivity|]. destruct c; reflexivity.
Qed.

#[using="Type"] Lemma classes_zrange : classes = zrange 0 48.
Proof. reflexivity. Qed.

#[using="Type"] Lemma zsum_lt_indicator (v c : Z) : 0 <= c <= 48 -> zsum (map (fun c' => if c' <? c then v else 0) classes) = v * c.
Proof.
  intros Hc. unfold classes.
  assert (G : forall n, (Z.of_nat n <= 48)%Z -> zsum (map (fun c' => if c' <? c then 1 else 0) (map Z.of_nat (seq 0 n))) = Z.min c (Z.of_nat n)).
  { induction n as [|n IH]; intros Hn; [cbn; lia|]. rewrite seq_S, !map_app, zsum_app, IH by lia. cbn [map Nat.add]. rewrite zsum_cons, zsum_nil.
    destruct (Z.of_nat n <? c) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; rewrite Nat2Z.inj_succ; lia. }
  transitivity (zsum (map (fun c' => v * (if c' <? c then 1 else 0)) (map Z.of_nat (seq 0 48)))).
  - apply zsum_map_ext. intros c' _. destruct (c' <? c); lia.
  - rewrite zsum_map_mul, G by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CAPS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis SGH : SG st BL.
Hypothesis HAQ : AQ st BL P.
Let IM : inv_M X st LS := proj1 (proj2 (proj2 INV)).
Let IL : inv_L st LS := proj1 (proj2 (proj2 (proj2 INV))).
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="Type"] Lemma HOSTSTD_guest c' : 0 <= c' <= 6 -> HOSTSTD P c' = 0.
Proof.
  intros Hc. unfold HOSTSTD. transitivity (zsum (map (fun _ : Z => 0) guests)); [| rewrite zsum_map_const; lia].
  apply zsum_map_ext. intros g Hg. assert (G : 0 <= g <= 6) by (unfold guests in Hg; cbn in Hg; lia).
  destruct (tab_host_small g G) as (_ & BH & _). destruct (Z.eqb_spec (bighost g) c'); [lia| reflexivity].
Qed.

#[using="CE X L BL LS INV HAQ"] Lemma nstd_cap c' : 0 <= c' <= 6 -> nstd st c' <= (CAP0 P c' + 32) / cmax c'.
Proof.
  intros Hc. pose proof (nstd_le_gcnt X st L BL LS INV c' ltac:(lia)) as N1. pose proof (aq_slots _ _ _ HAQ c' ltac:(lia)) as A2.
  unfold CAP in A2. rewrite (HOSTSTD_guest c' Hc) in A2. pose proof (tab_basic_ok c' ltac:(lia)) as (_ & CM & _).
  apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
#[using="CE X L BL LS INV SGH HAQ IG"] Theorem hosted_le c : 0 <= c < 48 -> hosted st c <= HOSTSTD P c + (if c <=? 23 then 160 * c else 0).
Proof.
  intros Hc. unfold hosted.
  set (H := fun mb : aptr * aptr => (m_maplen (MR st (fst mb)) =? 0) && match slotcls st (snd mb) with Some c' => c' =? c | None => false end).
  (* [comment removed for export] *)
  assert (HF : forall m b, In (m, b) (gmetas st) -> H (m, b) = true ->
     exists ai p i, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ m_maplen (MR st m) = 0 /\ s_slots st !! b = Some (p, i) /\ m_sizeclass (MR st p) = c
       /\ 0 <= m_sizeclass (MR st m) < c /\ c <= 23).
  { intros m b Hin Hh. apply gmetas_in in Hin as [ai Hb]. unfold H in Hh. cbn in Hh. apply andb_prop in Hh as [M0 SC]. apply Z.eqb_eq in M0.
    pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. destruct (g_nest _ _ _ _ _ _ GO M0) as (p & i & Hs & _ & _ & LT & _).
    unfold slotcls in SC. rewrite Hs in SC. unfold cls in SC. apply Z.eqb_eq in SC.
    exists ai, p, i. pose proof (sg_host _ _ SGH b m ai p i Hb M0 Hs). destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(_ & _ & ? & _)]; [| congruence].
    repeat split; auto; lia. }
  etransitivity; [apply (zcount_cover2 H (fun mb => H mb && stdg st (fst mb)) (fun mb => H mb && negb (stdg st (fst mb))))|].
  { intros mb _ Hh. rewrite Hh. destruct (stdg st (fst mb)); auto. }
  apply Z.add_le_mono.
  - (* [comment removed for export] *)
    rewrite (zcount_by_class (fun mb => m_sizeclass (MR st (fst mb))) (fun mb => H mb && stdg st (fst mb)) (gmetas st)).
    2:{ intros [m b] Hin Hh. apply andb_prop in Hh as [Hh _]. destruct (HF m b Hin Hh) as (ai & p & i & _ & _ & _ & _ & R & _). cbn. lia. }
    transitivity (zsum (map (fun c' => if (c' <=? 6) && (bighost c' =? c) then (CAP0 P c' + 32) / cmax c' else 0) classes)).
    + apply zsum_map_le. intros c' Hc'. apply In_classes in Hc'.
      destruct (Z.leb_spec c' 6) as [LE|GT]; cbn [andb].
      * destruct (Z.eqb_spec (bighost c') c) as [BH|NBH].
        -- etransitivity; [| apply (nstd_cap c'); lia]. unfold nstd. apply zcount_mono. intros [m b] _ Hh.
           apply andb_prop in Hh as [Hh E]. apply andb_prop in Hh as [Hh SD]. cbn in E, SD |- *. unfold cls. rewrite E, SD. reflexivity.
        -- rewrite zcount_false; [lia|]. intros [m b] Hin. cbn [fst snd]. destruct (H (m, b)) eqn:Hh; [| reflexivity]. destruct (stdg st m) eqn:SD; [| reflexivity]. cbn.
           destruct (Z.eqb_spec (m_sizeclass (MR st m)) c') as [E|]; [| reflexivity]. exfalso. apply NBH.
           destruct (HF m b Hin Hh) as (ai & p & i & Hb & M0 & Hs & Ep & _). destruct (sg_std _ _ SGH b m ai Hb SD) as (_ & Q2 & _).
           destruct (Q2 M0) as (p' & i' & Hs' & Ep'). rewrite Hs in Hs'. assert (p' = p) by congruence. subst p'. rewrite <- E, <- Ep'. exact Ep.
      * rewrite zcount_false; [lia|]. intros [m b] Hin. cbn [fst snd]. destruct (H (m, b)) eqn:Hh; [| reflexivity]. destruct (stdg st m) eqn:SD; [| reflexivity]. cbn.
        destruct (Z.eqb_spec (m_sizeclass (MR st m)) c') as [E|]; [| reflexivity]. exfalso.
        destruct (HF m b Hin Hh) as (ai & p & i & Hb & M0 & Hs & Ep & R & _). destruct (sg_std _ _ SGH b m ai Hb SD) as (Q1 & _ & _).
        apply Q1 in M0. rewrite E in M0. destruct (tab_host_big c' ltac:(lia)) as [F _]. rewrite F in M0. discriminate.
    + apply Z.eq_le_incl. unfold HOSTSTD.
      change classes with (guests ++ map Z.of_nat (seq 7 41)). rewrite map_app, zsum_app.
      assert (Z0 : zsum (map (fun c' => if (c' <=? 6) && (bighost c' =? c) then (CAP0 P c' + 32) / cmax c' else 0) (map Z.of_nat (seq 7 41))) = 0).
      { transitivity (zsum (map (fun _ : Z => 0) (map Z.of_nat (seq 7 41)))); [| rewrite zsum_map_const; lia].
        apply zsum_map_ext. intros c' Hc'. apply in_map_iff in Hc' as (n & <- & Hn). apply in_seq in Hn. destruct (Z.leb_spec (Z.of_nat n) 6); [lia| reflexivity]. }
      rewrite Z0, Z.add_0_r. apply zsum_map_ext. intros c' Hc'. assert (G : 0 <= c' <= 6) by (unfold guests in Hc'; cbn in Hc'; lia).
      replace (c' <=? 6) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - (* [comment removed for export] *)
    destruct (Z.leb_spec c 23) as [LE|GT].
    + rewrite (zcount_by_class (fun mb => m_sizeclass (MR st (fst mb))) (fun mb => H mb && negb (stdg st (fst mb))) (gmetas st)).
      2:{ intros [m b] Hin Hh. apply andb_prop in Hh as [Hh _]. destruct (HF m b Hin Hh) as (ai & p & i & _ & _ & _ & _ & R & _). cbn. lia. }
      transitivity (zsum (map (fun c' => if c' <? c then 159 else 0) classes)); [| rewrite zsum_lt_indicator; lia].
      apply zsum_map_le. intros c' Hc'. apply In_classes in Hc'. destruct (Z.ltb_spec c' c) as [LT|GE].
      * transitivity (nsc st c'); [| pose proof (sg_small _ _ SGH c' Hc'); lia].
        unfold nsc. rewrite zcount_eq_zsum. apply zsum_map_le. intros [m b] Hin. cbn [fst snd]. unfold cls.
        apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
        destruct (H (m, b)); cbn; [| destruct (_ && _); unfold cnt_of; lia].
        destruct (stdg st m); cbn; [destruct (_ && _); unfold cnt_of; lia|]. destruct (m_sizeclass (MR st m) =? c'); cbn; unfold cnt_of; lia.
      * rewrite zcount_false; [lia|]. intros [m b] Hin. cbn [fst snd]. destruct (H (m, b)) eqn:Hh; [| reflexivity]. cbn.
        destruct (stdg st m); cbn; [reflexivity|]. destruct (Z.eqb_spec (m_sizeclass (MR st m)) c') as [E|]; [| reflexivity]. exfalso.
        destruct (HF m b Hin Hh) as (ai & p & i & _ & _ & _ & _ & R & _). lia.
    + rewrite zcount_false; [lia|]. intros [m b] Hin. cbn [fst snd]. destruct (H (m, b)) eqn:Hh; [| reflexivity]. exfalso.
      destruct (HF m b Hin Hh) as (ai & p & i & _ & _ & _ & _ & _ & C23). lia.
Qed.
End CAPS.

Section CAPS2.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis SGH : SG st BL.
Hypothesis HAQ : AQ st BL P.
Let IM : inv_M X st LS := proj1 (proj2 (proj2 INV)).
Let IL : inv_L st LS := proj1 (proj2 (proj2 (proj2 INV))).
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
#[using="SGH"] Lemma LS_le_LR3 c : 0 <= c < 48 -> LB_Inv.LS st BL c <= LR BL (c - 1) + LR BL c + LR BL (c + 1).
Proof.
  intros Hc. unfold LB_Inv.LS, LR. apply zcount_cover3. intros k Hk Hs.
  destruct (sg_cls _ _ SGH k Hk) as (m & i & Es & C48 & _). unfold slotcls in Hs. rewrite Es in Hs. unfold cls in Hs.
  apply Z.eqb_eq in Hs. destruct (C48 ltac:(lia)) as [SM E].
  unfold isbig. replace (MMAP_THRESHOLD <=? bsize k) with false by (symmetry; apply Z.leb_gt; exact SM). cbn [negb andb].
  assert (size_to_class (bsize k) = c - 1 \/ size_to_class (bsize k) = c \/ size_to_class (bsize k) = c + 1) as [E1|[E1|E1]] by lia;
    rewrite E1, Z.eqb_refl; auto.
Qed.

(* [comment removed for export] *)
#[using="CE X st L LS INV SGH HAQ IS"] Lemma LR_le_P c : LR BL c <= P c.
Proof.
  destruct (Z_le_gt_dec 0 c) as [H0|H0]; [destruct (Z_lt_ge_dec c 48) as [H1|H1]; [apply (aq_live _ _ _ HAQ); lia|]|];
    (etransitivity; [| apply (proj1 (aq_P _ _ _ HAQ c))]); apply Z.eq_le_incl; unfold LR; apply zcount_false;
    intros k Hk; unfold isbig; destruct (Z.leb_spec MMAP_THRESHOLD (bsize k)); [reflexivity| | reflexivity|]; cbn [negb andb];
    destruct (sg_cls _ _ SGH k Hk) as (m & i & Es & _); destruct (is_blocks _ _ _ IS k Hk) as (? & ? & _ & _ & Hz & _);
    pose proof (size_to_class_ok (bsize k) ltac:(lia)) as [R _]; apply Z.eqb_neq; lia.
Qed.

(* [comment removed for export] *)
#[using="CE L BL LS INV SGH HAQ IS"] Theorem creation_room c : 0 <= c < 48 -> x_fresh X = None -> active st c = None -> gcnt st c <= CAP P c.
Proof.
  intros Hc HF HA.
  pose proof (all_in_use X st L BL LS INV c Hc HF HA) as A.
  pose proof (LS_le_LR3 c Hc) as B1. pose proof (LR_le_P (c - 1)) as B2. pose proof (LR_le_P c) as B3. pose proof (LR_le_P (c + 1)) as B3'.
  pose proof (hosted_le X st L BL LS P INV SGH HAQ c Hc) as B4.
  unfold CAP, CAP0. destruct (x_pend X); lia.
Qed.

(* [comment removed for export] *)
Definition slot0_blk (mb : aptr * aptr) : blk :=
  match find (fun k => aptr_eqb (bslot k) (slot_start' (MR st (fst mb)) 0)) BL with Some k => k | None => ((0%N, 0), 0, 0) end.

#[using="CE X L LS INV SGH IG IS"] Lemma n63g_le : zcount (fun mb => m_sizeclass (MR st (fst mb)) =? 63) (gmetas st) <= n63 BL.
Proof.
  unfold n63. apply (zcount_inj_le (dec_blk) _ _ slot0_blk); [apply gmetas_nodup| |].
  - intros [m b] Hin H63. apply Z.eqb_eq in H63. apply gmetas_in in Hin as [ai Hb]. cbn in H63.
    pose proof (sg_63 _ _ SGH b m ai Hb H63) as HB. unfold slot0_blk. cbn [fst].
    assert (EX : existsb (fun k => aptr_eqb (bslot k) (slot_start' (MR st m) 0)) BL = true).
    { apply existsb_exists. apply in_map_iff in HB as (k & Ek & Hk). exists k. split; [exact Hk| apply aptr_eqb_eq; exact Ek]. }
    destruct (existsb_find _ _ EX) as [k Hk]. rewrite Hk. apply find_some in Hk as [Hk Ek]. apply aptr_eqb_eq in Ek. split; [exact Hk|].
    destruct (sg_cls _ _ SGH k Hk) as (m' & i' & Es & _ & C63).
    pose proof (is_total _ _ _ IS b m 0 (ex_intro _ ai Hb) ltac:(pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)); lia)) as T.
    rewrite Ek, T in Es. assert (m' = m) by congruence. subst m'. unfold isbig. destruct (C63 H63) as [GE _]. apply Z.leb_le. exact GE.
  - intros [m1 b1] [m2 b2] H1 H2 P1 P2 E. unfold slot0_blk in E. cbn [fst] in E.
    apply Z.eqb_eq in P1. apply Z.eqb_eq in P2. cbn in P1, P2.
    apply gmetas_in in H1 as [ai1 Hb1]. apply gmetas_in in H2 as [ai2 Hb2].
    assert (EX1 : existsb (fun k => aptr_eqb (bslot k) (slot_start' (MR st m1) 0)) BL = true).
    { apply existsb_exists. pose proof (sg_63 _ _ SGH b1 m1 ai1 Hb1 P1) as HB. apply in_map_iff in HB as (k & Ek & Hk). exists k. split; [exact Hk| apply aptr_eqb_eq; exact Ek]. }
    assert (EX2 : existsb (fun k => aptr_eqb (bslot k) (slot_start' (MR st m2) 0)) BL = true).
    { apply existsb_exists. pose proof (sg_63 _ _ SGH b2 m2 ai2 Hb2 P2) as HB. apply in_map_iff in HB as (k & Ek & Hk). exists k. split; [exact Hk| apply aptr_eqb_eq; exact Ek]. }
    destruct (existsb_find _ _ EX1) as [k1 Hk1]. destruct (existsb_find _ _ EX2) as [k2 Hk2]. rewrite Hk1, Hk2 in E. subst k2.
    apply find_some in Hk1 as [_ E1]. apply find_some in Hk2 as [_ E2]. apply aptr_eqb_eq in E1. apply aptr_eqb_eq in E2.
    pose proof (is_total _ _ _ IS b1 m1 0 (ex_intro _ ai1 Hb1) ltac:(pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb1)); lia)) as T1.
    pose proof (is_total _ _ _ IS b2 m2 0 (ex_intro _ ai2 Hb2) ltac:(pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb2)); lia)) as T2.
    rewrite <- E1, E2, T2 in T1. assert (m1 = m2) by congruence. subst m2.
    f_equal. exact (gmetas_meta_inj X st L BL LS INV _ _ _ ltac:(apply gmetas_in; exists ai1; exact Hb1) ltac:(apply gmetas_in; exists ai2; exact Hb2)).
Qed.

#[using="CE X L BL LS INV SGH HAQ IG IS"] Theorem ngroups_le : ngroups st <= NG P.
Proof.
  unfold ngroups, NG. rewrite <- zcount_true.
  etransitivity; [apply (zcount_cover2 (fun _ => true) (fun mb => m_sizeclass (MR st (fst mb)) <? 48) (fun mb => m_sizeclass (MR st (fst mb)) =? 63))|].
  { intros [m b] Hin _. cbn. destruct (gfacts X st L BL LS INV m b Hin) as (_ & _ & [[? ?]|[? _]]); [left; apply Z.ltb_lt; lia| right; apply Z.eqb_eq; assumption]. }
  pose proof n63g_le as N63. pose proof (aq_big _ _ _ HAQ) as A63.
  assert (C48 : zcount (fun mb => m_sizeclass (MR st (fst mb)) <? 48) (gmetas st) <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)); [| lia].
  rewrite (zcount_by_class (fun mb => m_sizeclass (MR st (fst mb))) _ (gmetas st)).
  2:{ intros [m b] Hin Hlt. apply Z.ltb_lt in Hlt. cbn in Hlt |- *. destruct (gfacts X st L BL LS INV m b Hin) as (_ & _ & [[? ?]|[? _]]); lia. }
  apply zsum_map_le. intros c Hc. apply In_classes in Hc.
  etransitivity; [apply (zcount_cover2 _ (fun mb => (cls st (fst mb) =? c) && stdg st (fst mb)) (fun mb => (cls st (fst mb) =? c) && negb (stdg st (fst mb))))|].
  { intros [m b] _ Hq. apply andb_prop in Hq as [_ E]. unfold cls. cbn in E |- *. rewrite E. destruct (stdg st m); auto. }
  change (zcount (fun mb => (cls st (fst mb) =? c) && stdg st (fst mb)) (gmetas st)) with (nstd st c).
  pose proof (nstd_le_gcnt X st L BL LS INV c Hc) as N1. pose proof (aq_slots _ _ _ HAQ c Hc) as A2. pose proof (tab_basic_ok c Hc) as (_ & CM & _).
  assert (D : nstd st c <= (CAP P c + 32) / cmax c) by (apply Z.div_le_lower_bound; lia).
  assert (NS : zcount (fun mb => (cls st (fst mb) =? c) && negb (stdg st (fst mb))) (gmetas st) <= nsc st c).
  { unfold nsc. rewrite zcount_eq_zsum. apply zsum_map_le. intros [m b] Hin. cbn [fst snd].
    apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)). destruct (_ && _); unfold cnt_of; lia. }
  pose proof (sg_small _ _ SGH c Hc). lia.
Qed.

(* [comment removed for export] *)
#[using="CE L BL LS INV IM IL"] Theorem ncarved_le_groups d : QM X st d -> c_free_meta_head (ctx st) = None -> x_zomb X = [] ->
  ncarved st <= ngroups st + zlen (x_idle X).
Proof.
  intros Q HFH HZ. unfold ncarved, ngroups.
  transitivity (zcount (fun _ : aptr => true) (map fst (gmetas st) ++ x_idle X)); [| rewrite zcount_true, zlen_app, zlen_map; lia].
  rewrite <- zcount_true.
  assert (EMP : LS LFree = []).
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. rewrite HFH in HH. destruct (LS LFree); [reflexivity| cbn in HH; discriminate]. }
  apply (zcount_inj_le dec_ap _ _ fst); [apply mtl_nodup| |].
  - intros [m mr] Hin _. apply mtl_in in Hin. cbn. split; [| reflexivity]. apply in_app_iff.
    destruct (m_mem mr) as [b|] eqn:MM.
    + left. pose proof (im_group _ _ _ IM m b ltac:(rewrite (MR_of_lookup st m mr Hin); exact MM)) as [Hh|Hz]; [| rewrite HZ in Hz; destruct Hz].
      destruct Hh as [ai Hb]. apply in_map_iff. exists (m, b). split; [reflexivity| apply gmetas_in; exists ai; exact Hb].
    + destruct (qmm_leak _ _ _ Q m mr Hin MM) as [NN|ID]; [| right; exact ID]. exfalso.
      assert (INL : in_list LS m) by (apply (proj1 (il_link _ _ IL m)); rewrite (MR_of_lookup st m mr Hin); exact NN).
      destruct INL as [h Hh]. destruct h as [sc|].
      * destruct (il_active _ _ IL sc m Hh) as (_ & [b Hb] & _). rewrite (hosts_mem _ _ _ IM _ _ Hb) in MM || (pose proof (hosts_mem _ _ _ IM _ _ Hb) as MM2; rewrite (MR_of_lookup st m mr Hin) in MM2; rewrite MM2 in MM; discriminate).
        all: try discriminate.
      * rewrite EMP in Hh. destruct Hh.
  - intros [m1 r1] [m2 r2] H1 H2 _ _ E. cbn in E. subst m2. apply mtl_in in H1. apply mtl_in in H2. rewrite H1 in H2. inversion H2. reflexivity.
Qed.
End CAPS2.

End WithCeil.
End LB_Cnt.

(* [comment removed for export] *)
Module LB_AG.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WCreate2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_XferF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Cnt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition cnt_tab_f (sc : Z) : bool :=
  (if sc <? 9 then (small_cnt sc 0 <=? 32) && (1 <=? small_cnt sc 0) else true) && (med_cnt (Z.land sc 3) <=? 32) && (1 <=? med_cnt (Z.land sc 3)).
#[using="Type"] Lemma cnt_tab_ok sc : 0 <= sc < 48 -> (sc < 9 -> 1 <= small_cnt sc 0 <= 32) /\ 1 <= med_cnt (Z.land sc 3) <= 32.
Proof.
  intros Hsc. assert (H : forallb cnt_tab_f classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes _ H sc Hsc) as T. unfold cnt_tab_f in T.
  apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2]. apply Z.leb_le in T2. apply Z.leb_le in T3.
  split; [| lia]. intros H9. replace (sc <? 9) with true in T1 by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in T1 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cnt0_of_ge128 sc u : 0 <= sc < 48 -> 128 <= u -> cnt0_of sc u = cmax sc.
Proof.
  intros Hsc Hu. destruct (cnt_tab_ok sc Hsc) as [S0 M0]. unfold cnt0_of, cmax, S_.
  destruct (Z.ltb_spec sc 9) as [L9|G9].
  - unfold small_cnt_pick. replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; specialize (S0 L9); lia). reflexivity.
  - f_equal. cbn [halve_even]. replace (u <? 4 * med_cnt (Z.land sc 3)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma bump_big size c : 8 <= c -> bump size c = c.
Proof. intros H. unfold bump. replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

#[using="Type"] Lemma adj_small sc size c : adj sc size c = c \/ adj sc size c <= 5.
Proof. unfold adj. repeat (destruct (_ && _); [right; lia|]). left. reflexivity. Qed.

(* [comment removed for export] *)
Definition nest_host_f (sc : Z) : bool :=
  let size := UNIT * size_class sc in
  forallb (fun cnt0 => let cnt1 := bump size cnt0 in
     (PGSZ / 2 <? size * cnt1 + UNIT)
     || (let j := size_to_class (UNIT + cnt1 * size - IB) in (j =? 15) || (j =? 19) || (j =? 23))) (cnt0_list sc).
#[using="Type"] Lemma nest_host_all : forallb nest_host_f classes = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma nest_host sc u : 0 <= sc < 48 ->
  let size := UNIT * size_class sc in let cnt1 := bump size (cnt0_of sc u) in
  size * cnt1 + UNIT <= PGSZ / 2 ->
  let j := size_to_class (UNIT + cnt1 * size - IB) in j = 15 \/ j = 19 \/ j = 23.
Proof.
  intros Hsc. cbn zeta. intros HB. pose proof (forallb_classes _ nest_host_all sc Hsc) as T. unfold nest_host_f in T.
  rewrite forallb_forall in T. specialize (T _ (cnt0_in sc u)). cbn zeta in T.
  apply orb_prop in T as [T|T]; [apply Z.ltb_lt in T; lia|].
  apply orb_prop in T as [T|T]; [apply orb_prop in T as [T|T]|]; apply Z.eqb_eq in T; auto.
Qed.

(* [comment removed for export] *)
Definition rank (c : Z) : Z := if c <? 15 then 0 else if c <? 19 then 1 else if c <? 23 then 2 else 3.
#[using="Type"] Lemma rank_host c j : 0 <= c < j -> (j = 15 \/ j = 19 \/ j = 23) -> rank c + 1 <= rank j <= 3.
Proof. intros Hc Hj. unfold rank. destruct Hj as [->|[->| ->]]; destruct (Z.ltb_spec c 15); destruct (Z.ltb_spec c 19); destruct (Z.ltb_spec c 23); cbn; lia. Qed.
#[using="Type"] Lemma rank_range c : 0 <= rank c <= 3.
Proof. unfold rank. destruct (c <? 15); [lia|]. destruct (c <? 19); [lia|]. destruct (c <? 23); lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AGTQ.
Variables (X X' : extras) (stI st : mstate) (L L' : mled) (BL : list blk) (LS LS' : lhead -> list aptr) (P : Z -> Z).
Variables (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
(* [comment removed for export] *)
Hypothesis INV : INVL X stI L BL LS.
Hypothesis INV' : INVL X' st' L' BL LS'.
Hypothesis LKg : s_groups st = s_groups stI.
Hypothesis LKs : s_slots st = s_slots stI.
Hypothesis LKr : s_regions st = s_regions stI.
Hypothesis LKm : forall x, x <> m -> s_metas st !! x = s_metas stI !! x.
Hypothesis LKc : c_avail_meta_count (s_ctx st) = c_avail_meta_count (s_ctx stI) /\ c_avail_meta_areas (s_ctx st) = c_avail_meta_areas (s_ctx stI)
  /\ c_meta_alloc_shift (s_ctx st) = c_meta_alloc_shift (s_ctx stI).
Hypothesis Hm : s_metas st !! m <> None.
Hypothesis HmI : s_metas stI !! m = Some meta0.
Hypothesis Hp : s_groups stI !! p = None.
Hypothesis SGst : SG stI BL.
Hypothesis Q : QM X stI 0.
Hypothesis XI : forall x, In x (x_idle X) -> x = m \/ In x (x_idle X').
Hypothesis HAQ : AQ stI BL P.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis ROOM : gcnt stI sc <= CAP P sc.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis NEWG : m_sizeclass (MR st' m) = sc /\ m_last_idx (MR st' m) = cnt - 1.
Hypothesis QG_map : m_maplen (MR st' m) <> 0 -> m_maplen (MR st' m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots stI !! p = None.
(* [comment removed for export] *)
Hypothesis QG_one : cnt = 1 -> m_maplen (MR st' m) <> 0 ->
  m_maplen (MR st' m) * 4096 <= S_ sc + UNIT \/ (34 <= sc /\ m_maplen (MR st' m) * 4096 <= round_up_pg (S_ sc + UNIT)).
Hypothesis QG_nest : m_maplen (MR st' m) = 0 -> exists g i, s_slots stI !! p = Some (g, i) /\ m_sizeclass (MR stI g) <= 23
   /\ (stdg st' m = true -> m_sizeclass (MR stI g) = bighost sc).
Hypothesis QG_std : stdg st' m = true -> (m_maplen (MR st' m) = 0 <-> std_nested sc = true) /\ (m_maplen (MR st' m) <> 0 -> m_maplen (MR st' m) * 4096 = std_len sc).
Hypothesis QG_small : stdg st' m = false -> gcnt stI sc < 128.

#[using="LKm"] Lemma MR_st x : x <> m -> MR st x = MR stI x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite (LKm x NE). reflexivity. Qed.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let IM' := proj1 (proj2 (proj2 INV')).
Let IG' := proj1 (proj2 (proj2 (proj2 (proj2 INV')))).
Let IS' := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))).

#[using="CE X L BL LS INV LKm HmI IM"] Lemma aq_old x : (exists b, hosts stI b x) -> x <> m /\ MR st' x = MR stI x.
Proof.
  intros [b [aix Hb]]. assert (NE : x <> m).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ (ex_intro _ aix Hb)) as MM. rewrite (MR_of_lookup stI m meta0 HmI) in MM. cbn in MM. discriminate. }
  split; [exact NE|]. unfold st'. rewrite agt_MR_other by exact NE. apply MR_st. exact NE.
Qed.

#[using="LKg"] Lemma aq_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups stI).
Proof. unfold st'. rewrite agt_groups, LKg. reflexivity. Qed.

#[using="CE X' L' BL LS' INV' LKg Hp NEWG QG_map QG_one QG_nest QG_std QG_small"] Lemma aq_hosts_old b x : hosts stI b x -> hosts st' b x.
Proof.
  intros [aix Hb]. exists aix. rewrite aq_groups. rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite Hp in Hb. discriminate.
Qed.

#[using="CE X X' L L' BL LS LS' INV INV' LKg LKm HmI Hp NEWG QG_map QG_one QG_nest QG_std QG_small IM IS IS'"] Lemma aq_slots_old s v : s_slots stI !! s = Some v -> s_slots st' !! s = Some v.
Proof.
  intros Hs. destruct v as [x i]. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  destruct (aq_old x (ex_intro _ b Hb)) as [NE MRx].
  pose proof (is_total _ _ _ IS' b x i (aq_hosts_old b x Hb) ltac:(rewrite MRx; exact Hi)) as T. rewrite MRx, <- Es in T. exact T.
Qed.

#[using="LKg Hp"] Lemma aq_gmetas : Permutation (gmetas st') ((m, p) :: gmetas stI).
Proof.
  unfold gmetas, groups_l. rewrite aq_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact Hp|]. cbn. apply Permutation_refl.
Qed.

#[using="CE X L BL LS INV LKm HmI IM"] Lemma aq_stdg_old x : (exists b, hosts stI b x) -> stdg st' x = stdg stI x.
Proof. intros Hx. destruct (aq_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

#[using="CE X X' L L' BL LS LS' INV INV' LKg LKm HmI Hp NEWG QG_map QG_one QG_nest QG_std QG_small IM IS IS'"] Lemma aq_slotcls_old s : s_slots stI !! s <> None -> slotcls st' s = slotcls stI s.
Proof.
  intros Hs. destruct (s_slots stI !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (aq_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (aq_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

#[using="Type"] Lemma gmetas_hosts x b : In (x, b) (gmetas stI) -> exists b', hosts stI b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

(* [comment removed for export] *)
#[using="LKg Hp"] Lemma aq_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas stI) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st')) = F' (m, p) + zsum (map F (gmetas stI)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ aq_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.
#[using="LKg Hp"] Lemma aq_count (F F' : aptr * aptr -> bool) :
  (forall x b, In (x, b) (gmetas stI) -> F' (x, b) = F (x, b)) ->
  zcount F' (gmetas st') = (if F' (m, p) then 1 else 0) + zcount F (gmetas stI).
Proof. intros HF. rewrite !zcount_eq_zsum. apply (aq_sum (fun x => if F x then 1 else 0)). intros x b Hin. rewrite (HF x b Hin). reflexivity. Qed.

#[using="CE X L BL LS INV LKg LKm HmI Hp NEWG IM"] Lemma aq_gcnt c : gcnt st' c = (if sc =? c then cnt else 0) + gcnt stI c.
Proof.
  rewrite !gcnt_gmetas. rewrite (aq_sum (fun mb => if m_sizeclass (MR stI (fst mb)) =? c then cnt_of (MR stI (fst mb)) else 0)).
  - cbn [fst]. destruct NEWG as [E1 E2]. unfold cnt_of. rewrite E1, E2. destruct (sc =? c); lia.
  - intros x b Hin. cbn [fst]. destruct (aq_old x (gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

#[using="CE X L BL LS INV LKg LKm HmI Hp NEWG IM"] Lemma aq_nsc c : nsc st' c = (if (sc =? c) && negb (stdg st' m) then cnt else 0) + nsc stI c.
Proof.
  unfold nsc. rewrite (aq_sum (fun mb => if (cls stI (fst mb) =? c) && negb (stdg stI (fst mb)) then cnt_of (MR stI (fst mb)) else 0)).
  - cbn [fst]. destruct NEWG as [E1 E2]. unfold cls, cnt_of. rewrite E1, E2. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (gmetas_hosts x b Hin) as Hx. rewrite (aq_stdg_old x Hx). destruct (aq_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

#[using="LKm LKc Hm HmI Hsc CNT NEWG"] Lemma aq_ncarved : ncarved st' = ncarved stI.
Proof.
  transitivity (ncarved st).
  - destruct (s_metas st !! m) as [r|] eqn:E; [| congruence]. unfold ncarved, st'. rewrite agt_metas. unfold zlen.
    rewrite (Permutation_length (mtl_insert_old (s_metas st) m _ r E)), (Permutation_length (mtl_delete (s_metas st) m r E)). reflexivity.
  - apply ncarved_dom. intros x. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite HmI; split; [congruence| intros _; exact Hm]|]. rewrite (LKm x NE). tauto.
Qed.

#[using="CE X X' L L' LS LS' INV INV' LKg LKm HmI Hp NEWG QG_map QG_one QG_nest QG_std QG_small IM IS IS'"] Lemma aq_LS c : LB_Inv.LS st' BL c = LB_Inv.LS stI BL c.
Proof.
  unfold LB_Inv.LS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (aq_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.
#[using="CE X X' L L' LS LS' INV INV' LKg LKm HmI Hp NEWG QG_map QG_one QG_nest QG_std QG_small IM IS IS'"] Lemma aq_MIS c : MIS st' BL c = MIS stI BL c.
Proof.
  unfold MIS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (aq_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.

#[using="CE X stI L L' LS LS' INV INV' LKg LKr LKm LKc Hm HmI Hp SGst Q XI HAQ Hsc ROOM CNT NEWG QG_map QG_one QG_nest QG_std QG_small IM IG IS IS'"] Theorem agt_quant : SG st' BL /\ QM X' st' 0 /\ AQ st' BL P.
Proof.
  destruct NEWG as [E1 E2].
  assert (GRP' : forall b x aix, s_groups st' !! b = Some (mkGhdr (Some x) aix) -> (x = m /\ b = p) \/ (x <> m /\ s_groups stI !! b = Some (mkGhdr (Some x) aix) /\ MR st' x = MR stI x)).
  { intros b x aix Hb. rewrite aq_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (aq_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  split; [| split].
  - (* [comment removed for export] *) destruct SGst as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k Hk. destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (aq_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (aq_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + intros b x aix Hb Hl Hml Hc. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1, E2 in *. apply QG_one; [lia| exact Hml].
      * rewrite MRx in *. exact (S2 _ _ _ Hb0 Hl Hml Hc).
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1, E2 in *. unfold cnt_of. rewrite E2. replace (cnt - 1 + 1) with cnt by lia. exact (proj1 (QG_map Hml)).
      * rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1. destruct (QG_std SD) as [Q1 Q3]. split; [exact Q1|]. split; [| exact Q3].
        intros Z0. destruct (QG_nest Z0) as (g & i & Hs & _ & BH). exists g, i. split; [exact (aq_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact (BH SD).
      * rewrite (aq_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3).
        split; [exact Q1|]. split; [| exact Q3]. intros Z0. destruct (Q2 Z0) as (g & i & Hs & Eg). exists g, i. split; [exact (aq_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact Eg.
    + intros c Hc. rewrite aq_nsc. specialize (S5 c Hc). destruct (Z.eqb_spec sc c) as [<-|NE]; cbn [andb]; [| lia].
      destruct (stdg st' m) eqn:SD; cbn [negb]; [lia|]. pose proof (QG_small eq_refl). pose proof (nsc_le_gcnt X stI L BL LS INV sc). lia.
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite E1 in H63; lia|]. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * destruct (QG_nest Z0) as (g0 & i0 & Hs & C23 & _). rewrite (aq_slots_old _ _ Hs) in Hs'. assert (g0 = g) by congruence. subst g0.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact C23.
      * rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g0 & i0 & Hs & _).
        rewrite (aq_slots_old _ _ Hs) in Hs'. assert (g0 = g /\ i0 = i) as [-> ->] by (split; congruence).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  - (* [comment removed for export] *) destruct LKc as (C1 & C2 & C3).
    assert (RG' : s_regions st' = s_regions stI) by (unfold st'; rewrite agt_regions; exact LKr).
    assert (AP' : apages st' = apages stI) by (apply apages_ext; [exact RG'| unfold st'; rewrite agt_ctx; cbn; exact C2]).
    assert (CK' : c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx stI)) by (unfold st'; rewrite agt_ctx; cbn; exact C1).
    assert (SH' : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx stI)) by (unfold st'; rewrite agt_ctx; cbn; exact C3).
    destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?RG', ?aq_ncarved, ?AP', ?CK', ?SH'; auto.
    intros x mr Hx Z0. unfold st' in Hx. rewrite agt_metas in Hx. destruct (aptr_eq_dec x m) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. exfalso. revert Z0.
      (* [comment removed for export] *)
      (intros Z1; cbn [agG m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_mem] in Z1; discriminate Z1).
    + rewrite lookup_insert_ne in Hx by congruence. rewrite (LKm x NE) in Hx.
      destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. destruct (XI x I0) as [->|I1]; [congruence| right; exact I1].
  - (* [comment removed for export] *) destruct HAQ as [A1 A2 A3 A4 A5]. constructor; auto.
    + intros c Hc. rewrite aq_gcnt. specialize (A2 c Hc). destruct (Z.eqb_spec sc c) as [<-|NE]; lia.
    + rewrite aq_ncarved. exact A4.
Qed.
End AGTQ.

End WithCeil.
End LB_AG.

(* [comment removed for export] *)
Module LB_WAMeta.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Caps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_XferF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma gmetas_ext st st1 : s_groups st1 = s_groups st -> gmetas st1 = gmetas st.
Proof. intros E. unfold gmetas, groups_l. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma gcnt_frame st st1 c : s_groups st1 = s_groups st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> gcnt st1 c = gcnt st c.
Proof.
  intros EG GEO. rewrite !gcnt_gmetas, (gmetas_ext st st1 EG). apply zsum_map_ext. intros [m b] Hin. cbn.
  apply gmetas_in in Hin as [ai Hb]. pose proof (GEO m (ex_intro _ b (ex_intro _ ai Hb))) as G. unfold geom in G. inversion G.
  unfold cnt_of. rewrite H1, H2. reflexivity.
Qed.

#[using="Type"] Lemma AQ_frame st st1 BL P : s_groups st1 = s_groups st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> ncarved st1 <= NCAP P ->
  AQ st BL P -> AQ st1 BL P.
Proof.
  intros EG GEO NC A. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  intros c Hc. rewrite (gcnt_frame st st1 c EG GEO). exact (A2 c Hc).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma am_bytes X st L BL LS d : INVL X st L BL LS -> QM X st d ->
  gm L + BB L <= group_bytes st + PGSZ * (5 * (ncarved st / 101) + 6)
  /\ meta_bytes st <= PGSZ * (if c_meta_alloc_shift (s_ctx st) <? 1 then 0 else 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) - 2)
  /\ PGSZ * brk_pages st <= PGSZ * (ncarved st / 101 + 2)
  /\ gm L + BB L <= group_bytes st + meta_bytes st + PGSZ * brk_pages st.
Proof.
  intros INV Q. pose proof (proj1 INV) as IR. destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6].
  pose proof (ledger_bound X st L BL LS INV) as LB.
  pose proof (meta_bytes_bound4 st Q4 Q5 Q6) as M4. pose proof (meta_bytes_pow st Q4 Q5) as MP.
  pose proof (brk_pages_boundQ X st L IR Q3) as BP. unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma div101_mono n N : 0 <= n <= N -> 5 * (n / 101) <= 5 * N / 101.
Proof. intros H. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod n 101 ltac:(lia)). pose proof (Z.mod_pos_bound n 101 ltac:(lia)). pose proof (Z.div_le_mono n N 101 ltac:(lia) ltac:(lia)). nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AMQ.
Variables (T : Type) (BL : list blk) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVL X st0 L0 BL LS0.
Hypothesis SG0 : SG st0 BL.
Hypothesis HAQ0 : AQ st0 BL P.
Hypothesis ROOM0 : c_free_meta_head (s_ctx st0) = None -> ncarved st0 + 1 <= NCAP P.
Hypothesis HB : group_bytes st0 + PGSZ * (5 * NCAP P / 101 + 8) <= B.
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 ->
  SINV X st1 BL -> AQ st1 BL P -> (forall c, gcnt st1 c = gcnt st0 c) ->
  (forall m, (exists b, hosts st0 b m) -> geom (MR st1 m) = geom (MR st0 m)) -> fqtree B L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 ->
  SINV (xidle X (m :: x_idle X)) st1 BL -> AQ st1 BL P -> ncarved st1 <= ncarved st0 + 1 -> (forall c, gcnt st1 c = gcnt st0 c) ->
  (forall x, (exists b, hosts st0 b x) -> geom (MR st1 x) = geom (MR st0 x)) ->
  fqtree B L1 (k st1 (Some m)) Post.

(* [comment removed for export] *)
Definition QT (Y : extras) (st : mstate) (d : Z) : Prop :=
  QM Y st d /\ ncarved st = ncarved st0 /\ group_bytes st = group_bytes st0
  /\ (forall m, (exists b, hosts st0 b m) -> geom (MR st m) = geom (MR st0 m)).

#[using="CE BL X L0 LS0 INV0"] Lemma SV0 : forall s m i, s_slots st0 !! s = Some (m, i) -> exists b, hosts st0 b m.
Proof. intros s m i H. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0)))))) _ _ _ H)). Qed.

#[using="CE X L0 LS0 INV0 SG0"] Lemma SG_of st : AM_frame st0 st -> (forall m, (exists b, hosts st0 b m) -> geom (MR st m) = geom (MR st0 m)) -> SG st BL.
Proof. intros AF GEO. apply (SG_frame st0 st BL (amf_groups _ _ AF) (amf_slots _ _ AF) GEO SV0 SG0). Qed.

(* [comment removed for export] *)
#[using="P LS0 INV0 SG0 HAQ0 KN"] Lemma exit_none st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> QT X st 0 -> fqtree B L (k st None) Post.
Proof.
  intros INV AF LF (Q & NC & GB & GEO). apply (KN st L LS INV AF LF).
  - apply SINV_split. split; [exact (SG_of st AF GEO)| exact Q].
  - apply (AQ_frame st0 st BL P (amf_groups _ _ AF) GEO); [rewrite NC; exact (aq_carved _ _ _ HAQ0)| exact HAQ0].
  - intros c. exact (gcnt_frame st0 st c (amf_groups _ _ AF) GEO).
  - exact GEO.
Qed.

#[using="P HAQ0 HB"] Lemma bound_of st L LS d extra : INVL X st L BL LS -> QT X st d -> 0 <= extra <= 2 * PGSZ ->
  gm L + BB L + extra <= B.
Proof.
  intros INV (Q & NC & GB & GEO) HE. destruct (am_bytes X st L BL LS d INV Q) as (A & _).
  rewrite NC, GB in A. pose proof (div101_mono (ncarved st0) (NCAP P) ltac:(pose proof (ncarved_nonneg st0); pose proof (aq_carved _ _ _ HAQ0); lia)). unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
#[using="LS0 INV0 SG0 HAQ0 KS"] Lemma am_take_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> QT X st 0 -> fqtree B L (am_take st k bail) Post.
Proof.
  intros ROOM INV AF LF HC (Q & NC & GB & GEO).
  destruct (ia_avail _ (proj1 (proj2 INV))) as [A1 A2]. destruct (A2 HC) as (a & Ht & Ea & FREE).
  set (m := mslot a (NSLOTS - c_avail_meta_count (s_ctx st))) in *.
  pose proof (take_fresh X st L BL LS m INV HC Ea) as FRm.
  rewrite (am_take_unfold st m k bail Ea).
  (* [comment removed for export] *)
  destruct (am_take_ok X st L BL LS INV HC (fun s o => ret (s, o)) (ret (st, @None aptr))) as (m' & st2 & E2 & INV2 & AF2 & NI).
  rewrite (am_take_unfold st m _ _ Ea) in E2. assert (Em : m' = m) by (inversion E2; reflexivity). assert (Es : st2 = take_st st m) by (inversion E2; reflexivity). subst m' st2.
  destruct (QM_take X st m 0 FRm Q) as (Q2 & NC2 & RG2 & AP2 & MR2).
  assert (GEO2 : forall x, (exists b, hosts st0 b x) -> geom (MR (take_st st m) x) = geom (MR st0 x)).
  { intros x Hx. rewrite MR2; [exact (GEO x Hx)|]. intros ->.
    destruct Hx as [b [ai Hb]]. pose proof (im_hdr _ _ _ (proj1 (proj2 (proj2 INV0))) _ _ Hb) as (m1 & Em1 & MEM & _). cbn in Em1. assert (m1 = m) by congruence. subst m1.
    pose proof (GEO m (ex_intro _ b (ex_intro _ ai Hb))) as G. assert (Z0 : m_mem (MR st m) = None) by (unfold MR, get_meta_rec; rewrite FRm; reflexivity). unfold geom in G. rewrite Z0, MEM in G. congruence. }
  apply (KS (take_st st m) L LS m INV2 NI (amf_trans _ _ _ AF AF2) LF).
  - apply SINV_split. split; [| exact Q2]. exact (SG_of (take_st st m) (amf_trans _ _ _ AF AF2) GEO2).
  - apply (AQ_frame st0 (take_st st m) BL P (amf_groups _ _ (amf_trans _ _ _ AF AF2)) GEO2); [| exact HAQ0].
    rewrite NC2, NC. exact ROOM.
  - rewrite NC2, NC. lia.
  - intros c. exact (gcnt_frame st0 (take_st st m) c (amf_groups _ _ (amf_trans _ _ _ AF AF2)) GEO2).
  - exact GEO2.
Qed.

(* [comment removed for export] *)
#[using="LS0 INV0 SG0 HAQ0 KS"] Lemma am_carve_fq s p L LS : ncarved st0 + 1 <= NCAP P -> INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> QT X s 101 -> c_avail_meta_count (s_ctx s) = 0 ->
  fqtree B L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros ROOM INV H1 H2 H3 H4 H5 H6 AF LF (Q & NC & GB & GEO) HK.
  destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  destruct (carve_rest_q s p) as (R1 & R2 & R3 & R4 & R5 & R6).
  eapply am_take_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC|].
  split; [exact (QM_carve_rest X s p 101 Q HK ltac:(lia))|]. split; [rewrite (ncarved_ext s _ R2); exact NC|].
  split; [rewrite (group_bytes_ext s _ R1); exact GB|]. intros m Hm. rewrite <- (GEO m Hm). unfold MR, get_meta_rec. rewrite R2. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="LS0 INV0 SG0 HAQ0 HB KN KS"] Lemma am_finish_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 -> QT X st 0 -> c_avail_meta_count (s_ctx st) = 0 ->
  fqtree B L (am_finish st true k bail) Post.
Proof.
  intros ROOM INV AF LF HC HI QT0 HK. pose proof QT0 as (Q & NC & GB & GEO).
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply fqtree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| | | | exact I].
  - intros z Hz. unfold event_post. pose proof (bound_of st L LS 0 0 INV QT0 ltac:(unfold PGSZ; lia)) as B0.
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [rewrite gm_bump, BB_set_metas|]; lia.
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_fq; [exact ROOM| exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')| | |].
      * destruct LF; constructor; assumption.
      * split; [| split; [exact NC| split; [exact GB| exact GEO]]].
        replace 101 with (0 + 101) by reflexivity. apply (QM_adv X st L rid off r 0 (proj1 INV) EC Hr K P2 Q).
      * exact HK.
    + eapply exit_none; [exact INV| exact AF| exact LF| exact QT0].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

(* [comment removed for export] *)
#[using="LS0 INV0 SG0 HAQ0 HB KN KS"] Lemma am_after_brk_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> QT X st 0 -> c_avail_meta_count (s_ctx st) = 0 ->
  fqtree B L (am_after_brk st true k bail) Post.
Proof.
  intros ROOM INV AF LF HI QT0 HK. pose proof QT0 as (Q & NC & GB & GEO). unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - destruct (am_bytes X st L BL LS 0 INV Q) as (A1 & A2 & A3 & A4).
    destruct (nm_n X st L BL LS INV) as [En N2].
    pose proof (div101_mono (ncarved st0) (NCAP P) ltac:(pose proof (ncarved_nonneg st0); pose proof (aq_carved _ _ _ HAQ0); lia)) as DM.
    assert (LEN : mmap_len (Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ) = Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ).
    { apply mmap_len_of_aligned; [unfold PGSZ; lia| unfold PGSZ; apply Z_mod_mult]. }
    assert (MAIN : gm L + BB L + Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ <= B).
    { rewrite En in *. rewrite Z.pow_add_r in * by (try lia; pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). change (2 ^ 1) with 2 in *.
      rewrite NC, GB in *.
      destruct (Z.ltb_spec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
      - assert (E0 : c_meta_alloc_shift (s_ctx st) = 0) by (pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). rewrite E0 in *. cbn in *. unfold PGSZ in *. lia.
      - pose proof (exhausted_shift X st L 0 (proj1 INV) Q (ltac:(unfold ctx in HC; exact HC)) HK ltac:(lia) S1) as EX. rewrite NC in EX.
        set (t := 2 ^ c_meta_alloc_shift (s_ctx st)) in *.
        assert (TQ : t - 1 <= ncarved st0 / 101) by (apply Z.div_le_lower_bound; lia).
        unfold PGSZ in *. lia. }
    pose proof (gm_BB_nonneg X st L BL LS INV) as [GM0 BB0].
    (* [comment removed for export] *)
    assert (REQ : mmap_len (Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ) <= QMAX).
    { rewrite LEN. pose proof (AQ_NCAP _ _ _ HAQ0) as HNC. rewrite En.
      rewrite Z.pow_add_r by (try lia; pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). change (2 ^ 1) with 2.
      destruct (Z.ltb_spec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
      - assert (E0 : c_meta_alloc_shift (s_ctx st) = 0) by (pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). rewrite E0. unfold QMAX, PGSZ. cbn. lia.
      - pose proof (exhausted_shift X st L 0 (proj1 INV) Q (ltac:(unfold ctx in HC; exact HC)) HK ltac:(lia) S1) as EX. rewrite NC in EX.
        set (t := 2 ^ c_meta_alloc_shift (s_ctx st)) in *.
        assert (TQ : t - 1 <= NCAPMAX / 101) by (apply Z.div_le_lower_bound; [lia|]; unfold NCAPMAX in *; lia).
        unfold QMAX, NCAPMAX, PGSZ in *. cbn in TQ. lia. }
    apply fqtree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| | | | intros _; unfold ctx; exact REQ].
    + (* [comment removed for export] *)
      intros z Hz. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn iota.
      pose proof (proj2 (nm_n X st L BL LS INV)) as N2'.
      destruct (is_err z); [unfold PGSZ in *; lia|]. rewrite gm_add_meta, BB_set_metas. unfold ctx. rewrite LEN. lia.
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply exit_none; [exact INV| exact AF| exact LF| exact QT0].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        destruct (QM_new_meta X st L BL LS a 0 INV HC HK Q ltac:(lia)) as (Q2 & NC2 & AP2 & GB2 & MB2 & BP2 & MR2 & SH2 & EX2).
        eapply am_finish_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI| | reflexivity || exact HK].
        split; [exact Q2|]. split; [rewrite NC2; exact NC|]. split; [rewrite GB2; exact GB|]. intros m Hm. rewrite MR2. exact (GEO m Hm).
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_fq; [exact ROOM| exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI| exact QT0| exact HK].
Qed.

#[using="Type"] Lemma QT_am_init Y st d : QT Y st d -> QT Y (am_init st) d.
Proof.
  intros (Q & NC & GB & GEO). unfold am_init. destruct (c_init_done (ctx st) =? 0); [| split; auto].
  split; [| split; [exact NC| split; [exact GB| exact GEO]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]; constructor; cbn -[apages ncarved]; auto.
  all: replace (apages (upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st)) with (apages st) by (apply apages_ext; reflexivity); exact Q2.
Qed.

#[using="Type"] Lemma QT_brk_dead Y st d : QT Y st d -> QT Y (upd_ctx (set_brk BrkDead) st) d.
Proof.
  intros (Q & NC & GB & GEO). split; [| split; [exact NC| split; [exact GB| exact GEO]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]; constructor; cbn -[apages ncarved]; auto.
  all: replace (apages (upd_ctx (set_brk BrkDead) st)) with (apages st) by (apply apages_ext; reflexivity); exact Q2.
Qed.

#[using="P LS0 INV0 SG0 HAQ0 ROOM0 HB KN KS"] Theorem alloc_meta_fq st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> QT X st 0 ->
  c_free_meta_head (s_ctx st) = c_free_meta_head (s_ctx st0) ->
  fqtree B L (alloc_meta st k bail) Post.
Proof.
  intros INV1 AF0 LF QT1 EFH0.
  assert (EFH1 : c_free_meta_head (s_ctx (am_init st)) = c_free_meta_head (s_ctx st0)) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); exact EFH0).
  destruct (INVL_am_init X st L BL LS INV1) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. pose proof (QT_am_init X st 0 QT1) as QT0. clear AF0 AFi INV1 QT1.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). pose proof QT0 as (Q & NC & GB & GEO).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV2.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
    destruct (am_reuse_q X s L BL LS m rest 0 INV ELS Q) as (Q2 & NC2 & RG2 & AP2 & DD).
    assert (AF2 : AM_frame st0 (dequeue LFree m s)).
    { eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
      all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
                destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
      all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
      all: try (intros rid r H _; rewrite F1; exact H).
      all: rewrite ?F3; lia. }
    assert (GEO2 : forall x, (exists b, hosts st0 b x) -> geom (MR (dequeue LFree m s) x) = geom (MR st0 x)).
    { intros x Hx. rewrite <- (GEO x Hx). apply geom_data. apply DD. }
    eapply KS; [exact INV2| | exact AF2| exact LF| | | | | exact GEO2].
    - intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity.
    - apply SINV_split. split; [exact (SG_of _ AF2 GEO2)| exact Q2].
    - apply (AQ_frame st0 _ BL P (amf_groups _ _ AF2) GEO2); [rewrite NC2, NC; exact (aq_carved _ _ _ HAQ0)| exact HAQ0].
    - rewrite NC2, NC. lia.
    - intros c. exact (gcnt_frame st0 _ c (amf_groups _ _ AF2) GEO2). }
  (* [comment removed for export] *)
  assert (ROOM : ncarved st0 + 1 <= NCAP P) by (apply ROOM0; rewrite <- EFH1; unfold ctx in EFH; exact EFH).
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_fq; [exact ROOM| exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia| exact QT0]. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_fq; [exact ROOM| exact INV| exact AF| exact LF| exact HI| exact QT0| unfold ctx in HAC; exact HAC]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  - (* [comment removed for export] *)
    destruct IBK as [BP NB].
    assert (BR0 : ld_brkreg L = None).
    { destruct (ld_brkreg L) as [[b l]|] eqn:E; [| reflexivity]. exfalso.
      destruct (proj1 (ir_brkreg _ _ _ IR b l) E) as (q & rq & Hq & Kq & _). exact (NB q rq Hq Kq). }
    assert (BB0 : BB L = 0) by (unfold BB; rewrite BP, BR0; reflexivity).
    pose proof (bound_of s L LS 0 (2 * PGSZ) INV QT0 ltac:(unfold PGSZ; lia)) as BND. rewrite BB0 in BND. unfold PGSZ in BND.
    apply fqtree_vis; [reflexivity| reflexivity| left; auto| | | | exact I].
    { intros cur Hc. cbn [event_post Z.eqb]. rewrite gm_set_brkph. unfold BB. cbn. rewrite BR0. lia. }
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply fqtree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| | | | exact I].
    { intros z Hz. unfold event_post. rewrite NZ. unfold L1. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph].
      destruct (z =? new); unfold BB; cbn; rewrite ?BR0; unfold gm in BND |- *; cbn in BND |- *; unfold PGSZ in *; lia. }
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply fqtree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| | | | intros HF; cbv in HF; discriminate].
        { intros z Hz. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
          unfold BB, gm in BND |- *. cbn in BND |- *. unfold PGSZ in *. lia. }
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPGuard cur) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           destruct (QM_brk_first X s L BL LS cur 0 INV EBRK HC HAC Q ltac:(lia)) as (Q3 & NC3 & AP3 & GB3 & MB3 & BP3 & MR3 & CK3 & _).
           eapply am_carve_fq; [exact ROOM| exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact CK3].
           ++ destruct LF; constructor; assumption.
           ++ split; [exact Q3|]. split; [rewrite NC3; exact NC|]. split; [rewrite GB3; exact GB|]. intros x Hx. rewrite MR3. exact (GEO x Hx).
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph BPDead (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| apply QT_brk_dead; exact QT0| cbn; exact HAC].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_fq; [exact ROOM| exact INV| exact AF| exact LF| exact HI| exact QT0| exact HAC].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    pose proof (bound_of s L LS 0 PGSZ INV QT0 ltac:(unfold PGSZ; lia)) as BND.
    apply fqtree_vis; [reflexivity| reflexivity| exact PRE| | | | exact I].
    { intros z Hz. unfold event_post. rewrite NZ, BP, BR.
      assert (BBL : BB L = off) by (unfold BB; rewrite BP, BR; reflexivity). rewrite BBL in BND.
      destruct (z =? new).
      - rewrite gm_set_brkreg. unfold BB. cbn [ld_brk ld_brkreg set_brkreg]. rewrite BP. unfold PGSZ in *. lia.
      - rewrite gm_set_brkph. unfold BB. cbn [ld_brk ld_brkreg set_brkph]. rewrite BR. unfold PGSZ in *. lia. }
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        destruct (QM_brk_grow X s L BL LS rid off 0 INV EBRK HC HAC Q ltac:(lia)) as (Q3 & NC3 & AP3 & GB3 & MB3 & BP3 & MR3 & CK3 & _).
        eapply am_carve_fq; [exact ROOM| exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact CK3].
        -- destruct LF; constructor; assumption.
        -- split; [exact Q3|]. split; [rewrite NC3; exact NC|]. split; [rewrite GB3; exact GB|]. intros x Hx. rewrite MR3. exact (GEO x Hx).
      * destruct (INVL_brk_dead X s L (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| apply QT_brk_dead; exact QT0| cbn; exact HAC].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AMQ.

End WithCeil.
End LB_WAMeta.

(* [comment removed for export] *)
Module LB_WSlot.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WTry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WTry2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WCreate2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_XferF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_WTry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_AG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition QPOST (P : Z -> Z) (idle : list aptr) (BL : list blk) (st : mstate) : Prop :=
  SG st BL /\ QM (X_as idle) st 0 /\ AQ st BL P.

#[using="Type"] Lemma QPOST_SINV P idle BL st X : x_idle X = idle -> QPOST P idle BL st -> SINV X st BL /\ AQ st BL P.
Proof. intros E (S & Q & A). split; [| exact A]. apply SINV_split. split; [exact S|]. apply (QM_X (X_as idle)); [rewrite E; reflexivity| exact Q]. Qed.

#[using="Type"] Lemma SINV_QPOST P idle BL st X : x_idle X = idle -> SINV X st BL -> AQ st BL P -> QPOST P idle BL st.
Proof. intros E S A. apply SINV_split in S as [S Q]. split; [exact S|]. split; [| exact A]. apply (QM_X X); [cbn; symmetry; exact E| exact Q]. Qed.

(* [comment removed for export] *)
Record qsame (st st1 : mstate) : Prop := mkQS {
  qs_groups : s_groups st1 = s_groups st;
  qs_slots : s_slots st1 = s_slots st;
  qs_metas : s_metas st1 = s_metas st;
  qs_regions : s_regions st1 = s_regions st;
  qs_amc : c_avail_meta_count (s_ctx st1) = c_avail_meta_count (s_ctx st);
  qs_amas : c_avail_meta_areas (s_ctx st1) = c_avail_meta_areas (s_ctx st);
  qs_shift : c_meta_alloc_shift (s_ctx st1) = c_meta_alloc_shift (s_ctx st) }.

#[using="Type"] Lemma QPOST_qsame P idle BL st st1 X L LS : INVL X st L BL LS -> qsame st st1 -> QPOST P idle BL st -> QPOST P idle BL st1.
Proof.
  intros INV [EG ES EM ER EC EA EH] (S & Q & A).
  assert (MRx : forall x, MR st1 x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR st1 x) = geom (MR st x)) by (intros x _; rewrite MRx; reflexivity).
  split; [| split].
  - apply (SG_frame st st1 BL EG ES GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?EM, ?ER, ?EC, ?EH, ?(ncarved_ext st st1 EM), ?(apages_ext st st1 ER EA); auto.
  - apply (AQ_frame st st1 BL P EG GEO); [rewrite (ncarved_ext st st1 EM); exact (aq_carved _ _ _ A)| exact A].
Qed.

#[using="Type"] Lemma qsame_step_seq st : qsame st (step_seq st).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); constructor; reflexivity. Qed.
#[using="Type"] Lemma qsame_account_bounce sc st : qsame st (account_bounce sc st).
Proof. unfold account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; constructor; reflexivity. Qed.
#[using="Type"] Lemma qsame_trans a b c : qsame a b -> qsame b c -> qsame a c.
Proof. intros [A1 A2 A3 A4 A5 A6 A7] [B1 B2 B3 B4 B5 B6 B7]; constructor; congruence. Qed.

(* [comment removed for export] *)
Definition BLF (st0 st1 : mstate) (BL : list blk) : Prop :=
  forall k, In k BL -> slotcls st1 (bslot k) = slotcls st0 (bslot k).
#[using="Type"] Lemma BLF_refl st BL : BLF st st BL.
Proof. intros k _. reflexivity. Qed.
#[using="Type"] Lemma BLF_trans a b c BL : BLF a b BL -> BLF b c BL -> BLF a c BL.
Proof. intros H1 H2 k Hk. rewrite (H2 k Hk). exact (H1 k Hk). Qed.
#[using="Type"] Lemma scl_geo X st st1 L BL LS : INVL X st L BL LS -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> forall s, slotcls st1 s = slotcls st s.
Proof.
  intros INV ES GEO s. unfold slotcls, cls. rewrite ES. destruct (s_slots st !! s) as [[m i]|] eqn:E; [| reflexivity].
  pose proof (GEO m (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ E))) as G.
  unfold geom in G. inversion G. reflexivity.
Qed.
#[using="Type"] Lemma BLF_geo X st st1 L BL LS : INVL X st L BL LS -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> BLF st st1 BL.
Proof. intros INV ES GEO k _. exact (scl_geo X st st1 L BL LS INV ES GEO (bslot k)). Qed.
#[using="Type"] Lemma BLF_qsame st st1 BL : qsame st st1 -> BLF st st1 BL.
Proof. intros [_ ES EM _ _ _ _] k _. unfold slotcls, cls, MR, get_meta_rec. rewrite ES, EM. reflexivity. Qed.
#[using="Type"] Lemma BLF_ffr X2 st1 st2 L2 BL LS2 : INVL X2 st2 L2 BL LS2 -> FFR st1 st2 -> BLF st1 st2 BL.
Proof. intros INV F k Hk. exact (x_slotcls X2 st1 st2 L2 BL LS2 INV F k Hk). Qed.
#[using="Type"] Lemma BLF_old X st0 st1 L BL LS : INVL X st0 L BL LS -> (forall s, s_slots st0 !! s <> None -> slotcls st1 s = slotcls st0 s) -> BLF st0 st1 BL.
Proof.
  intros INV H k Hk. apply H. destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) k Hk) as (x & i & Hs & _). rewrite Hs. discriminate.
Qed.
#[using="Type"] Lemma BLF_MIS st0 st1 BL c : BLF st0 st1 BL -> MIS st1 BL c = MIS st0 BL c.
Proof. intros H. unfold MIS. apply zcount_ext. intros k Hk. rewrite (H k Hk). reflexivity. Qed.
#[using="Type"] Lemma BLF_LS st0 st1 BL c : BLF st0 st1 BL -> LS st1 BL c = LS st0 BL c.
Proof. intros H. unfold LS. apply zcount_ext. intros k Hk. rewrite (H k Hk). reflexivity. Qed.
#[using="Type"] Lemma qsame_upd_ctx st f :
  (forall c, c_avail_meta_count (f c) = c_avail_meta_count c) -> (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) ->
  (forall c, c_meta_alloc_shift (f c) = c_meta_alloc_shift c) -> qsame st (upd_ctx f st).
Proof. intros H1 H2 H3. constructor; cbn; auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma free_idle_q idle m st L BL LS P : INVL (X_as (m :: idle)) st L BL LS -> ~ In m idle ->
  QPOST P (m :: idle) BL st -> QPOST P idle BL (fm_st st m).
Proof.
  intros INV NIm (S & Q & A).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (fi_metas idle m st L BL LS INV) as Hm.
  assert (PUT : put_meta m meta0 st = st) by (apply (fi_put idle m st L BL LS INV)).
  unfold fm_st. rewrite PUT.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  pose proof (queue_data LFree m st) as DD.
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR (queue_st LFree m st) x) = geom (MR st x)) by (intros x _; apply geom_data; apply DD).
  (* [comment removed for export] *)
  assert (DOM : forall x, s_metas (queue_st LFree m st) !! x <> None <-> s_metas st !! x <> None).
  { intros x. split; [| apply queue_keys_mono]. intros Hx. destruct (queue_keys LFree m st x Hx) as [H'|[->|[Hh|(a & Hh & Hpv)]]]; [exact H'| rewrite Hm; discriminate| |].
    - apply (listed_present _ _ _ _ _ INV x LFree). exact (head_listed _ _ _ _ _ INV LFree x Hh).
    - apply (listed_present _ _ _ _ _ INV x LFree). exact (prev_listed _ _ _ _ _ INV LFree a x (head_listed _ _ _ _ _ INV LFree a Hh) Hpv). }
  pose proof (ncarved_dom st (queue_st LFree m st) DOM) as NC.
  split; [| split].
  - apply (SG_frame st _ BL F5 F6 GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ IS _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. destruct FC. constructor; rewrite ?F1, ?NC; auto.
    + intros x mr Hx Z0.
      assert (Px : s_metas st !! x <> None) by (apply DOM; rewrite Hx; discriminate).
      destruct (s_metas st !! x) as [mr0|] eqn:E0; [| congruence].
      pose proof (DD x) as Dx. rewrite (MR_of_lookup _ _ _ Hx), (MR_of_lookup _ _ _ E0) in Dx. apply data_of_eq in Dx as (Em & _).
      pose proof (queue_next LFree m st x) as QN. rewrite (MR_of_lookup _ _ _ Hx) in QN.
      destruct (aptr_eq_dec x m) as [->|NE].
      * left. rewrite QN. cbn [get_head]. destruct (c_free_meta_head (ctx st)) as [a|] eqn:HH.
        -- destruct (aptr_eqb_spec m a) as [->|NEa].
           { exfalso. apply (proj2 (im_idle _ _ _ IM a ltac:(left; reflexivity))). exists LFree. exact (head_listed _ _ _ _ _ INV LFree a HH). }
           destruct (optr_eqb _ _); [discriminate|]. rewrite aptr_eqb_refl. discriminate.
        -- rewrite aptr_eqb_refl. discriminate.
      * destruct (Q1 x mr0 E0 ltac:(congruence)) as [N0|I0].
        -- left. rewrite QN. cbn [get_head]. destruct (c_free_meta_head (ctx st)) as [a|].
           ++ destruct (aptr_eqb_spec x a) as [->|NEa].
              ** destruct (optr_eqb _ _); [discriminate|]. destruct (aptr_eqb_spec a m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
              ** destruct (optr_eqb _ _); [discriminate|]. destruct (aptr_eqb_spec x m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
           ++ destruct (aptr_eqb_spec x m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
        -- destruct I0 as [->|I1]; [congruence| right; exact I1].
    + rewrite (apages_ext st (queue_st LFree m st) F1 cb_amas), cb_amc. exact Q2.
    + rewrite cb_shift. exact Q4.
    + rewrite cb_shift. exact Q6.
  - apply (AQ_frame st _ BL P F5 GEO); [rewrite NC; exact (aq_carved _ _ _ A)| exact A].
Qed.

#[using="Type"] Lemma BLF_free_idle idle m st L BL LS : INVL (X_as (m :: idle)) st L BL LS -> BLF st (fm_st st m) BL.
Proof.
  intros INV. apply (BLF_geo _ st _ L BL LS INV).
  - unfold fm_st. rewrite (fi_put idle m st L BL LS INV). destruct (queue_frame LFree m st) as (_ & _ & _ & _ & _ & F6 & _). exact F6.
  - intros x _. apply geom_data. unfold fm_st. rewrite (fi_put idle m st L BL LS INV). apply queue_data.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma state_bytes_B X st L BL LS P B : INVL X st L BL LS -> x_pend X = None -> x_orph X = None ->
  SINV X st BL -> AQ st BL P -> PHI P + R63 BL <= B + 3 * PGSZ -> gm L + BB L <= B.
Proof.
  intros INV HP HO SI HAQ HB. pose proof (ledger_bound X st L BL LS INV) as L1. pose proof (regions_bound X st L BL LS P INV SI HAQ HP) as R1.
  unfold ORPH in R1. rewrite HO in R1. unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma group_bytes_B X st L BL LS P B : INVL X st L BL LS -> x_pend X = None -> x_orph X = None ->
  SINV X st BL -> AQ st BL P -> PHI P + R63 BL <= B + 3 * PGSZ -> group_bytes st + PGSZ * (5 * NCAP P / 101 + 8) <= B.
Proof.
  intros INV HP HO SI HAQ HB. pose proof (group_bytes_bound X st L BL LS P INV SI HAQ HP) as R1.
  unfold ORPH in R1. rewrite HO in R1. unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Definition AGK (T : Type) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) (idle : list aptr) (sc req : Z) (st0 : mstate) (L0 : mled) (BL : list blk)
  (k : mstate -> optr -> M T) : Prop :=
  forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> QPOST P idle BL st2 ->
  (forall c, 0 <= c < sc -> gcnt st2 c <= gcnt st0 c) -> BLF st0 st2 BL -> fqtree B L2 (k st2 go) Post.

(* [comment removed for export] *)
#[using="Type"] Lemma QPOST_new_group_region P idle BL st X L LS a len :
  INVL X st L BL LS -> QPOST P idle BL st -> QPOST P idle BL (fst (new_region RKGroup a len st)).
Proof.
  intros INV (S & Q & A). pose proof (nm_fresh _ _ _ _ _ INV) as FR.
  set (st2 := fst (new_region RKGroup a len st)).
  assert (MRx : forall x, MR st2 x = MR st x) by (intros; reflexivity).
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR st2 x) = geom (MR st x)) by (intros; reflexivity).
  assert (RG : s_regions st2 = <[s_next_rid st := mkRegion RKGroup a len]> (s_regions st)) by reflexivity.
  assert (AP : apages st2 = apages st).
  { rewrite !apages_msum, RG, (msum_insert _ _ _ _ FR). unfold apF at 1. cbn [fst snd is_metakind_b r_kind]. rewrite Z.add_0_l.
    apply msum_ext. intros q rq Hq. unfold apF, frontier. cbn. reflexivity. }
  split; [| split].
  - apply (SG_frame st st2 BL eq_refl eq_refl GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; try exact Q1; rewrite ?RG, ?AP; change (ncarved st2) with (ncarved st); change (s_ctx st2) with (s_ctx st); auto.
    + intros q rq Hq K. destruct (N.eq_dec q (s_next_rid st)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; cbn in K; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. exact (Q3 q rq Hq K).
    + intros q rq Hq K. destruct (N.eq_dec q (s_next_rid st)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; cbn in K; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. exact (Q4 q rq Hq K).
    + intros q1 q2 r1 r2 H1 H2 K1 K2 NE.
      destruct (N.eq_dec q1 (s_next_rid st)) as [->|NE1]; [rewrite lookup_insert_eq in H1; inversion H1; subst; cbn in K1; discriminate|].
      destruct (N.eq_dec q2 (s_next_rid st)) as [->|NE2]; [rewrite lookup_insert_eq in H2; inversion H2; subst; cbn in K2; discriminate|].
      rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (Q5 _ _ _ _ H1 H2 K1 K2 NE).
  - apply (AQ_frame st st2 BL P eq_refl GEO); [change (ncarved st2) with (ncarved st); exact (aq_carved _ _ _ A)| exact A].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP_BRANCHQ.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr) (P : Z -> Z) (B : Z).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis QP1 : QPOST P (m :: idle) BL st1.
Hypothesis STD : cnt = cmax sc -> needed = std_len sc /\ std_nested sc = false.
Hypothesis NSTD : cnt <> cmax sc -> gcnt st1 sc < 128.
Hypothesis NUB : needed <= UNIT * size_class sc * cnt + 4111.
Hypothesis GLE1 : forall c, gcnt st1 c = gcnt st0 c.
Hypothesis BF1 : BLF st0 st1 BL.
Hypothesis HBP : PHI P + R63 BL <= B + 3 * PGSZ.
Hypothesis HK : AGK T P B Post idle sc req st0 L0 BL k.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

#[using="CE L1 LS1 INV1 QP1"] Lemma QP1' : QPOST P (m :: idle) BL st1'.
Proof. apply (QPOST_qsame P (m :: idle) BL st1 st1' _ L1 LS1 INV1); [| exact QP1]. eapply qsame_trans; [apply qsame_account_bounce| apply qsame_step_seq]. Qed.

(* [comment removed for export] *)
#[using="INV1 NIm TF1 Hsc HA1 HA0 GRP QP1 STD NSTD NUB BF1 st1'"] Lemma mmap_final a :
  let st1f := step_seq (account_bounce sc st1) in
  mmap_answer_ok (live_ranges st1f) needed a = true -> is_err a = false ->
  let st2 := fst (new_region RKGroup a needed st1f) in let rid := s_next_rid st1f in
  let stf := agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI in
  let mr' := agG sc (rid, 0) cnt AI (m_set_maplen (Z.shiftr needed 12) meta0) in
  INVL (mkX idle [] None None (Some m)) stf (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1
  /\ TF0 stf /\ MR stf m = mr' /\ s_groups stf !! (rid, 0) = Some (mkGhdr (Some m) AI)
  /\ (forall sc0, active stf sc0 = active st0 sc0) /\ QPOST P idle BL stf
  /\ s_regions stf = s_regions st2 /\ s_secret st2 = s_secret st1 /\ (forall c, gcnt stf c = (if sc =? c then cnt else 0) + gcnt st1 c)
  /\ BLF st0 stf BL.
Proof.
  cbn zeta. intros Ha ER.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1'). fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1' |- *.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  set (st2 := fst (new_region RKGroup a needed st1')). set (rid := s_next_rid st1').
  pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
  fold rid st2 in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
  assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)) by (unfold st2; rewrite ng_lookup; fold rid; rewrite N.eqb_refl; reflexivity).
  assert (NS : s_shadow st2 !! rid = None) by (unfold st2, rid; change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'); exact (shadow_next_rid_none _ _ _ _ _ INV1')).
  assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; unfold st2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
  assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
  assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [reflexivity| reflexivity| exact TF1']).
  pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
  assert (HAI0 : sc = 0 -> AI = cnt - 1).
  { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
    replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (ag_top_ok idle st2 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
              INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
  change (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) in *.
  split; [exact INV'|]. split; [exact TF'|]. split; [exact MR'|]. split; [exact GR'|]. split; [intros sc0; rewrite ACT'; apply ACT2|].
  enough (QG : QPOST P idle BL (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI)
              /\ (forall c, gcnt (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) c = (if sc =? c then cnt else 0) + gcnt st1 c)
              /\ BLF st0 (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) BL).
  { destruct QG as (QG1 & QG2 & QG3). split; [exact QG1|]. split; [rewrite agt_regions; reflexivity|]. split; [exact SS1'|]. split; [exact QG2| exact QG3]. }
  (* [comment removed for export] *)
  pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
  destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  destruct (QPOST_new_group_region P (m :: idle) BL st1' _ L1 LS1 a needed INV1' QP1') as (SG2 & Q2 & A2). fold st2 in SG2, Q2, A2.
  pose proof INV2 as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2).
  assert (FR : s_regions st1' !! rid = None) by (unfold rid; exact (nm_fresh _ _ _ _ _ INV1')).
  assert (HpN : s_groups st2 !! (rid, 0) = None).
  { destruct (s_groups st2 !! (rid, 0)) as [h|] eqn:E; [| reflexivity]. exfalso.
    change (s_groups st2) with (s_groups st1') in E. destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1'))))) _ _ E) as (r & Hr' & _). cbn in Hr'. rewrite FR in Hr'. discriminate. }
  assert (HsN : s_slots st2 !! (rid, 0) = None).
  { destruct (s_slots st2 !! (rid, 0)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
    change (s_slots st2) with (s_slots st1') in E. destruct (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1')))))) _ _ _ E) as ([b [aix Hb]] & _ & Es).
    destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1'))))) _ _ Hb) as (r & Hr' & _).
    pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV1'))) _ _ (ex_intro _ aix Hb)) as MM.
    unfold slot_start', gbase in Es. rewrite MM in Es. cbn in Es. assert (E1 : fst b = rid) by (inversion Es; reflexivity). rewrite E1, FR in Hr'. discriminate. }
  assert (NEEDED : Z.shiftr needed 12 * 4096 = needed) by (rewrite F10; apply round_up_pg_id; exact G2).
  assert (STRIDE : get_stride (agG sc (rid, 0) cnt AI (m_set_maplen (Z.shiftr needed 12) meta0)) = if (cnt - 1 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
  { rewrite Emr. unfold get_stride. cbn -[Z.shiftr Z.mul Z.sub Z.eqb size_class]. replace (Z.shiftr needed 12 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_true_r. reflexivity. }
  pose proof (tab_basic_ok sc Hsc) as (_ & CM & _).
  set (stA := upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) in *.
  assert (LKm : forall x, x <> m -> s_metas stA !! x = s_metas st2 !! x) by (intros x NE; unfold stA; rewrite s_metas_upd_meta, lookup_insert_ne by congruence; reflexivity).
  assert (LKc : c_avail_meta_count (s_ctx stA) = c_avail_meta_count (s_ctx st2) /\ c_avail_meta_areas (s_ctx stA) = c_avail_meta_areas (s_ctx st2)
                /\ c_meta_alloc_shift (s_ctx stA) = c_meta_alloc_shift (s_ctx st2)) by (repeat split; reflexivity).
  assert (HmA : s_metas stA !! m <> None) by (unfold stA; rewrite s_metas_upd_meta, lookup_insert_eq; discriminate).
  assert (HmI : s_metas st2 !! m = Some meta0) by exact (proj1 (im_idle _ _ _ IM2 m ltac:(left; reflexivity))).
  assert (ROOM : gcnt st2 sc <= CAP P sc) by (apply (creation_room _ st2 _ BL LS1 P INV2 SG2 A2 sc Hsc eq_refl); rewrite ACT2; exact HA0).
  assert (NEWG : m_sizeclass (MR (agt stA sc m (rid, 0) cnt AI) m) = sc /\ m_last_idx (MR (agt stA sc m (rid, 0) cnt AI) m) = cnt - 1) by (rewrite MR', Emr; split; reflexivity).
  assert (QGm : m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots st2 !! (rid, 0) = None).
  { rewrite MR', Emr. cbn [m_maplen]. intros _. split; [| exact HsN]. unfold S_. rewrite NEEDED. lia. }
  assert (QGn : m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) = 0 -> exists g i, s_slots st2 !! (rid, 0) = Some (g, i) /\ m_sizeclass (MR st2 g) <= 23
                /\ (stdg (agt stA sc m (rid, 0) cnt AI) m = true -> m_sizeclass (MR st2 g) = bighost sc)).
  { rewrite MR', Emr. cbn [m_maplen]. intros Z0. exfalso. lia. }
  assert (QGo : cnt = 1 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 ->
                m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 <= S_ sc + UNIT \/ (34 <= sc /\ m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 <= round_up_pg (S_ sc + UNIT))).
  { rewrite MR', Emr. cbn [m_maplen]. intros C1 _. rewrite NEEDED. unfold S_. exact (grp_ok_one sc cnt needed GRP C1). }
  assert (SDc : stdg (agt stA sc m (rid, 0) cnt AI) m = true -> cnt = cmax sc).
  { unfold stdg, cls, cnt_of. rewrite MR', Emr. cbn -[Z.eqb Z.shiftr Z.mul Z.sub Z.add get_stride cmax S_ size_class agG m_set_maplen meta0].
    intros SD. apply andb_prop in SD as [SD1 _]. apply Z.eqb_eq in SD1. cbn in SD1. clear -SD1. lia. }
  assert (QGs : stdg (agt stA sc m (rid, 0) cnt AI) m = true -> (m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) = 0 <-> std_nested sc = true)
                /\ (m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 = std_len sc)).
  { intros SD. destruct (STD (SDc SD)) as [EN SNF]. rewrite MR', Emr. cbn [m_maplen].
    split; [rewrite SNF; split; [intros; exfalso; lia| discriminate]| intros _; rewrite NEEDED; exact EN]. }
  assert (MS1 : s_metas st1' = s_metas st1 /\ s_groups st1' = s_groups st1).
  { unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); split; reflexivity. }
  assert (MS12 : s_metas st2 = s_metas st1 /\ s_groups st2 = s_groups st1) by exact MS1.
  assert (G12c : forall c, gcnt st2 c = gcnt st1 c).
  { intros c. destruct MS12 as [MS GS]. apply gcnt_frame; [exact GS|]. intros x _. unfold MR, get_meta_rec. rewrite MS. reflexivity. }
  pose proof (G12c sc) as G12.
  assert (QGsm : stdg (agt stA sc m (rid, 0) cnt AI) m = false -> gcnt st2 sc < 128).
  { intros SD. rewrite G12. apply NSTD. intros EC.
    unfold stdg, cls, cnt_of in SD. rewrite MR', Emr in SD. cbn -[Z.eqb Z.shiftr Z.mul Z.sub Z.add get_stride cmax S_ size_class agG m_set_maplen meta0] in SD.
    rewrite <- Emr, STRIDE in SD. replace (cnt - 1 =? 0) with false in SD by (symmetry; apply Z.eqb_neq; clear -EC CM; lia).
    replace (cnt - 1 + 1 =? cmax sc) with true in SD by (symmetry; apply Z.eqb_eq; clear -EC; lia). unfold S_ in SD. rewrite Z.eqb_refl in SD. discriminate. }
  destruct (agt_quant (xorph (X_as (m :: idle)) (Some rid)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS1 LS1 P sc m (rid, 0) cnt AI
              INV2 INV' eq_refl eq_refl LKm LKc HmA HmI HpN SG2 (QM_X (X_as (m :: idle)) (xorph (X_as (m :: idle)) (Some rid)) st2 0 eq_refl Q2) ltac:(intros x Hx; cbn in Hx |- *; destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx| right; exact Hx]) A2 Hsc ROOM ltac:(lia) NEWG QGm QGo QGn QGs QGsm)
    as (Qa & Qb & Qc).
  split; [split; [exact Qa|]; split; [exact (QM_X (mkX idle [] None None (Some m)) (X_as idle) _ 0 eq_refl Qb)| exact Qc]|].
  split.
  { intros c. rewrite (aq_gcnt (xorph (X_as (m :: idle)) (Some rid)) st2 stA _ BL LS1 sc m (rid, 0) cnt AI INV2 eq_refl LKm HmI HpN NEWG c).
    rewrite <- (G12c c). reflexivity. }
  (* [comment removed for export] *)
  eapply BLF_trans; [exact BF1|].
  assert (B12 : BLF st1 st2 BL).
  { intros kk _. unfold slotcls, cls, MR, get_meta_rec. rewrite (proj1 MS12). replace (s_slots st2) with (s_slots st1); [reflexivity|].
    unfold st2. change (s_slots (fst (new_region RKGroup a needed st1'))) with (s_slots st1').
    unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity. }
  eapply BLF_trans; [exact B12|].
  apply (BLF_old _ st2 _ _ BL LS1 INV2).
  exact (aq_slotcls_old (xorph (X_as (m :: idle)) (Some rid)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS1 LS1 sc m (rid, 0) cnt AI
           INV2 INV' eq_refl LKm HmI HpN NEWG QGm QGo QGn QGs QGsm).
Qed.

#[using="idle st0 L0 BL LS1 P req INV1 NIm TF1 Hsc Hfit HA1 HA0 HL1 HG1 GRP RED QP1 STD NSTD NUB GLE1 BF1 HBP HK"] Theorem ag_mmap_fq :
  fqtree B L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1'). fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1'.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof QP1' as QP. destruct (QPOST_SINV P (m :: idle) BL st1' (X_as (m :: idle)) eq_refl QP) as [SI1' A1'].
  assert (MS1 : s_metas st1' = s_metas st1 /\ s_groups st1' = s_groups st1).
  { unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); split; reflexivity. }
  apply fqtree_vis; [reflexivity| reflexivity| | | | | intros _; rewrite (mmap_len_of_aligned needed) by lia; unfold QMAX; lia].
  - (* [comment removed for export] *) cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - (* [comment removed for export] *)
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha.
    destruct (is_err a) eqn:ER.
    + exact (state_bytes_B (X_as (m :: idle)) st1' L1 BL LS1 P B INV1' eq_refl eq_refl SI1' A1' HBP).
    + destruct (mmap_final a Ha ER) as (INVf & _ & _ & _ & _ & QPf & _ & _ & _).
      destruct (QPOST_SINV P idle BL _ (mkX idle [] None None (Some m)) eq_refl QPf) as [SIf Af].
      exact (state_bytes_B _ _ _ BL LS1 P B INVf eq_refl eq_refl SIf Af HBP).
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + (* [comment removed for export] *)
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK.
      * split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
          unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
        split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
      * exact (free_idle_q idle m st1' L1 BL LS1 P INV1' NIm QP).
      * intros c Hc. rewrite <- GLE1. apply Z.eq_le_incl. apply gcnt_frame; [rewrite F3; exact (proj2 MS1)|].
        intros x _. transitivity (geom (MR st1' x)); [| unfold MR, get_meta_rec; rewrite (proj1 MS1); reflexivity].
        apply geom_data. unfold fm_st. rewrite (fi_put idle m st1' L1 BL LS1 INV1'). apply queue_data.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [| exact (BLF_free_idle idle m st1' L1 BL LS1 INV1')].
        apply BLF_qsame. eapply qsame_trans; [apply qsame_account_bounce| apply qsame_step_seq].
    + (* [comment removed for export] *)
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      destruct (mmap_final a Ha ER) as (INV' & TF' & MR' & GR' & ACT' & QPf & RGf & SSf & GCf & BFf). rewrite <- Est2, <- Erid in *.
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK; [| exact QPf| intros c Hc; rewrite GCf, <- GLE1; destruct (Z.eqb_spec sc c); lia| exact BFf].
      split; [intros sc' _; apply ACT'|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite RGf, Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - transitivity (s_secret st2); [rewrite agt_secret; reflexivity|]. rewrite SSf. reflexivity. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F10; apply round_up_pg_id; exact G2).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|C1]; [| lia]. rewrite E12. assert (C1' : cnt = 1) by lia. rewrite C1', Z.mul_1_r in NR. unfold UNIT, IB in *. lia.
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCHQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REC_OKQ (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  QPOST P idle BL st -> zlen idle <= rank j -> PHI P + R63 BL <= B + 3 * PGSZ ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> QPOST P idle BL st1 ->
     (forall c, 0 <= c < j -> gcnt st1 c <= gcnt st c) -> BLF st st1 BL -> fqtree B L1 (k st1 idx) Post) ->
  fqtree B L (rec st j req k bail) Post.

Section NEST_BRANCHQ.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr) (P : Z -> Z) (B : Z).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKQ T rec sc P B Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis QP1 : QPOST P (m :: idle) BL st1.
Hypothesis NSTD : cnt <> cmax sc -> gcnt st1 sc < 128.
Hypothesis GLE1 : forall c, gcnt st1 c = gcnt st0 c.
Hypothesis BF1 : BLF st0 st1 BL.
Hypothesis RK : zlen idle + 1 <= rank (size_to_class (UNIT + cnt * (UNIT * size_class sc) - IB)).
Hypothesis HBP : PHI P + R63 BL <= B + 3 * PGSZ.
Hypothesis HK : AGK T P B Post idle sc req st0 L0 BL k.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

#[using="idle st0 L0 BL LS1 P req REC INV1 NIm ND TF1 Hsc Hfit HA1 HA0 HL1 HG1 NEST QP1 NSTD GLE1 BF1 RK HBP HK"] Theorem ag_nest_fq :
  fqtree B L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons_2; [intros Hin; apply NIm; apply (proj1 (list_elem_of_In _ _)); exact Hin| exact ND].
  - exact N5.
  - lia.
  - exact QP1.
  - rewrite zlen_cons. fold size in RK. fold j in RK. lia.
  - exact HBP.
  - intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES) QP2 GLE2 BF2.
    destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    + (* [comment removed for export] *)
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK.
      * split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
          unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
        split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
      * exact (free_idle_q idle m st2 L2 BL LS2 P INV2 NIm QP2).
      * intros c Hc. rewrite <- GLE1. etransitivity; [| apply (GLE2 c); lia]. apply Z.eq_le_incl. apply gcnt_frame; [exact F3|].
        intros x _. apply geom_data. unfold fm_st. rewrite (fi_put idle m st2 L2 BL LS2 INV2). apply queue_data.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2| exact (BLF_free_idle idle m st2 L2 BL LS2 INV2)].
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      (* [comment removed for export] *)
      set (p := (fst bg, sstart (MR st2 g) idx)) in *.
      set (stA := upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) in *.
      pose proof (strip_nest_layout st2 g idx j size cnt) as SN.
      assert (LKg : s_groups stA = s_groups st2) by (unfold stA; rewrite s_groups_upd_meta || cbn; transitivity (s_groups (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (LKr : s_regions stA = s_regions st2) by (unfold stA; transitivity (s_regions (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (MSn : s_metas (nest_layout st2 g idx j size cnt) = s_metas st2) by (transitivity (s_metas (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (CXn : s_ctx (nest_layout st2 g idx j size cnt) = s_ctx st2) by (transitivity (s_ctx (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (LKm : forall x, x <> m -> s_metas stA !! x = s_metas st2 !! x) by (intros x NE; unfold stA; rewrite s_metas_upd_meta, lookup_insert_ne by congruence; exact (f_equal (fun t => t !! x) MSn) || (rewrite MSn; reflexivity)).
      assert (LKc : c_avail_meta_count (s_ctx stA) = c_avail_meta_count (s_ctx st2) /\ c_avail_meta_areas (s_ctx stA) = c_avail_meta_areas (s_ctx st2)
                    /\ c_meta_alloc_shift (s_ctx stA) = c_meta_alloc_shift (s_ctx st2)) by (unfold stA; rewrite s_ctx_upd_meta || cbn -[nest_layout]; rewrite CXn; repeat split; reflexivity).
      assert (HmA : s_metas stA !! m <> None) by (unfold stA; rewrite s_metas_upd_meta, lookup_insert_eq; discriminate).
      pose proof INV2 as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2).
      assert (HmI : s_metas st2 !! m = Some meta0) by exact (proj1 (im_idle _ _ _ IM2 m ltac:(left; reflexivity))).
      assert (Ep' : p = slot_start' (MR st2 g) idx) by (unfold p; symmetry; exact (slot_start'_eq _ _ _ IM2 _ _ idx Hgh)).
      assert (HpN : s_groups st2 !! p = None).
      { pose proof (is_part _ _ _ IS2 bg g aig idx Hg Hidx) as P5. cbn zeta in P5. rewrite <- Ep' in P5.
        destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDE).
        destruct (s_groups st2 !! p) as [h|] eqn:E; [| reflexivity]. exfalso. apply NDE. split; [rewrite E; discriminate| reflexivity]. }
      assert (HsP : s_slots st2 !! p = Some (g, idx)) by (rewrite Ep'; exact (is_total _ _ _ IS2 bg g idx Hgh Hidx)).
      destruct QP2 as (SG2 & Q2 & A2).
      assert (ROOM : gcnt st2 sc <= CAP P sc) by (apply (creation_room _ st2 _ BL LS2 P INV2 SG2 A2 sc Hsc eq_refl); rewrite ACT by lia; rewrite HA1; exact HA0).
      assert (NEWG : m_sizeclass (MR (agt stA sc m p cnt (cnt - 1)) m) = sc /\ m_last_idx (MR (agt stA sc m p cnt (cnt - 1)) m) = cnt - 1) by (rewrite MR'; split; reflexivity).
      assert (SDc : stdg (agt stA sc m p cnt (cnt - 1)) m = (cnt =? cmax sc)).
      { unfold stdg, cls, cnt_of. rewrite MR'. cbn -[Z.eqb Z.mul Z.sub Z.add get_stride cmax S_ size_class]. rewrite Es. unfold size, S_. rewrite Z.eqb_refl, andb_true_r.
        replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
      assert (BH : cnt = cmax sc -> std_nested sc = true /\ bighost sc = j).
      { intros EC. assert (SN2 : std_nested sc = true).
        { unfold std_nested, std_span, S_. apply Z.leb_le. rewrite <- EC. fold size.
          unfold UNIT, IB, PGSZ in N6 |- *. clear -N6. lia. }
        split; [exact SN2|]. unfold bighost. rewrite SN2. unfold std_span, S_, j. rewrite <- EC. fold size. f_equal. unfold UNIT. lia. }
      assert (QGm : m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots st2 !! p = None).
      { rewrite MR'. cbn [m_maplen]. intros Z0. exfalso. exact (Z0 eq_refl). }
      assert (QGo : cnt = 1 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 ->
                    m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 <= S_ sc + UNIT \/ (34 <= sc /\ m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 <= round_up_pg (S_ sc + UNIT))).
      { rewrite MR'. cbn [m_maplen]. intros _ Z0. exfalso. exact (Z0 eq_refl). }
      assert (QGn : m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) = 0 -> exists g0 i0, s_slots st2 !! p = Some (g0, i0) /\ m_sizeclass (MR st2 g0) <= 23
                    /\ (stdg (agt stA sc m p cnt (cnt - 1)) m = true -> m_sizeclass (MR st2 g0) = bighost sc)).
      { intros _. exists g, idx. split; [exact HsP|]. rewrite SCg. split; [lia|]. rewrite SDc. intros EC. apply Z.eqb_eq in EC. destruct (BH EC) as [_ E]. symmetry. exact E. }
      assert (QGs : stdg (agt stA sc m p cnt (cnt - 1)) m = true -> (m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) = 0 <-> std_nested sc = true)
                    /\ (m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 = std_len sc)).
      { rewrite SDc. intros EC. apply Z.eqb_eq in EC. destruct (BH EC) as [SN2 _]. rewrite MR'. cbn [m_maplen]. rewrite SN2. split; [split; intros; reflexivity| intros Z0; exfalso; exact (Z0 eq_refl)]. }
      assert (QGsm : stdg (agt stA sc m p cnt (cnt - 1)) m = false -> gcnt st2 sc < 128).
      { rewrite SDc. intros EC. apply Z.eqb_neq in EC. pose proof (GLE2 sc ltac:(lia)). pose proof (NSTD EC). lia. }
      destruct (agt_quant (xpend (X_as (m :: idle)) (Some p)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS2 LS2 P sc m p cnt (cnt - 1)
                  INV2 INV' LKg LKr LKm LKc HmA HmI HpN SG2 (QM_X (X_as (m :: idle)) (xpend (X_as (m :: idle)) (Some p)) st2 0 eq_refl Q2)
                  ltac:(intros x Hx; cbn in Hx |- *; destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx| right; exact Hx]) A2 Hsc ROOM ltac:(lia) NEWG QGm QGo QGn QGs QGsm)
        as (Qa & Qb & Qc).
      eapply HK.
      * split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
          - rewrite agt_regions. exact LKr.
          - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
            rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), SN. reflexivity. }
        exists p, (cnt - 1), (cnt - 1), 0.
        rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
        rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
        split; [exact INV'| exact TF'].
      * split; [exact Qa|]. split; [exact (QM_X (mkX idle [] None None (Some m)) (X_as idle) _ 0 eq_refl Qb)| exact Qc].
      * intros c Hc. rewrite (aq_gcnt (xpend (X_as (m :: idle)) (Some p)) st2 stA _ BL LS2 sc m p cnt (cnt - 1) INV2 LKg LKm HmI HpN NEWG c).
        replace (sc =? c) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- GLE1. pose proof (GLE2 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2|].
        apply (BLF_old _ st2 _ _ BL LS2 INV2).
        exact (aq_slotcls_old (xpend (X_as (m :: idle)) (Some p)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS2 LS2 sc m p cnt (cnt - 1)
                 INV2 INV' LKg LKm HmI HpN NEWG QGm QGo QGn QGs QGsm).
Qed.
End NEST_BRANCHQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ag_cnt1_ge128 sc u0 : 0 <= sc < 48 -> 128 <= u0 -> ag_cnt1 sc u0 = cmax sc.
Proof.
  intros Hsc Hu. unfold ag_cnt1. rewrite (cnt0_of_ge128 sc u0 Hsc Hu). pose proof (tab_basic_ok sc Hsc) as (_ & CM & _).
  replace (cmax sc =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

#[using="Type"] Lemma ag_cnt1_nstd sc u0 : 0 <= sc < 48 -> ag_cnt1 sc u0 <> cmax sc -> u0 < 128.
Proof. intros Hsc H. destruct (Z.lt_ge_cases u0 128) as [L|G]; [exact L|]. exfalso. apply H. apply ag_cnt1_ge128; assumption. Qed.

Definition cnt0_range_f (sc : Z) : bool := forallb (fun c => (1 <=? c) && (c <=? 32)) (cnt0_list sc).
#[using="Type"] Lemma cnt0_range_all : forallb cnt0_range_f classes = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma cnt0_range sc c : 0 <= sc < 48 -> In c (cnt0_list sc) -> 1 <= c <= 32.
Proof.
  intros Hsc Hc. pose proof (forallb_classes _ cnt0_range_all sc Hsc) as T. unfold cnt0_range_f in T. rewrite forallb_forall in T.
  specialize (T c Hc). apply andb_prop in T as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
#[using="Type"] Lemma ag_cnt1_range sc u0 : 0 <= sc < 48 -> 1 <= ag_cnt1 sc u0 <= 32.
Proof.
  intros Hsc. unfold ag_cnt1. pose proof (cnt0_range sc _ Hsc (cnt0_in sc u0)) as R.
  destruct (_ && _) eqn:E; [apply andb_prop in E as [E _]; apply Z.eqb_eq in E; lia| exact R].
Qed.

#[using="Type"] Lemma ag_cnt_facts sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc -> u0 <= u1 ->
  PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u0 + UNIT ->
  ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
  (c3 = cmax sc -> n3 = std_len sc /\ std_nested sc = false) /\ (c3 <> cmax sc -> u0 < 128) /\ n3 <= UNIT * size_class sc * c3 + 4111.
Proof.
  intros Hsc Hreq Hfit HU HB E. pose proof (tab_basic_ok sc Hsc) as (S16 & CM & _).
  set (c1 := ag_cnt1 sc u0) in *.
  assert (C2 : ag_cnt2 sc c1 u1 ns = c1 \/ (ag_cnt2 sc c1 u1 ns <= 5 /\ u1 < 4 * c1)).
  { unfold ag_cnt2. destruct (Z.ltb_spec u1 (4 * c1)); cbn [andb]; [| left; reflexivity]. destruct ns; cbn; [left; reflexivity|].
    destruct (adj_small sc (UNIT * size_class sc) c1) as [E1|LE]; [left; exact E1| right; split; [exact LE| assumption]]. }
  set (c2 := ag_cnt2 sc c1 u1 ns) in *.
  assert (C1R : c1 = cmax sc \/ u0 < 128) by (destruct (Z.eq_dec c1 (cmax sc)); [left; assumption| right; apply (ag_cnt1_nstd sc u0 Hsc); assumption]).
  assert (C1B : 1 <= c1 <= 32) by (unfold c1; apply ag_cnt1_range; exact Hsc).
  unfold ag_cn3 in E. cbn zeta in E.
  assert (RU : forall x, x <= round_up_pg x <= x + 4095) by (intros x; pose proof (round_up_pg_spec x); lia).
  destruct (negb ns && (c2 <=? 7)) eqn:E7.
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst c3 n3. split; [intros E1; exfalso; lia|]. split.
      * intros _. apply andb_prop in E7 as [_ E7]. apply Z.leb_le in E7. destruct C2 as [E2|[LE LT]]; [| lia]. destruct C1R as [E1|L]; [| exact L]. exfalso. unfold c2 in E7. lia.
      * pose proof (RU (req + IB + UNIT)). unfold IB, UNIT in *. lia.
    + inversion E; subst c3 n3. apply andb_prop in E7 as [_ E7]. apply Z.leb_le in E7. split; [intros E1; exfalso; lia|]. split.
      * intros _. destruct C2 as [E2|[LE LT]]; [| lia]. destruct C1R as [E1|L]; [| exact L]. exfalso. unfold c2 in E7. lia.
      * pose proof (RU (UNIT * size_class sc * c2 + UNIT)). unfold UNIT in *. lia.
  - inversion E; subst c3 n3. split; [| split].
    + intros E2. assert (E1 : c1 = cmax sc) by (destruct C2 as [E0|[LE LT]]; lia).
      split; [unfold std_len, std_span, S_; rewrite E2; f_equal; lia|].
      unfold std_nested, std_span, S_. apply Z.leb_gt. rewrite <- E1. unfold c1 in HB |- *. lia.
    + intros NE. destruct C2 as [E0|[LE LT]]; [destruct C1R as [E1|L]; [exfalso; apply NE; lia| exact L]| lia].
    + pose proof (RU (UNIT * size_class sc * c2 + UNIT)). unfold UNIT in *. lia.
Qed.

#[using="Type"] Lemma gcnt_nonneg X st L BL LS c : INVL X st L BL LS -> 0 <= gcnt st c.
Proof.
  intros INV. rewrite gcnt_gmetas. apply zsum_map_nonneg. intros [m b] Hin. cbn. destruct (gfacts X st L BL LS INV m b Hin) as ([? ?] & _).
  destruct (_ =? _); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AGQ.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKQ T rec sc P B Post.

#[using="REC"] Theorem alloc_group_fq idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None -> QPOST P idle BL st -> zlen idle <= rank sc -> PHI P + R63 BL <= B + 3 * PGSZ ->
  AGK T P B Post idle sc req st L BL k ->
  fqtree B L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA QP RK HBP HK. pose proof QP as (SGst & Qst & Ast). unfold alloc_group.
  destruct (QPOST_SINV P idle BL st (X_as idle) eq_refl QP) as [SIst _].
  pose proof (rank_range sc) as RR.
  eapply (alloc_meta_fq T BL P B Post _ bail (X_as idle) st L LS INV SGst Ast); [ | | | | exact INV| apply amf_refl| apply lf_refl| | reflexivity].
  - (* [comment removed for export] *)
    intros HFH. pose proof (ncarved_le_groups (X_as idle) st L BL LS INV 0 Qst HFH eq_refl) as NC.
    pose proof (ngroups_le (X_as idle) st L BL LS P INV SGst Ast) as NG0. cbn [x_idle X_as] in NC. unfold NCAP. lia.
  - (* [comment removed for export] *)
    exact (group_bytes_B (X_as idle) st L BL LS P B INV eq_refl eq_refl SIst Ast HBP).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 INV1 AF LF SI1 A1 GC1 GEO1. cbn beta iota. eapply HK.
    + split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
      exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    + exact (SINV_QPOST P idle BL st1 (X_as idle) eq_refl SI1 A1).
    + intros c Hc. rewrite GC1. lia.
    + exact (BLF_geo _ st st1 L BL LS INV (amf_slots _ _ AF) GEO1).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 m INV1 NIm AF LF SI1 A1 NC1 GC1 GEO1. cbn beta iota zeta.
    pose proof (BLF_geo _ st st1 L BL LS INV (amf_slots _ _ AF) GEO1) as BF1. cbn [xidle X_as x_idle x_zomb x_pend x_orph x_fresh] in INV1, NIm, SI1. change (mkX (m :: idle) [] None None None) with (X_as (m :: idle)) in INV1, SI1.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (SINV_QPOST P (m :: idle) BL st1 (X_as (m :: idle)) eq_refl SI1 A1) as QP1.
    assert (U0 : usage st1 sc = gcnt st1 sc) by exact (ia_usage _ (proj1 (proj2 INV1)) sc Hsc).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    + (* [comment removed for export] *)
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns).
      assert (HU : usage st1 sc <= u1).
      { unfold u1. destruct (Z.even sc && (sc <? 32)) eqn:E; [| lia].
        apply andb_prop in E as [_ E]. apply Z.ltb_lt in E.
        destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & _). fold st1' in INV1'.
        rewrite (ia_usage _ (proj1 (proj2 INV1')) (sc + 1) ltac:(lia)). pose proof (gcnt_nonneg _ _ _ _ _ (sc + 1) INV1'). lia. }
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        fqtree B L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        destruct (ag_cnt_facts sc req (usage st1 sc) u1 ns c3 n3 Hsc Hreq Hfit HU HB E3) as (STD & NSTD & NUB).
        apply (ag_mmap_fq T idle st st1 L L1 BL LS1 P B m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED QP1 STD); [| exact NUB| exact GC1| exact BF1| exact HBP| exact HK].
        intros NE. rewrite <- U0. exact (NSTD NE). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + (* [comment removed for export] *)
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      apply (ag_nest_fq T rec idle st st1 L L1 BL LS1 P B m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST QP1); [| exact GC1| exact BF1| | exact HBP| exact HK].
      * intros NE. rewrite <- U0. apply (ag_cnt1_nstd sc); [exact Hsc| exact NE].
      * pose proof (nest_host sc (usage st1 sc) Hsc) as NH. cbn zeta in NH.
        change (bump (UNIT * size_class sc) (cnt0_of sc (usage st1 sc))) with c1 in NH.
        specialize (NH HB).
        pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0. destruct N0 as (_ & N2 & _).
        pose proof (rank_host sc (size_to_class (UNIT + c1 * (UNIT * size_class sc) - IB)) ltac:(lia) NH). lia.
  - (* [comment removed for export] *) split; [exact Qst|]. split; [reflexivity|]. split; [reflexivity|]. intros x _. reflexivity.
Qed.
End AGQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SLOTQ.
Variables (T : Type) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop).

#[using="Type"] Theorem alloc_slot_fq (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  QPOST P idle BL st -> zlen idle <= rank sc -> PHI P + R63 BL <= B + 3 * PGSZ ->
  (forall st1 idx L1 LS1, SLOT_POST idle sc req st L BL st1 idx L1 LS1 -> QPOST P idle BL st1 ->
     (forall c, 0 <= c < sc -> gcnt st1 c <= gcnt st c) -> BLF st st1 BL -> fqtree B L1 (k st1 idx) Post) ->
  fqtree B L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit QP RK HBP HK.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  destruct (try_avail_okQ T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & [TAF RES] & FF).
  rewrite E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
  (* [comment removed for export] *)
  pose proof QP as (SGst & Qst & Ast). destruct (QPOST_SINV P idle BL st (X_as idle) eq_refl QP) as [SIst _].
  assert (XFER : forall X1, x_idle X1 = idle -> INVL X1 st1 L BL LS1 -> QPOST P idle BL st1 /\ (forall c, 0 <= c < 48 -> gcnt st1 c <= gcnt st c) /\ BLF st st1 BL).
  { intros X1 HX INV1.
    destruct (SINVx_xfer (X_as idle) X1 st st1 L L BL LS LS1 P None INV INV1 ltac:(rewrite HX; reflexivity) FF Ast (SINV_SINVx _ _ _ SIst) ltac:(intros; discriminate)) as (SI1 & A1 & GC & _).
    split; [exact (SINV_QPOST P idle BL st1 X1 HX SI1 A1)|]. split; [exact GC| exact (BLF_ffr X1 st st1 L BL LS1 INV1 FF)]. }
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
  - (* [comment removed for export] *)
    change (negb (0 =? 0)) with false. cbn iota.
    destruct (XFER (X_as idle) eq_refl INV1) as (QP1 & GC1 & BF1).
    assert (RECQ : REC_OKQ T (alloc_slot full_lay f) sc P B Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' QP' RK' HBP' HK'.
      apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_fq T (alloc_slot full_lay f) sc P B Post RECQ idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA QP1 RK HBP).
    intros st2 go L2 LS2 (ACT2 & LIVE2 & GP2 & RES2) QP2 GLE2 BF2. destruct go as [g|].
    + destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2').
      cbn zeta.
      destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                  ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
        as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4).
      rewrite EQ.
      (* [comment removed for export] *)
      set (st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2) in *.
      set (st4 := queue_st (LActive sc) g st3) in *.
      assert (F24 : FFR st2 st4).
      { apply (FFR_trans st2 st3 st4).
        - unfold st3. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr].
        - unfold st4. apply FFR_queue_st.
          + unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
          + unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 g). rewrite Em. cbn. discriminate.
          + intros a Ha. exfalso. unfold st3 in Ha. rewrite get_head_upd_meta in Ha. cbn in Ha. rewrite ACT2 in Ha by lia. rewrite HA in Ha. discriminate.
          + intros a z Ha. exfalso. unfold st3 in Ha. rewrite get_head_upd_meta in Ha. cbn in Ha. rewrite ACT2 in Ha by lia. rewrite HA in Ha. discriminate. }
      destruct QP2 as (SG2 & Q2 & A2). destruct (QPOST_SINV P idle BL st2 (mkX idle [] None None (Some g)) eq_refl (conj SG2 (conj Q2 A2))) as [SI2 _].
      destruct (SINVx_xfer (mkX idle [] None None (Some g)) _ st2 st4 L2 L2 BL LS2 LS4 P None INV2 INV4 eq_refl F24 A2 (SINV_SINVx _ _ _ SI2) ltac:(intros; discriminate)) as (SI4 & A4 & GC4 & _).
      eapply HK.
      * split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]]|].
        right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
        split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
        split; [exact INV4| exact TF4].
      * exact (SINV_QPOST P idle BL st4 (xpend (X_as idle) (Some (fst b, sstart (MR st2 g) 0))) eq_refl SI4 A4).
      * intros c Hc. pose proof (GC4 c ltac:(lia)). pose proof (GLE2 c Hc). pose proof (GC1 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2|]. exact (BLF_ffr _ st2 st4 L2 BL LS4 INV4 F24).
    + destruct RES2 as [INV2 TF2']. eapply HK.
      * split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
        left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
      * exact QP2.
      * intros c Hc. pose proof (GLE2 c Hc). pose proof (GC1 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1| exact BF2].
  - (* [comment removed for export] *)
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx.
    destruct (XFER (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl INV1) as (QP1 & GC1 & BF1).
    eapply HK.
    + split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
      pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
      exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
      split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
    + exact QP1.
    + intros c Hc. apply GC1. lia.
    + exact BF1.
Qed.
End SLOTQ.

End WithCeil.
End LB_WSlot.

(* [comment removed for export] *)
Module LB_WMalloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WTry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WTry2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WCreate2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Bits OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.LB_WNtf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_XferF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_WTry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_AG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WSlot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma MIS_le_LS st BL c : MIS st BL c <= LS st BL c.
Proof.
  unfold MIS, LS. induction BL as [|k l IH]; [unfold zcount, zlen; cbn; lia|].
  rewrite !zcount_cons. destruct (slotcls st (bslot k)) as [c'|]; [| lia]. destruct (c' =? c); cbn [andb]; [destruct (size_to_class (bsize k) =? c - 1); lia| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma SG_add_block st BL c off n m i :
  SG st BL -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) < 48 -> 0 <= n < MMAP_THRESHOLD ->
  m_sizeclass (MR st m) - 1 <= size_to_class n <= m_sizeclass (MR st m) + 1 ->
  SG st (((c, off), n) :: BL).
Proof.
  intros S Hs Hsc Hn CLS. destruct S as [S1 S2 S3 S4 S5 S6 S7]. constructor; auto.
  - intros k [<-|Hk]; [| exact (S1 k Hk)]. exists m, i. cbn [bslot bsize fst snd]. split; [exact Hs|].
    split; [intros _; split; [lia| exact CLS]| intros E63; exfalso; lia].
  - intros b x ai Hb H63. right. exact (S6 b x ai Hb H63).
Qed.

#[using="Type"] Lemma AQ_add_block st BL P c off n :
  AQ st BL P -> 0 <= n -> ROOM BL P n -> AQ st (((c, off), n) :: BL) P.
Proof.
  intros A Hn [R1 R2]. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c' Hc'. unfold LR. rewrite zcount_cons. fold (LR BL c'). cbn [bsize snd]. unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; cbn [negb andb]; [exact (A1 c' Hc')|].
    destruct (Z.eqb_spec (size_to_class n) c') as [<-|NE]; [specialize (R1 LT); lia| exact (A1 c' Hc')].
  - unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; [specialize (R2 GE); lia| exact A3].
Qed.

#[using="Type"] Lemma R63_cons c off n BL : R63 (((c, off), n) :: BL) = bigb n + R63 BL.
Proof. unfold R63, bigb, isbig. cbn [map bsize snd]. rewrite zsum_cons. reflexivity. Qed.

#[using="Type"] Lemma bigb_small n : n < MMAP_THRESHOLD -> bigb n = 0.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

#[using="Type"] Lemma bigb_big n : MMAP_THRESHOLD <= n -> bigb n = round_up_pg (n + IB + UNIT) + PGSZ.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma small_class X st L BL LS n : INVL X st L BL LS -> 0 <= n < MMAP_THRESHOLD ->
  let sc0 := size_to_class n in
  let sc := match active st sc0 with
            | Some _ => sc0
            | None =>
              if (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0) then
                let usage1 := usage st (Z.lor sc0 1) in
                let usage1 := match active st (Z.lor sc0 1) with
                              | None => usage1 + 3
                              | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc0 1))) in
                                          if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                              end in
                if usage1 <=? 12 then Z.lor sc0 1 else sc0
              else sc0
            end in
  0 <= sc < 48 /\ n + IB <= UNIT * size_class sc /\ (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)).
Proof.
  intros INV Hn. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. cbn zeta.
  set (sc0 := size_to_class n) in *.
  destruct (active st sc0); [auto|].
  destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (lor1_even sc0 ltac:(lia) EV).
  assert (U : usage st (sc0 + 1) = gcnt st (sc0 + 1)) by exact (ia_usage _ (proj1 (proj2 INV)) (sc0 + 1) ltac:(lia)).
  match goal with |- context [if ?c then sc0 + 1 else sc0] => destruct c eqn:LE end; [| auto].
  apply Z.leb_le in LE.
  pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [unfold UNIT in *; lia|]. right. split; [lia|].
  rewrite <- U. destruct (active st (sc0 + 1)); [| lia]. destruct (_ && _); lia.
Qed.

#[using="Type"] Lemma size_to_class_ne62 m : size_to_class m <> 62.
Proof.
  unfold size_to_class.
  set (n' := Z.shiftr (m + IB - 1) 4). destruct (Z.ltb_spec n' 10) as [LT|GE]; [lia|].
  set (i := (28 - clz32 (n' + 1)) * 4 + 8).
  assert (S61 : forall k, 48 <= k -> size_class k = 0).
  { intros k Hk. unfold size_class. rewrite nth_overflow; [reflexivity|]. cbn. lia. }
  destruct (size_class (i + 1) <? n' + 1) eqn:E1.
  - destruct (size_class (i + 2) <? n' + 1) eqn:E2; [lia|]. intros E. replace (i + 2) with 62 in E2 by lia.
    rewrite (S61 62 ltac:(lia)) in E2. apply Z.ltb_ge in E2. lia.
  - destruct (size_class i <? n' + 1) eqn:E2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section C63Q.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Variables (g : aptr) (rid : N) (r : region) (needed n off : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Hypothesis En : needed = n + IB + UNIT.
Hypothesis Hbig : MMAP_THRESHOLD <= n.
Hypothesis SG3 : SG st3 BL.
Hypothesis Q3 : QM X st3 0.
Hypothesis A3 : AQ st3 BL P.
Hypothesis R63room : n63 BL + 1 <= P 63.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.
Let k0 : blk := (((rid, 16), off), n).

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="CE L BL LS X INV Hn"] Lemma q63_metas : s_metas st6 = <[g := mr']> (s_metas st3).
Proof.
  change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g).
  rewrite (c63_MRg st3 L BL LS g rid INV). unfold ml, mr', p. rewrite (c63_F rid needed Hn). reflexivity.
Qed.

#[using="CE L BL LS X INV"] Lemma q63_groups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  change (s_groups st6) with (s_groups st5). unfold st5, put_group. cbn [s_groups Malloc.set_groups].
  unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite (c63_nogroup st3 L BL LS g rid INV). reflexivity.
Qed.

#[using="CE L BL LS X INV Hn st6"] Lemma q63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. change (s_metas st5) with (s_metas st6). rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

#[using="CE L BL LS X INV Hn mr'"] Lemma q63_slots : s_slots st6 = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold st6, add_slots. rewrite q63_rec5. cbn [Z.iter Pos.iter snd s_slots set_slots].
  replace (aadd p (UNIT + get_stride mr' * 0)) with (rid, 16); [reflexivity|].
  unfold aadd, p. cbn [fst snd]. f_equal. unfold UNIT. lia.
Qed.

#[using="CE L BL LS X INV Hn mr'"] Lemma q63_MR x : x <> g -> MR st6 x = MR st3 x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_ne by congruence. reflexivity. Qed.

#[using="CE L BL LS X INV Hn"] Lemma q63_MRg : MR st6 g = mr'.
Proof. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

#[using="CE L BL LS X INV Hn mr' IM"] Lemma q63_old x : (exists b, hosts st3 b x) -> x <> g /\ MR st6 x = MR st3 x.
Proof.
  intros [b Hb]. assert (NE : x <> g).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ Hb) as MM. rewrite (c63_MRg st3 L BL LS g rid INV) in MM. cbn in MM. discriminate. }
  split; [exact NE| exact (q63_MR x NE)].
Qed.

#[using="CE L BL LS g X INV"] Lemma q63_nogroup_rid b : fst b = rid -> s_groups st3 !! b = None.
Proof. intros Hb. destruct (ir_orph _ _ _ (proj1 INV) rid eq_refl) as (r0 & _ & _ & NG). exact (NG b Hb). Qed.

#[using="CE L BL LS g X INV IM IS"] Lemma q63_noslot : s_slots st3 !! (rid, 16) = None.
Proof.
  destruct (s_slots st3 !! (rid, 16)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM x b i Hb) in Es. assert (Eb : fst b = rid) by (inversion Es; reflexivity).
  destruct Hb as [ai Hb]. rewrite (q63_nogroup_rid b Eb) in Hb. discriminate.
Qed.

#[using="CE L BL LS X INV Hn mr' IM IS"] Lemma q63_slots_old s v : s_slots st3 !! s = Some v -> s_slots st6 !! s = Some v.
Proof. intros Hs. rewrite q63_slots, lookup_insert_ne; [exact Hs|]. intros <-. rewrite q63_noslot in Hs. discriminate. Qed.

#[using="CE L BL LS X INV Hn mr' IM IS"] Lemma q63_slotcls_old s : s_slots st3 !! s <> None -> slotcls st6 s = slotcls st3 s.
Proof.
  intros Hs. destruct (s_slots st3 !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (q63_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

#[using="CE L BL LS X INV"] Lemma q63_gmetas : Permutation (gmetas st6) ((g, p) :: gmetas st3).
Proof.
  unfold gmetas, groups_l. rewrite q63_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact (q63_nogroup_rid p eq_refl)|]. cbn. apply Permutation_refl.
Qed.

#[using="Type"] Lemma q63_gmetas_hosts x b : In (x, b) (gmetas st3) -> exists b', hosts st3 b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

#[using="CE L BL LS X INV"] Lemma q63_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas st3) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st6)) = F' (g, p) + zsum (map F (gmetas st3)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ q63_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.

#[using="CE L BL LS X INV Hn mr' IM"] Lemma q63_gcnt c : c <> 63 -> gcnt st6 c = gcnt st3 c.
Proof.
  intros NE. rewrite !gcnt_gmetas. rewrite (q63_sum (fun mb => if m_sizeclass (MR st3 (fst mb)) =? c then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - intros x b Hin. cbn [fst]. destruct (q63_old x (q63_gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

#[using="CE L BL LS X INV Hn mr'"] Lemma q63_stdg_g : stdg st6 g = false.
Proof.
  unfold stdg, cls. rewrite q63_MRg. cbn [m_sizeclass]. unfold mr', ml, p. rewrite (c63_stride rid needed Hn).
  pose proof (c63_ml needed Hn) as [M _]. replace (_ =? S_ 63) with false; [apply andb_false_r|].
  symmetry. apply Z.eqb_neq. unfold S_. change (size_class 63) with 0. unfold UNIT. lia.
Qed.

#[using="CE L BL LS X INV Hn mr' IM"] Lemma q63_stdg_old x : (exists b, hosts st3 b x) -> stdg st6 x = stdg st3 x.
Proof. intros Hx. destruct (q63_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

#[using="CE L BL LS X INV Hn mr' IM"] Lemma q63_nsc c : 0 <= c < 48 -> nsc st6 c = nsc st3 c.
Proof.
  intros Hc. unfold nsc. rewrite (q63_sum (fun mb => if (cls st3 (fst mb) =? c) && negb (stdg st3 (fst mb)) then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. unfold cls at 1. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). cbn. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (q63_gmetas_hosts x b Hin) as Hx. rewrite (q63_stdg_old x Hx). destruct (q63_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

#[using="CE L BL LS X INV Hn mr' IM"] Lemma q63_ncarved : ncarved st6 = ncarved st3.
Proof.
  unfold ncarved. rewrite q63_metas.
  pose proof (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))) as Hg.
  change (zlen (map_to_list (<[g:=mr']> (s_metas st3))) = zlen (map_to_list (s_metas st3))).
  unfold zlen. rewrite (Permutation_length (mtl_insert_old (s_metas st3) g mr' _ Hg)), (Permutation_length (mtl_delete (s_metas st3) g _ Hg)). reflexivity.
Qed.

#[using="CE L LS X INV Hn mr' IM IS"] Lemma q63_MIS c : MIS st6 BL c = MIS st3 BL c.
Proof.
  unfold MIS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (q63_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.

#[using="CE L LS X INV Hn En Hbig SG3 Q3 A3 R63room mr' IM IG IS"] Theorem c63_quant : SG st6 (k0 :: BL) /\ QM x0 st6 0 /\ AQ st6 (k0 :: BL) P /\ BLF st3 st6 BL.
Proof.
  pose proof (c63_ml needed Hn) as [M RU].
  assert (GRP' : forall b x aix, s_groups st6 !! b = Some (mkGhdr (Some x) aix) -> (x = g /\ b = p) \/ (x <> g /\ s_groups st3 !! b = Some (mkGhdr (Some x) aix) /\ MR st6 x = MR st3 x)).
  { intros b x aix Hb. rewrite q63_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (q63_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  assert (BF : BLF st3 st6 BL).
  { intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). apply q63_slotcls_old. rewrite Hs. discriminate. }
  split; [| split; [| split; [| exact BF]]].
  - (* [comment removed for export] *) destruct SG3 as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k [<-|Hk].
      * exists g, 0. unfold k0. cbn [bslot bsize fst snd]. rewrite q63_slots, lookup_insert_eq, q63_MRg. unfold mr'. cbn [m_sizeclass m_maplen].
        split; [reflexivity|]. split; [intros; exfalso; lia|]. intros _. split; [exact Hbig|]. unfold ml in *. rewrite RU, En. unfold PGSZ. lia.
      * destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (q63_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + intros b x aix Hb Hl Hml Hc. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Hc; unfold mr' in Hc; cbn in Hc; lia|].
      rewrite MRx in *. exact (S2 _ _ _ Hb0 Hl Hml Hc).
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Hc; unfold mr' in Hc; cbn in Hc; lia|].
      rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_stdg_g in SD; discriminate|].
      rewrite (q63_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3').
      split; [exact Q1|]. split; [| exact Q3']. intros Z0. destruct (Q2 Z0) as (g0 & i0 & Hs & Eg). exists g0, i0. split; [exact (q63_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact Eg.
    + intros c Hc. rewrite (q63_nsc c Hc). exact (S5 c Hc).
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * left. rewrite q63_MRg. unfold k0, slot_start', mr'. cbn -[Z.add Z.mul]. unfold p. cbn [fst snd]. f_equal. rewrite (c63_stride rid needed Hn) || idtac. unfold UNIT. lia.
      * right. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g0 i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Z0; unfold mr' in Z0; cbn in Z0; unfold ml in Z0; lia|].
      rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g1 & i1 & Hs & _).
      rewrite (q63_slots_old _ _ Hs) in Hs'. assert (g1 = g0 /\ i1 = i) as [-> ->] by (split; congruence).
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  - (* [comment removed for export] *)
    assert (RG' : s_regions st6 = s_regions st3) by reflexivity.
    assert (CX' : s_ctx st6 = s_ctx st3) by reflexivity.
    assert (AP' : apages st6 = apages st3) by (apply apages_ext; [exact RG'| rewrite CX'; reflexivity]).
    destruct Q3 as [Q1 Q2 Q3' Q4 Q5 Q6]. constructor; rewrite ?RG', ?q63_ncarved, ?AP', ?CX'; auto.
    intros x mr Hx Z0. rewrite q63_metas in Hx. destruct (aptr_eq_dec x g) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. cbn in Z0. discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. cbn in I0. destruct I0 as [I0|[]]. congruence.
  - (* [comment removed for export] *) destruct A3 as [A1 A2 A3' A4 A5]. constructor; auto.
    + intros c Hc. unfold LR. rewrite zcount_cons. fold (LR BL c). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). cbn. exact (A1 c Hc).
    + intros c Hc. rewrite (q63_gcnt c ltac:(lia)). exact (A2 c Hc).
    + unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). lia.
    + rewrite q63_ncarved. exact A4.
Qed.
End C63Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section COREQ.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z) (n B : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis SI : SINV x0 st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis Hn : 0 <= n.
Hypothesis HR : ROOM BL P n.
Hypothesis HB : PHI P + R63 BL + bigb n <= B + 3 * PGSZ.
Hypothesis HQ : bigb n <= QMAX.

(* [comment removed for export] *)
#[using="Hn HR"] Lemma small_leaf st1 L1 LS1 g bg idx sc X1 :
  INVL X1 st1 L1 BL LS1 -> x_idle X1 = [] -> hosts st1 bg g -> 0 <= idx <= m_last_idx (MR st1 g) ->
  m_sizeclass (MR st1 g) = sc -> 0 <= sc < 48 ->
  (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)) ->
  SINV X1 st1 BL -> AQ st1 BL P -> BLF st st1 BL -> n < MMAP_THRESHOLD ->
  CORE_POSTQ n BL P L1 (st1, Some (g, idx)).
Proof.
  intros INV1 HX Hh Hidx SCg Hsc CLS SI1 A1 BF Hlt. unfold CORE_POSTQ. cbn [fst snd]. intros bg' off Hh'.
  pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ _ Hh' Hh) as ->.
  pose proof (is_total _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1)))))) bg g idx Hh Hidx) as T.
  rewrite (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) g bg idx Hh) in T.
  split.
  - apply (SINV_X X1 x0); [rewrite HX; reflexivity|]. apply SINV_split in SI1 as [G1 Q1]. apply SINV_split. split; [| exact Q1].
    apply (SG_add_block st1 BL _ off n g idx G1 T ltac:(lia) ltac:(lia)). rewrite SCg.
    destruct CLS as [E|[E G12]]; lia.
  - exact (AQ_add_block st1 BL P _ off n A1 Hn HR).
Qed.


#[using="LS INV TF SI HAQ Hn HR HB"] Lemma malloc_small_fq : n < MMAP_THRESHOLD ->
  fqtree B L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTQ n BL P).
Proof.
  intros Hlt. pose proof (small_class x0 st L BL LS n INV ltac:(lia)) as SCF. cbn zeta in SCF.
  pose proof HB as HB0. rewrite (bigb_small n Hlt), Z.add_0_r in HB0.
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP.
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end) in *.
  clearbody sc. destruct SCF as (SC' & FIT' & CLS).
  assert (SLOT : fqtree B L (alloc_slot full_lay FUEL st sc n (fun st1 idx =>
             if idx <? 0 then ret (st1, None)
             else match active st1 sc with
                  | Some gp => ret (st1, Some (gp, idx))
                  | None => SVis (EUndef UBadPtr) (fun _ => ret (st, @None (aptr * Z)))
                  end) (ret (st, None))) (CORE_POSTQ n BL P)).
  { apply (alloc_slot_fq (mstate * option (aptr * Z)) P B (CORE_POSTQ n BL P) FUEL sc [] st L BL LS n); try assumption.
    - unfold FUEL. cbn. lia.
    - apply NoDup_nil_2.
    - pose proof (rank_range sc). unfold zlen. cbn. lia.
    - intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES) QP1 GC1 BF1.
      destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      + change (-1 <? 0) with true. cbn iota. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
        exact (QPOST_SINV P [] BL st1 x0 eq_refl QP1).
      + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. apply fqtree_ret.
        destruct (QPOST_SINV P [] BL st1 (xpend (X_as []) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl QP1) as [SI1 A1].
        apply (small_leaf st1 L1 LS1 g bg idx sc _ INV1 eq_refl (ex_intro _ ai Hg) Hidx SCg SC' CLS SI1 A1 BF1 Hlt). }
  destruct (active st sc) as [gp|] eqn:HA; [| exact SLOT].
  destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
  { rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb]. exact SLOT. }
  (* [comment removed for export] *)
  destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
  pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
  destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
  assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
  rewrite LNZ. cbn [negb]. apply fqtree_ret.
  pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
  set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
  assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
  { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; split; reflexivity. }
  destruct MRg as [ML MSC].
  assert (F01 : FFR st st1).
  { unfold st1. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO)| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]. }
  destruct (SINVx_xfer x0 (xpend x0 (Some (fst bm, sstart (MR st gp) (ctz32 (lowbit (m_avail (MR st gp))))))) st st1 L L BL LS LS P None INV INV1 eq_refl F01 HAQ (SINV_SINVx _ _ _ SI) ltac:(intros; discriminate)) as (SI1 & A1 & _).
  apply (small_leaf st1 L LS gp bm _ sc _ INV1 eq_refl); try assumption.
  - apply (proj2 (hosts_ext st st1 eq_refl bm gp)). exists ai. exact Hbm.
  - rewrite ML. exact Hidx.
  - rewrite MSC. exact Esc.
  - exact (BLF_ffr _ st st1 L BL LS INV1 F01).
Qed.

(* [comment removed for export] *)
#[using="LS INV TF SI HAQ HR HB HQ"] Lemma malloc_big_fq : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  fqtree B L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
        | Some g =>
          let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) (ret (st, @None (aptr * Z)))))
    (CORE_POSTQ n BL P).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof HB as HB0. rewrite (bigb_big n Hbig) in HB0. fold needed in HB0. assert (PG0 : 0 <= PGSZ) by (unfold PGSZ; lia).
  pose proof (round_up_pg_spec needed) as [[RU1 RU2] _].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP. destruct QP as (SGst & Qst & Ast).
  pose proof (state_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(unfold PGSZ in *; lia)) as SB.
  pose proof (gm_BB_nonneg x0 st L BL LS INV) as [GM0 BB0].
  pose proof HQ as HQ0. rewrite (bigb_big n Hbig) in HQ0. fold needed in HQ0.
  apply fqtree_vis; [reflexivity| reflexivity| | | | | intros _; rewrite mmap_len_rup; unfold PGSZ in *; lia].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - (* [comment removed for export] *)
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas ((a, needed, 0) :: ld_metas L) L else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    destruct (is_err a); [lia|]. rewrite gm_add_group, BB_set_groups, mmap_len_rup. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_metas ((a, needed, 0) :: ld_metas L) L else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (FR : s_regions st !! rid = None) by (rewrite Erid; exact (nm_fresh _ _ _ _ _ INV)).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { destruct (step_seq_fields st1) as (A' & B' & _). apply (TF0_ctrl st1); [exact A'| exact B'|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
      (* [comment removed for export] *)
      pose proof (QPOST_new_group_region P [] BL st x0 L LS a needed INV (conj SGst (conj Qst Ast))) as QP1. rewrite <- Est1 in QP1.
      pose proof (QPOST_qsame P [] BL st1 (step_seq st1) _ L1 LS INV1 (qsame_step_seq st1) QP1) as (SG2 & Q2 & A2).
      set (st2 := step_seq st1) in *.
      assert (GB2 : group_bytes st2 = group_bytes st + round_up_pg needed).
      { rewrite (group_bytes_ext st1 st2 SS4). rewrite !group_bytes_msum, Est1. unfold new_region. cbn [fst s_regions set_next_rid set_regions].
        rewrite <- Erid. rewrite (msum_regions_insert_fresh gbF st rid _ FR). unfold gbF at 1. cbn. lia. }
      eapply (alloc_meta_fq (mstate * option (aptr * Z)) BL P B (CORE_POSTQ n BL P) _ _ (xorph x0 (Some rid)) st2 L1 LS INV2 SG2 A2);
        [ | | | | exact INV2| apply amf_refl| apply lf_refl| | reflexivity].
      * (* [comment removed for export] *)
        intros HFH. pose proof (ncarved_le_groups (xorph x0 (Some rid)) st2 L1 BL LS INV2 0 (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2) HFH eq_refl) as NC.
        pose proof (ngroups_le (xorph x0 (Some rid)) st2 L1 BL LS P INV2 SG2 A2) as NG0. cbn [x_idle xorph x0] in NC. unfold zlen in NC. cbn [length] in NC. change (Z.of_nat 0) with 0 in NC. unfold NCAP. lia.
      * (* [comment removed for export] *)
        rewrite GB2. pose proof (group_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(unfold PGSZ in *; lia)). lia.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF SI3 A3' GC3 GEO3. cbn beta iota.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        pose proof (proj1 INV3) as IR3.
        assert (GPOS : forall g, In g (ld_groups L3) -> 0 <= snd g).
        { intros g Hg. apply (Permutation_in _ (ir_groups _ _ _ IR3)) in Hg. apply in_map_iff in Hg as ([q rq] & <- & Hin). cbn.
          apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR3 _ _ Hin) as (_ & _ & L0 & _). lia. }
        apply fqtree_vis; [reflexivity| reflexivity| | | | | exact I].
        -- cbn. split; [exact (brk_quiet_of _ _ _ IR3)|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros z Hz. etransitivity; [apply lbytes_event_post_munmap; exact GPOS|].
           pose proof (ledger_bound _ st3 L3 BL LS3 INV3) as LB3. pose proof (regions_bound _ st3 L3 BL LS3 P INV3 SI3 A3' eq_refl) as RB3.
           unfold ORPH in RB3. cbn [x_orph xorph x0] in RB3. rewrite Hr3 in RB3. cbn [r_len] in RB3. lia.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
           destruct (SINV_drop_orph _ st3 L3 BL LS3 P rid _ INV3 Hr3 eq_refl SI3 A3') as [S'' A'']. split; [exact (SINV_X (xorph x0 (Some rid)) x0 _ _ eq_refl S'')| exact A''].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF SI3 A3' NC3 GC3 GEO3. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl st2); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3, SI3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
        match goal with |- fqtree _ _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. intros bg off Hh.
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (Hh6 : hosts st6 bg g) by exact Hh.
        pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV6))) _ _ _ Hh6 (ex_intro _ 0 GR6)) as ->.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity. rewrite MR7, MR6.
        replace (sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0) with 16 by (unfold sstart, gbase; cbn -[Z.mul Z.add get_stride]; unfold UNIT; lia).
        change (fst (rid, 0)) with rid.
        apply SINV_split in SI3 as [SG3 Q3].
        destruct (c63_quant st3 L3 BL LS3 P g rid needed n off INV3 ltac:(lia) eq_refl Hbig SG3 Q3 A3' ltac:(exact (proj2 HR Hbig)))
          as (SG6 & Q6 & A6 & _).
        fold st6 in SG6, Q6, A6.
        assert (SV6 : forall s x i, s_slots st6 !! s = Some (x, i) -> exists b, hosts st6 b x).
        { intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV6)))))) _ _ _ Hs)). }
        split.
        -- apply SINV_split. split.
           ++ apply (SG_frame st6 st7 _ eq_refl eq_refl ltac:(intros; reflexivity) SV6 SG6).
           ++ destruct Q6 as [Q1' Q2' Q3' Q4' Q5' Q6']. constructor; auto.
        -- apply (AQ_frame st6 st7 _ P eq_refl ltac:(intros; reflexivity)); [| exact A6]. exact (aq_carved _ _ _ A6).
      * (* [comment removed for export] *)
        split; [exact (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2)|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

#[using="LS INV TF SI HAQ Hn HR HB HQ"] Theorem malloc_core_fq : fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_fq Hbig Hov).
    + exact (malloc_small_fq Hsmall).
Qed.
End COREQ.

#[using="Type"] Theorem malloc_core_fq_proof : malloc_core_fq_stmt.
Proof. intros st L BL LS P n B INV TF SI HAQ Hn HR HB HQ. exact (malloc_core_fq st L BL LS P n B INV TF SI HAQ Hn HR HB HQ). Qed.

Check (malloc_core_fq_proof : malloc_core_fq_stmt).

End WithCeil.
End LB_WMalloc.

(* [comment removed for export] *)
Module LB_Raw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WEnframe2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Sim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Logic OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Kernel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Embed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Section LBRaw.
Context {St : Type} {AS : AllocSt St}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bs (k : blk) : cptr * Z := (bslot k, bsize k).
Definition xs (xb : bptr * Z) : cptr * Z := (fst (fst xb), snd xb).

(* [comment removed for export] *)
Definition LRX (X : list (bptr * Z)) (c : Z) : Z := zcount (fun xb => negb (MMAP_THRESHOLD <=? snd xb) && (size_to_class (snd xb) =? c)) X.
Definition n63X (X : list (bptr * Z)) : Z := zcount (fun xb => MMAP_THRESHOLD <=? snd xb) X.
Definition R63X (X : list (bptr * Z)) : Z := zsum (map (fun xb => if MMAP_THRESHOLD <=? snd xb then round_up_pg (snd xb + IB + UNIT) + PGSZ else 0) X).
Definition ROOMX (X : list (bptr * Z)) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LRX X (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63X X + 1 <= P 63).

#[using="Type"] Lemma zcount_map {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

#[using="Type"] Lemma LRX_eq X BL c : Permutation (map xs X) (map bs BL) -> LRX X c = LR BL c.
Proof.
  intros HP. unfold LRX, LR, isbig.
  transitivity (zcount (fun q : cptr * Z => negb (MMAP_THRESHOLD <=? snd q) && (size_to_class (snd q) =? c)) (map xs X)); [rewrite zcount_map; reflexivity|].
  rewrite (zcount_perm _ _ _ HP), zcount_map. reflexivity.
Qed.
#[using="Type"] Lemma n63X_eq X BL : Permutation (map xs X) (map bs BL) -> n63X X = n63 BL.
Proof.
  intros HP. unfold n63X, n63, isbig.
  transitivity (zcount (fun q : cptr * Z => MMAP_THRESHOLD <=? snd q) (map xs X)); [rewrite zcount_map; reflexivity|].
  rewrite (zcount_perm _ _ _ HP), zcount_map. reflexivity.
Qed.
#[using="Type"] Lemma R63X_eq X BL : Permutation (map xs X) (map bs BL) -> R63X X = R63 BL.
Proof.
  intros HP. unfold R63X, R63, isbig.
  transitivity (zsum (map (fun q : cptr * Z => if MMAP_THRESHOLD <=? snd q then round_up_pg (snd q + IB + UNIT) + PGSZ else 0) (map xs X))); [rewrite map_map; reflexivity|].
  rewrite (zsum_map_perm _ _ _ HP), map_map. reflexivity.
Qed.
#[using="Type"] Lemma ROOMX_eq X BL P n : Permutation (map xs X) (map bs BL) -> ROOMX X P n -> ROOM BL P n.
Proof. intros HP [R1 R2]. split; [rewrite <- (LRX_eq X BL _ HP); exact R1| rewrite <- (n63X_eq X BL HP); exact R2]. Qed.

#[using="Type"] Lemma R63X_cons p n X : R63X ((p, n) :: X) = bigb n + R63X X.
Proof. unfold R63X, bigb. cbn [map snd]. rewrite zsum_cons. reflexivity. Qed.
#[using="Type"] Lemma R63X_nonneg X : 0 <= R63X X.
Proof.
  unfold R63X. apply zsum_map_nonneg. intros xb _. destruct (Z.leb_spec MMAP_THRESHOLD (snd xb)); [| lia].
  pose proof (round_up_pg_spec (snd xb + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. lia.
Qed.
#[using="Type"] Lemma bigb_nonneg n : 0 <= bigb n.
Proof. unfold bigb. destruct (Z.leb_spec MMAP_THRESHOLD n); [| lia]. pose proof (round_up_pg_spec (n + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LBUDGET : Z := 2 ^ 34.

(* [comment removed for export] *)
Definition QI (X : list (bptr * Z)) (P : Z -> Z) : assn St := fun s mo =>
  (exists st L BL LS, strip st = ps_m s /\ INVL x0 st L BL LS /\ SINV x0 st BL /\ AQ st BL P
      /\ KL L (ps_brk s) mo /\ LI L mo /\ Permutation (map xs X) (map bs BL))
  /\ PHI P + R63X X <= LBUDGET.

#[using="Type"] Lemma QI_live X P s mo : QI X P s mo -> live mo <= LBUDGET.
Proof.
  intros [(st & L & BL & LS & _ & INV & SI & HAQ & HK & HL & HP) HB].
  pose proof (live_bound x0 st L BL LS P INV SI HAQ (ps_brk s) mo eq_refl HK HL) as LB.
  unfold ORPH in LB. cbn [x_orph x0] in LB. rewrite <- (R63X_eq X BL HP) in LB. unfold live, PINB, PGSZ in *. lia.
Qed.

#[using="Type"] Lemma QI_perm X Y P s mo : Permutation X Y -> QI X P s mo -> QI Y P s mo.
Proof.
  intros HXY [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) HB]. split.
  - exists st, L, BL, LS. repeat (split; [assumption|]). etransitivity; [| exact HP]. apply Permutation_map. apply Permutation_sym. exact HXY.
  - rewrite <- (zsum_map_perm _ _ _ HXY) || idtac. unfold R63X in *. rewrite (zsum_map_perm _ _ _ (Permutation_sym HXY)). exact HB.
Qed.

#[using="Type"] Lemma QI_fds X P s mo mo' : QI X P s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> QI X P s mo'.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) HB] Hvm Hmi Hh. split; [| exact HB].
  exists st, L, BL, LS. repeat (split; [assumption|]). split; [| split; [| exact HP]].
  - destruct HK; constructor; try (rewrite Hvm); auto.
  - unfold LI in *. rewrite Hvm. exact HL.
Qed.

#[using="Type"] Lemma QI_minv X P s mo : QI X P s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(st & L & BL & LS & _ & _ & _ & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

#[using="Type"] Lemma QI_after_node X P s mo n rsp mo' evs :
  QI X P s mo -> node_static_ok n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> QI X P s mo'.
Proof.
  intros HQ Hso Hst Hvm. destruct (QI_minv _ _ _ _ HQ) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hso Hmi Hh Hst) as [Hh' Hmi']. eapply QI_fds; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma QI_other X P s s' mo : QI X P s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> QI X P s' mo.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) HB] Hm Hb. split; [| exact HB].
  exists st, L, BL, LS. rewrite Hm, Hb. repeat (split; [assumption|]). exact HP.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma zsum_map_le' {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof. apply zsum_map_le. Qed.

#[using="Type"] Lemma CAP_mono P P' c : (forall c, P c <= P' c) -> CAP P c <= CAP P' c.
Proof.
  intros HP. unfold CAP, HOSTSTD.
  assert (zsum (map (fun c' => if bighost c' =? c then (CAP0 P c' + 32) / cmax c' else 0) guests)
          <= zsum (map (fun c' => if bighost c' =? c then (CAP0 P' c' + 32) / cmax c' else 0) guests)); [| assert (C0 : CAP0 P c <= CAP0 P' c) by (unfold CAP0; pose proof (HP (c - 1)); pose proof (HP c); pose proof (HP (c + 1)); lia); lia].
  apply zsum_map_le. intros c' Hc'. destruct (bighost c' =? c); [| lia].
  assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia).
  pose proof (tab_basic_ok c' G) as (_ & CM & _). apply Z.div_le_mono; [lia|]. assert (C0 : CAP0 P c' <= CAP0 P' c') by (unfold CAP0; pose proof (HP (c' - 1)); pose proof (HP c'); pose proof (HP (c' + 1)); lia). lia.
Qed.
#[using="Type"] Lemma NCAP_mono P P' : (forall c, P c <= P' c) -> NCAP P <= NCAP P'.
Proof.
  intros HP. unfold NCAP, NG.
  assert (zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes) <= zsum (map (fun c => (CAP P' c + 32) / cmax c + 160) classes)); [| specialize (HP 63); lia].
  apply zsum_map_le. intros c Hc. apply In_classes in Hc. pose proof (tab_basic_ok c Hc) as (_ & CM & _).
  pose proof (CAP_mono P P' c HP). apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
Qed.
#[using="Type"] Lemma AQ_monoP st BL P P' : (forall c, P c <= P' c <= PMAX) -> AQ st BL P -> AQ st BL P'.
Proof.
  intros HP A. destruct A as [A1 A2 A3 A4 A5]. assert (HP' : forall c, P c <= P' c) by (intros c; pose proof (HP c); lia). constructor.
  - intros c Hc. specialize (A1 c Hc). specialize (HP c). lia.
  - intros c Hc. pose proof (CAP_mono P P' c HP'). specialize (A2 c Hc). lia.
  - specialize (HP 63). lia.
  - pose proof (NCAP_mono P P' HP'). lia.
  - intros c. specialize (A5 c). specialize (HP c). lia.
Qed.
#[using="Type"] Lemma QI_monoP X P P' s mo : (forall c, P c <= P' c <= PMAX) -> PHI P' + R63X X <= LBUDGET -> QI X P s mo -> QI X P' s mo.
Proof.
  intros HP HB [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HPm) _]. split; [| exact HB].
  exists st, L, BL, LS. repeat (split; [assumption|]). split; [exact (AQ_monoP st BL P P' HP HAQ)|]. auto.
Qed.

#[using="Type"] Lemma QI_nodup X P s mo : QI X P s mo -> List.NoDup (map (fun xb => fst (fst xb)) X).
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) _].
  pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND.
  assert (ND' : List.NoDup (map bslot BL)) by (apply NoDup_ListNoDup; exact ND).
  assert (E1 : map (fun xb : bptr * Z => fst (fst xb)) X = map fst (map xs X)) by (rewrite map_map; reflexivity).
  assert (E2 : map bslot BL = map fst (map bs BL)) by (rewrite map_map; reflexivity).
  rewrite E1. rewrite E2 in ND'. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact HP| exact ND'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma SINV_ctrl X st st1 BL : ctrl_eq st st1 -> SINV X st BL -> SINV X st1 BL.
Proof.
  intros CE S.
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (NC : ncarved st1 = ncarved st) by (unfold ncarved; rewrite (ce_metas _ _ CE); reflexivity).
  assert (AP : apages st1 = apages st).
  { unfold apages, regions_l, frontier. rewrite (ce_regions _ _ CE), (ce_ctx _ _ CE). reflexivity. }
  assert (SCL : forall s, slotcls st1 s = slotcls st s) by (intros s; unfold slotcls, cls; rewrite (ce_slots _ _ CE); destruct (s_slots st !! s) as [[? ?]|]; [rewrite MR1|]; reflexivity).
  assert (STD : forall x, stdg st1 x = stdg st x) by (intros x; unfold stdg, cls; rewrite !MR1; reflexivity).
  destruct S as [qb_cls qg_one qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; rewrite ?(ce_slots _ _ CE), ?(ce_groups _ _ CE), ?(ce_metas _ _ CE), ?(ce_regions _ _ CE), ?(ce_ctx _ _ CE), ?NC, ?AP; auto.
  - intros k Hk. destruct (qb_cls k Hk) as (m0 & i0 & H0 & H1 & H2). exists m0, i0. rewrite !MR1. auto.
  - intros b m' ai Hg. rewrite !MR1. intros A0 A1 A2. exact (qg_one _ _ _ Hg A0 A1 A2).
  - intros b m' ai Hg. rewrite !MR1. intros A1 A2. exact (qg_map _ _ _ Hg A1 A2).
  - intros b m' ai Hg. rewrite STD, !MR1. intros SG. destruct (qg_std _ _ _ Hg SG) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p' & i' & Hs' & E'). exists p', i'. rewrite (MR1 p'). auto.
  - intros c' Hc'. replace (nsc st1 c') with (nsc st c'); [apply qg_small; exact Hc'|].
    unfold nsc, gmetas, groups_l, cls. rewrite (ce_groups _ _ CE). apply zsum_map_ext. intros mb _. rewrite STD, MR1. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros C63. exact (qg_63 _ _ _ Hg C63).
  - intros b m' ai p' i' Hg. rewrite !MR1. intros Z0 Hs'. exact (qg_host _ _ _ _ _ Hg Z0 Hs').
Qed.

#[using="Type"] Lemma bl_remove_perm k BL : In k BL -> List.NoDup (map bslot BL) ->
  Permutation (map bs BL) (bs k :: map bs (bl_remove (bslot k) BL)).
Proof.
  induction BL as [|k' BL IH]; intros Hin ND; [destruct Hin|]. cbn [map bl_remove].
  inversion ND as [|x l NI ND']; subst.
  destruct (aptr_eqb_spec (bslot k') (bslot k)) as [E|NE].
  - destruct Hin as [->|Hin]; [apply Permutation_refl|].
    exfalso. apply NI. rewrite E. apply in_map_iff. exists k. auto.
  - destruct Hin as [->|Hin]; [congruence|]. cbn [map]. etransitivity; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

#[using="Type"] Lemma INVL_nodup_slots X st L BL LS : INVL X st L BL LS -> List.NoDup (map bslot BL).
Proof. intros INV. apply NoDup_ListNoDup. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

Definition GT : St -> Model -> Prop := fun _ _ => True.
#[using="Type"] Lemma frame_ok_GT : frame_ok GT.
Proof. intros s s' mo mo' _ _ _. exact I. Qed.

Section RAWQ.
Hypothesis MQ : malloc_core_fq_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma free_simQ st L BL LS P c off n (o : unit) ans o' st' :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> In ((c, off), n) BL ->
  follow (prun pans0 pupd0 o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  SINV x0 st' (bl_remove c BL) /\ AQ st' (bl_remove c BL) P.
Proof.
  intros INV SI HAQ Hk Hf.
  pose proof (free_fq st L BL LS P c off n (PHI P + R63 BL) INV SI HAQ Hk ltac:(unfold PGSZ; lia)) as FQ.
  pose proof (ftree_prun pans0 pupd0 pans0_range _ L _ o (@fqtree_ftree _ _ _ _ _ _ FQ)) as PT.
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ (LS' & _ & S' & A')]. split; assumption.
Qed.

#[using="Type"] Theorem raw_free_L X P p n :
  mspecL LBUDGET (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P).
Proof.
  unfold raw_free.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) HB]].
  assert (Hin : In (fst p, n) (map bs BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebs & Hk). unfold bs in Ebs. cbn in Ebs.
  assert (Ec : c = fst p) by congruence. assert (En : n' = n) by congruence. subst n'.
  rewrite R63X_cons in HB. pose proof (bigb_nonneg n) as BBn.
  pose proof (R63X_eq _ _ HP) as R63E. rewrite R63X_cons in R63E.
  (* [comment removed for export] *)
  assert (QT : qtree (LBUDGET - PINB) L (cfree (ps_m s1) (Some (fst p))) (fun _ _ => True)).
  { rewrite <- E, <- Ec.
    eapply (qtree_of_full pans0 pupd0 pans0_range (RR := FREL)).
    - exact (free_fq st L BL LS P c off n (LBUDGET - PINB) INV SI HAQ Hk ltac:(unfold PINB, PGSZ; lia)).
    - exact (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)).
    - intros; exact I. }
  eapply mspecL_bind.
  { eapply (mspecL_monoB (LBUDGET - PINB + PINB) LBUDGET); [lia|].
    eapply mspecL_pre; [apply (membedL (LBUDGET - PINB) (cfree (ps_m s1) (Some (fst p))) (fun _ _ => True) GT L s1 frame_ok_GT QT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL| exact I]. }
  intros stc'. cbn beta iota.
  apply mspecL_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HL' & _ & Hm & Hx0).
  apply mspecL_upd'. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2).
  rewrite <- E, <- Ec in Hf, HL2.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
  unfold FREL in SF. cbn in SF.
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (_ & _ & LIVE' & LS' & INV').
  destruct (free_simQ st L BL LS P c off n tt ans o' st' INV SI HAQ Hk FF) as [SI' HAQ'].
  rewrite HL2 in INV'.
  split; [| lia].
  exists st', L', (bl_remove c BL), LS'. autorewrite with alloc_lens.
  split; [exact SF|]. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
  split; [exact HK'|]. split; [exact HL'|].
  pose proof (bl_remove_perm ((c, off), n) BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP. cbn [bs bslot bsize fst snd] in BP.
  apply (Permutation_cons_inv (l:=map xs X) (a:=bs ((c, off), n))). etransitivity; [| exact BP]. etransitivity; [| exact HP]. cbn [map xs fst snd]. unfold bs. cbn [bslot bsize fst snd]. rewrite Ec. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mallocK (n : Z) (x : mstate * option (aptr * Z)) : M (mstate * optr) :=
  let '(st1, r) := x in
  match r with
  | None => ret (st1, @None aptr)
  | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
  end.

#[using="Type"] Lemma malloc_unfold st n : malloc st n = sbind (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n) (mallocK n).
Proof. reflexivity. Qed.

#[using="Type"] Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st).
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
#[using="MQ"] Lemma malloc_fbnd8 st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> bigb n <= QMAX -> fbnd8 B L (malloc st n).
Proof.
  intros INV SI HAQ Hn HR HB HQ. rewrite malloc_unfold.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  eapply fbnd8_bind; [exact (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB HQ)|].
  intros L1 [st1 [[g idx]|]] _; cbn [mallocK].
  - apply fbnd8_enframe_full. intros st' p. exact I.
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="MQ"] Lemma malloc_simQ st L BL LS P n B (o : unit) ans o' st' r :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> bigb n <= QMAX ->
  follow (prun pans0 pupd0 o (malloc st n)) ans = Some (o', (st', r)) ->
  let t := cmalloc (strip st) n in
  let L' := lafter L t ans in
  exists rc, follow t ans = Some (strip st', rc) /\
    match r, rc with
    | None, None => (exists LS', INVL x0 st' L' BL LS') /\ SINV x0 st' BL /\ AQ st' BL P
    | Some pf, Some c => exists off LS', pf = aadd c (UNIT * off)
                         /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ SINV x0 st' (((c, off), n) :: BL) /\ AQ st' (((c, off), n) :: BL) P
    | _, _ => False
    end.
Proof.
  intros INV SI HAQ Hn HR HB HQ Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  assert (E1 : steq (prun pans0 pupd0 o (malloc st n)) (sbind (prun pans0 pupd0 o (malloc_core full_lay st0 n)) (fun x => prun pans0 pupd0 (fst x) (mallocK n (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  (* [comment removed for export] *)
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (@fqtree_ftree _ _ _ _ _ _ (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HR HB HQ))) as PTQ.
  pose proof (ptree_followk _ L _ ans PTQ FK) as CQ. unfold CORE_POSTQ in CQ. cbn [snd fst] in CQ.
  set (L1 := lafter L (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans0 pupd0 n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    specialize (CQ bg). fold c0 in CQ.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ ctrl_eq st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9; reflexivity| exact CE])).
    pose proof (ftree_prun pans0 pupd0 pans0_range _ L1 _ o1 EF) as PTE.
    cbn [mallocK fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Er & INV2 & SS2 & CE2)]. cbn [fst snd] in Er, INV2, SS2, CE2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    exists off, LS1. split; [reflexivity|]. split; [exact INV2|].
    destruct (CQ off Hg) as [S1 A1].
    split; [exact (SINV_ctrl x0 st1 st' _ CE2 S1)| exact (AQ_ctrl st1 st' _ P CE2 A1)].
  - destruct CP as (LS1 & INV1). cbn [mallocK fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [exists LS1; exact INV1|]. exact CQ.
Qed.

#[using="MQ"] Theorem raw_malloc_L X P n : 0 <= n -> bigb n <= QMAX ->
  mspecL LBUDGET (fun s mo => QI X P s mo /\ ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
                        | None => QI X P s mo
                        end).
Proof.
  intros Hn HQ. unfold raw_malloc.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> ([(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) HB0] & HRX & HB)].
  pose proof (R63X_eq _ _ HP) as R63E. pose proof (ROOMX_eq X BL P n HP HRX) as HR.
  assert (HBB : PHI P + R63 BL + bigb n <= (LBUDGET - PINB) + 3 * PGSZ) by (unfold PINB, PGSZ; lia).
  (* [comment removed for export] *)
  assert (QT : qtree (LBUDGET - PINB) L (cmalloc (ps_m s1) n) (fun _ _ => True)).
  { rewrite <- E.
    eapply (qtree_of_full8 pans0 pupd0 pans0_range (RR := MREL)).
    - exact (malloc_INVL st L BL LS n INV Hn).
    - exact (malloc_fbnd8 st L BL LS P n (LBUDGET - PINB) INV SI HAQ Hn HR HBB HQ).
    - exact (malloc_control pans0 pupd0 pans0_range st n tt).
    - intros; exact I. }
  eapply mspecL_bind.
  { eapply (mspecL_monoB (LBUDGET - PINB + PINB) LBUDGET); [lia|].
    eapply mspecL_pre; [apply (membedL (LBUDGET - PINB) (cmalloc (ps_m s1) n) (fun _ _ => True) GT L s1 frame_ok_GT QT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL| exact I]. }
  intros [stc' rc]. cbn beta iota.
  apply mspecL_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HL' & _ & Hm & Hx0).
  eapply mspecL_seq with (R := fun s mo => s = set_m stc' s2 /\ mo = mo2).
  { apply mspecL_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspecL_ret. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2). rewrite <- E in Hf, HL2.
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
  destruct (malloc_simQ st L BL LS P n (LBUDGET - PINB) tt ans o' st' rf INV SI HAQ Hn HR HBB HQ FF) as (rc2 & Hf2 & RES).
  rewrite Hf in Hf2. assert (Est : stc' = strip st') by congruence. assert (Erc : rc = rc2) by congruence. subst rc2.
  rewrite HL2 in RES.
  destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
  - destruct RES as (off & LS' & Epf & INV' & SI' & HAQ'). split.
    + split; [| rewrite R63X_cons; lia].
      exists st', L', (((c, off), n) :: BL), LS'. autorewrite with alloc_lens.
      split; [symmetry; exact Est|]. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
      split; [exact HK'|]. split; [exact HL'|].
      cbn [map xs bs fst snd]. unfold bs at 1. cbn [bslot bsize fst snd]. apply perm_skip. exact HP.
    + destruct (size_overflows n) eqn:Eov.
      * exfalso. rewrite (cmalloc_overflow _ _ Eov) in CP. inversion CP.
      * unfold size_overflows in Eov. apply Z.leb_gt in Eov. lia.
  - destruct RES as (INV' & SI' & HAQ'). split; [| lia].
    destruct INV' as [LS' INV'].
    exists st', L', BL, LS'. autorewrite with alloc_lens.
    split; [symmetry; exact Est|]. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
    split; [exact HK'|]. split; [exact HL'| exact HP].
Qed.
End RAWQ.

End LBRaw.

End WithCeil.
End LB_Raw.

(* [comment removed for export] *)
Module LB_Init.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Nodes Decode Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_QM. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Kernel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Raw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma zsum_nonneg' l : (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. induction l as [|a l IH]; intros H; cbn; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)). unfold zsum in IH. lia. Qed.

#[using="Type"] Lemma CAP_lower P c : (forall c, 0 <= P c) -> 0 <= c -> 1 <= CAP P c.
Proof.
  intros HP Hc.
  assert (0 <= HOSTSTD P c).
  { unfold HOSTSTD. apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc').
    assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
    destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
    apply Z.div_pos; [| lia]. unfold CAP0. pose proof (HP (c' - 1)). pose proof (HP c'). pose proof (HP (c' + 1)). destruct (c' <=? 23); lia. }
  unfold CAP, CAP0. pose proof (HP (c - 1)). pose proof (HP c). pose proof (HP (c + 1)). destruct (c <=? 23); lia.
Qed.

#[using="Type"] Lemma NCAP_lower P : (forall c, 0 <= P c) -> 4 <= NCAP P.
Proof.
  intros HP. unfold NCAP, NG.
  assert (0 <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)).
  { apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c & <- & Hc). apply In_classes in Hc. cbn beta.
    pose proof (tab_basic_ok c Hc) as (_ & CM & _). pose proof (CAP_lower P c HP ltac:(lia)).
    assert (0 <= (CAP P c + 32) / cmax c) by (apply Z.div_pos; lia). lia. }
  pose proof (HP 63). lia.
Qed.

#[using="Type"] Lemma SINV_minit secret resv : SINV x0 (minit secret resv) [].
Proof.
  constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
  - intros k [].
  - intros c Hc. unfold nsc, gmetas, groups_l. cbn [s_groups minit]. rewrite map_to_list_empty. cbn. lia.
  - unfold apages, ncarved, regions_l. cbn [s_regions s_metas minit]. rewrite !map_to_list_empty. unfold zlen. cbn. lia.
  - intros H. lia.
Qed.

#[using="Type"] Lemma gcnt_minit secret resv c : gcnt (minit secret resv) c = 0.
Proof. unfold gcnt. cbn [s_groups minit]. rewrite map_to_list_empty. reflexivity. Qed.

#[using="Type"] Lemma AQ_minit P secret resv : (forall c, 0 <= P c <= PMAX) -> AQ (minit secret resv) [] P.
Proof.
  intros HP0. assert (HP : forall c, 0 <= P c) by (intros c; pose proof (HP0 c); lia). constructor.
  - intros c Hc. unfold LR, zcount, zlen. cbn. apply HP.
  - intros c Hc. rewrite gcnt_minit. pose proof (CAP_lower P c HP ltac:(lia)). lia.
  - unfold n63, zcount, zlen. cbn. apply HP.
  - unfold ncarved. cbn [s_metas minit]. rewrite map_to_list_empty. pose proof (NCAP_lower P HP). unfold zlen. cbn. lia.
  - exact HP0.
Qed.

#[using="Type"] Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem QI_init {St : Type} {AS : AllocSt St} : forall P segs brk0 mbase sp lim inp secret (s0 : St),
  ps_m s0 = strip (minit secret (reservedZ segs)) -> ps_brk s0 = 0 -> 0 <= secret < 2^64 ->
  fs_keys_relative (in_image_fs inp) ->    (* [comment removed for export] *)
  alloc_ceiling = page_round_down_Z (alloc_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))) ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  (* [comment removed for export] *)
  reserved_top (segments_reserved segs) + brk_aslr_max + 2 * PGSZ + BLIVE <= bottomup_floor -> BLIVE + RMAX <= lim ->
  (forall c, 0 <= P c <= PMAX) -> PHI P <= LBUDGET ->
  QI [] P s0 (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros P segs brk0 mbase sp lim inp secret s0 Hm0 Hb0 Hsec Hvfs Htop (Hlo & Hhi & Hal) Hpos Hceil Hfloor Hlim HP HPHI. split; [| unfold R63X, zsum; cbn; lia].
  rewrite Hm0, Hb0.
  exists (minit secret (reservedZ segs)), (led_init (reservedZ segs)), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; exact Hsec|]. split; [apply SINV_minit|]. split; [apply AQ_minit; exact HP|].
  split; [| split; [| apply Permutation_refl]].
  - constructor; try exact Htop; rewrite ?m_vmmaps_init_model, ?m_halted_init_model; cbn -[Z.pow Z.mul Z.add init_model].
    + apply minv_init. exact Hvfs.
    + reflexivity.
    + split; [intros e []| apply pwdisj_nil].
    + intros r Hr. unfold reservedZ in Hr. apply in_map_iff in Hr as (e & <- & He). exists e.
      split; [unfold elo; cbn; lia|]. split; [unfold ehi; cbn; lia|]. left. exact He.
    + intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
    + unfold PGSZ in *. unfold page_size in Hal. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + split; reflexivity.
    + intros e [].
    + intros b l H. discriminate.
    + unfold PGSZ. lia.
    + unfold PGSZ in *. lia.
    + intros b l [[]|[k []]].
    + intros e [].
  - unfold LI, gm, BB, PINB, PGSZ. rewrite m_vmmaps_init_model. cbn. lia.
Qed.

End WithCeil.
End LB_Init.

(* [comment removed for export] *)
Module LB_Alloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic LB_Inv LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Logic OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Raw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Init.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
Section LBAlloc.
Context {St : Type} {AS : AllocSt St}.
Definition raw_malloc_LQ := raw_malloc_L malloc_core_fq_proof.
Definition raw_free_LQ := @raw_free_L _ St AS.

Check (raw_malloc_LQ : forall X P n, 0 <= n -> bigb n <= QMAX ->
  mspecL LBUDGET (fun s mo => QI X P s mo /\ ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
                        | None => QI X P s mo
                        end)).
Check (raw_free_LQ : forall X P p n, mspecL LBUDGET (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P)).
End LBAlloc.

End WithCeil.
End LB_Alloc.
