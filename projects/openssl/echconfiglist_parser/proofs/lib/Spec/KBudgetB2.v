(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4 MI_Cnt KLink KBudgetB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sumw {A} (w : A -> Z) (l : list A) : Z := fold_right (fun x acc => w x + acc) 0 l.
Lemma sumw_cons {A} (w : A -> Z) x l : sumw w (x :: l) = w x + sumw w l. Proof. reflexivity. Qed.
Lemma sumw_nil {A} (w : A -> Z) : sumw w [] = 0. Proof. reflexivity. Qed.
Arguments sumw {A} w l : simpl never.

Lemma sumw_app {A} (w : A -> Z) l k : sumw w (l ++ k) = sumw w l + sumw w k.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [app]. rewrite !sumw_cons, IH. lia. Qed.

Lemma sumw_perm {A} (w : A -> Z) l k : Permutation l k -> sumw w l = sumw w k.
Proof. induction 1; rewrite ?sumw_cons in *; try lia. Qed.

Lemma sumw_nonneg {A} (w : A -> Z) l : (forall x, In x l -> 0 <= w x) -> 0 <= sumw w l.
Proof. induction l as [|x l IH]; intros H; [rewrite sumw_nil; lia|]. rewrite sumw_cons. pose proof (H x ltac:(left; reflexivity)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.

Lemma sumw_le {A} (w v : A -> Z) l : (forall x, In x l -> w x <= v x) -> sumw w l <= sumw v l.
Proof. induction l as [|x l IH]; intros H; [rewrite !sumw_nil; lia|]. rewrite !sumw_cons. pose proof (H x ltac:(left; reflexivity)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.

Lemma sumw_const {A} (c : Z) (l : list A) : sumw (fun _ => c) l = Z.of_nat (length l) * c.
Proof. induction l as [|x l IH]; [rewrite sumw_nil; cbn; lia|]. rewrite sumw_cons, IH. cbn [length]. rewrite Nat2Z.inj_succ. lia. Qed.

Lemma sumw_map {A B} (f : A -> B) (w : B -> Z) l : sumw w (map f l) = sumw (fun x => w (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !sumw_cons, IH. reflexivity. Qed.

Lemma sumw_add {A} (w v : A -> Z) l : sumw (fun x => w x + v x) l = sumw w l + sumw v l.
Proof. induction l as [|x l IH]; [rewrite !sumw_nil; lia|]. rewrite !sumw_cons, IH. lia. Qed.

Lemma sumw_ext {A} (w v : A -> Z) l : (forall x, In x l -> w x = v x) -> sumw w l = sumw v l.
Proof. intros H. pose proof (sumw_le w v l ltac:(intros x Hx; rewrite (H x Hx); lia)). pose proof (sumw_le v w l ltac:(intros x Hx; rewrite (H x Hx); lia)). lia. Qed.

(* [comment removed for export] *)
Lemma sumw_sub {A} (w : A -> Z) (l k : list A) :
  List.NoDup l -> (forall x, In x l -> In x k) -> (forall x, In x k -> 0 <= w x) -> sumw w l <= sumw w k.
Proof.
  revert k. induction l as [|x l IH]; intros k ND SUB POS.
  - rewrite sumw_nil. apply sumw_nonneg. exact POS.
  - apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (in_split x k (SUB x ltac:(left; reflexivity))) as (k1 & k2 & ->).
    rewrite sumw_app, !sumw_cons. pose proof (IH (k1 ++ k2) ND) as H. rewrite sumw_app in H.
    assert (S' : forall y, In y l -> In y (k1 ++ k2)).
    { intros y Hy. pose proof (SUB y ltac:(right; exact Hy)) as K. apply in_app_iff in K. apply in_app_iff.
      destruct K as [K|[<-|K]]; [left; exact K| exfalso; exact (NI Hy)| right; exact K]. }
    specialize (H S' ltac:(intros y Hy; apply POS; apply in_app_iff in Hy; apply in_app_iff; cbn; tauto)). lia.
Qed.

Lemma sum_glen_sumw l : sum_glen l = sumw (fun g => mmap_len (snd g)) l.
Proof. reflexivity. Qed.
Lemma sum_mlen_sumw l : sum_mlen l = sumw (fun m => mmap_len (snd (fst m))) l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_groupb (r : region) : bool := match r_kind r with RKGroup => true | _ => false end.
Definition is_metab (r : region) : bool := match r_kind r with RKMeta => true | _ => false end.
Definition is_brkb (r : region) : bool := match r_kind r with RKBrk => true | _ => false end.
Definition RG (st : mstate) : list (N * region) := List.filter (fun kr => is_groupb (snd kr)) (map_to_list (s_regions st)).
Definition RM (st : mstate) : list (N * region) := List.filter (fun kr => is_metab (snd kr)) (map_to_list (s_regions st)).
Definition RB (st : mstate) : list (N * region) := List.filter (fun kr => is_brkb (snd kr)) (map_to_list (s_regions st)).

Lemma In_RG st rid r : In (rid, r) (RG st) <-> s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Proof.
  unfold RG. rewrite filter_In. cbn. unfold is_groupb. split.
  - intros [Hin K]. split; [apply elem_of_map_to_list; apply list_elem_of_In; exact Hin| destruct (r_kind r); congruence].
  - intros [H K]. rewrite K. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact H| reflexivity].
Qed.
Lemma In_RM st rid r : In (rid, r) (RM st) <-> s_regions st !! rid = Some r /\ r_kind r = RKMeta.
Proof.
  unfold RM. rewrite filter_In. cbn. unfold is_metab. split.
  - intros [Hin K]. split; [apply elem_of_map_to_list; apply list_elem_of_In; exact Hin| destruct (r_kind r); congruence].
  - intros [H K]. rewrite K. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact H| reflexivity].
Qed.
Lemma In_RB st rid r : In (rid, r) (RB st) <-> s_regions st !! rid = Some r /\ r_kind r = RKBrk.
Proof.
  unfold RB. rewrite filter_In. cbn. unfold is_brkb. split.
  - intros [Hin K]. split; [apply elem_of_map_to_list; apply list_elem_of_In; exact Hin| destruct (r_kind r); congruence].
  - intros [H K]. rewrite K. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact H| reflexivity].
Qed.

Lemma filter_nodup_fst {K V} (f : K * V -> bool) (l : list (K * V)) : List.NoDup (map fst l) -> List.NoDup (map fst (List.filter f l)).
Proof.
  induction l as [|[k v] l IH]; cbn; intros ND; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct (f (k, v)); cbn; [| apply IH; exact ND]. apply List.NoDup_cons; [| apply IH; exact ND].
  intros Hin. apply NI. apply in_map_iff in Hin as ([k' v'] & E & Hin). apply filter_In in Hin as [Hin _]. apply in_map_iff. exists (k', v'). auto.
Qed.
Lemma RG_nodup st : List.NoDup (map fst (RG st)). Proof. apply filter_nodup_fst. apply keys_nodup. Qed.
Lemma RM_nodup st : List.NoDup (map fst (RM st)). Proof. apply filter_nodup_fst. apply keys_nodup. Qed.
Lemma NoDup_of_fst {K V} (l : list (K * V)) : List.NoDup (map fst l) -> List.NoDup l.
Proof.
  induction l as [|[k v] l IH]; cbn; intros ND; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  apply List.NoDup_cons; [| apply IH; exact ND]. intros Hin. apply NI. apply in_map_iff. exists (k, v). auto.
Qed.

(* [comment removed for export] *)
Lemma length_kinds st : (length (RG st) + length (RM st) + length (RB st) <= size (s_regions st))%nat.
Proof.
  unfold RG, RM, RB. rewrite <- (length_map_to_list (s_regions st)). induction (map_to_list (s_regions st)) as [|[k r] l IH]; [cbn; lia|].
  cbn [List.filter snd]. destruct (is_groupb r) eqn:E1; destruct (is_metab r) eqn:E2; destruct (is_brkb r) eqn:E3; cbn [length] in *; try lia;
    unfold is_groupb, is_metab, is_brkb in E1, E2, E3; destruct (r_kind r); discriminate.
Qed.

(* [comment removed for export] *)
Fixpoint omapl {A B} (f : A -> option B) (l : list A) : list B :=
  match l with [] => [] | x :: l' => match f x with Some b => b :: omapl f l' | None => omapl f l' end end.
Lemma In_omapl {A B} (f : A -> option B) l b : In b (omapl f l) <-> exists x, In x l /\ f x = Some b.
Proof.
  induction l as [|x l IH]; cbn; [split; [intros []| intros (x & [] & _)]|].
  destruct (f x) as [b0|] eqn:E; cbn; rewrite IH; split.
  - intros [<-|(y & Hy & Ey)]; [exists x; auto| exists y; auto].
  - intros (y & [<-|Hy] & Ey); [left; congruence| right; exists y; auto].
  - intros (y & Hy & Ey); exists y; auto.
  - intros (y & [<-|Hy] & Ey); [congruence| exists y; auto].
Qed.
Lemma sumw_omapl {A B} (f : A -> option B) (w : B -> Z) l :
  sumw (fun x => match f x with Some b => w b | None => 0 end) l = sumw w (omapl f l).
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [omapl]. rewrite sumw_cons, IH. destruct (f x); [rewrite sumw_cons; reflexivity| lia]. Qed.
Lemma NoDup_omapl {A B} (f : A -> option B) l :
  List.NoDup l -> (forall x y b, In x l -> In y l -> f x = Some b -> f y = Some b -> x = y) -> List.NoDup (omapl f l).
Proof.
  induction l as [|x l IH]; cbn; intros ND INJ; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  assert (IH' : List.NoDup (omapl f l)) by (apply IH; [exact ND| intros; eapply INJ; eauto]).
  destruct (f x) as [b|] eqn:E; [| exact IH']. apply List.NoDup_cons; [| exact IH'].
  intros Hin. apply In_omapl in Hin as (y & Hy & Ey). pose proof (INJ x y b ltac:(auto) ltac:(auto) E Ey) as <-. exact (NI Hy).
Qed.
Lemma NoDup_map_inj {A B} (f : A -> B) l x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; cbn; intros ND Hx Hy E; [destruct Hx|]. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | exact (IH ND Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
Definition zrange (a : Z) (n : nat) : list Z := map (fun z => a + z) (zseq n).
Lemma In_zrange a n z : In z (zrange a n) <-> a <= z < a + Z.of_nat n.
Proof. unfold zrange. rewrite in_map_iff. split; [intros (y & <- & Hy); apply In_zseq in Hy; lia| intros H; exists (z - a); split; [lia| apply In_zseq; lia]]. Qed.
Lemma zrange_nodup a n : List.NoDup (zrange a n).
Proof. unfold zrange. apply Finite.Injective_map_NoDup_in; [intros x y _ _ E; lia| apply zseq_nodup]. Qed.
Lemma zrange_length a n : length (zrange a n) = n.
Proof. unfold zrange. rewrite map_length. apply zseq_length. Qed.
Lemma geo_sum s : 0 <= s -> sumw (fun j => 2^j) (zrange 1 (Z.to_nat s)) = 2^(s+1) - 2.
Proof.
  intros Hs. rewrite <- (Z2Nat.id s) at 2 by lia. generalize (Z.to_nat s). clear s Hs. intros n.
  unfold zrange, zseq. induction n as [|n IH]; [reflexivity|].
  rewrite seq_S, !map_app, sumw_app, IH. cbn [map]. rewrite sumw_cons, sumw_nil, Nat2Z.inj_succ.
  rewrite Nat.add_0_l. replace (1 + Z.of_nat n) with (Z.succ (Z.of_nat n)) by lia. rewrite !Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FOOT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HXO : x_orph X = None.
Hypothesis HXP : x_pend X = None.
Hypothesis HXF : x_fresh X = None.
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Local Notation R := (MR st).
Local Notation cx := (s_ctx st).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma up_base0 rid : up st (rid, 0) = None.
Proof.
  unfold up. destruct (_ !! _) as [[p i]|] eqn:E; [| reflexivity]. exfalso.
  destruct (is_valid _ _ _ IS _ _ _ E) as ((b & Hb) & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. injection Es as _ Eo.
  pose proof (sstart_mono _ _ _ IG _ _ 0 i Hb ltac:(lia)). rewrite (sstart0 _ _ _ IM _ _ Hb) in H.
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
Qed.

Lemma ups_last x n b d : In b (ups st x n) -> up st b = None -> b = List.last (ups st x n) d.
Proof.
  revert x. induction n as [|n IH]; intros x Hin U; [destruct Hin|].
  cbn in Hin |- *. destruct (up st x) as [b0|]; [| destruct Hin]. destruct Hin as [<-|Hin].
  - destruct n; cbn; [reflexivity|]. rewrite U. reflexivity.
  - pose proof (IH b0 Hin U) as E. destruct (ups st b0 n) as [|y l] eqn:El; [destruct Hin| exact E].
Qed.

Definition roots : list aptr := map (fun kr => (fst kr, 0)) (RG st).

Lemma roots_nodup : List.NoDup roots.
Proof.
  unfold roots. pose proof (RG_nodup st) as ND. remember (RG st) as l eqn:El. clear El.
  induction l as [|[k r] l IH]; cbn; [constructor|]. cbn in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  apply List.NoDup_cons; [| apply IH; exact ND]. intros Hin. apply NI. apply in_map_iff in Hin as ([k' r'] & E & Hin). cbn in E. injection E as ->.
  apply in_map_iff. exists (k, r'). auto.
Qed.

Lemma roots_top b : In b roots -> exists m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ m_maplen (R m) <> 0 /\ snd b = 0.
Proof.
  intros Hin. unfold roots in Hin. apply in_map_iff in Hin as ([rid r] & <- & Hin). apply In_RG in Hin as [Hr K].
  destruct (ig_top _ _ _ IG rid r Hr K ltac:(rewrite HXO; discriminate)) as (m & [ai Hb] & ML).
  exists m, ai. cbn. auto.
Qed.

Lemma RG_length : (length (RG st) <= 48 + (length BL + 1 + 48))%nat.
Proof.
  replace (length (RG st)) with (length roots) by (unfold roots; apply map_length).
  pose proof (AF_length X st L BL LS INV) as AFL.
  eapply Nat.le_trans; [apply (count_incl roots (AF st ++ map (fun l => List.last (ups st l DEPTH) l) (leaves X st BL))); [apply roots_nodup|]|].
  - intros b Hb. destruct (roots_top b Hb) as (m & ai & Hg & ML & B0). apply in_app_iff.
    destruct (group_cover_n X st L BL LS INV 48 b m ai Hg ltac:(intros; lia)) as [A|(l & k & Hl & Hk & Hin)]; [left; exact A| right].
    apply in_map_iff. exists l. split; [| exact Hl]. symmetry. apply ups_last; [eapply ups_mono; [| exact Hin]; unfold DEPTH; lia|].
    destruct b as [rid o]. cbn in B0. subst o. apply up_base0.
  - rewrite app_length, map_length. unfold leaves. rewrite !app_length, map_length.
    assert (PL : (length (pend_list X) <= 1)%nat) by (unfold pend_list; destruct (x_pend X); cbn; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition topclass (kr : N * region) : Z :=
  match s_groups st !! (fst kr, 0) with Some (mkGhdr (Some m) _) => m_sizeclass (R m) | _ => 0 end.
Definition heavyb (kr : N * region) : bool := 27 <=? topclass kr.
Definition bigb (k : blk) : bool := 2028 <? bsize k.
Definition nbig : Z := Z.of_nat (length (List.filter bigb BL)).

Lemma up_inv x b : up st x = Some b -> exists p i, s_slots st !! x = Some (p, i) /\ hosts st b p.
Proof.
  intros U. pose proof U as U0. unfold up in U. destruct (s_slots st !! x) as [[p i]|] eqn:Hs; [| discriminate].
  exists p, i. split; [reflexivity|]. destruct (up_slot X st L BL LS INV x p i Hs) as (bp & Hp & U2).
  rewrite U0 in U2. injection U2 as ->. exact Hp.
Qed.

Lemma hosts_fun b m1 m2 : hosts st b m1 -> hosts st b m2 -> m1 = m2.
Proof. intros [a1 H1] [a2 H2]. rewrite H1 in H2. injection H2 as -> _. reflexivity. Qed.

(* [comment removed for export] *)
Lemma heavy_no_nest x px m i : hosts st x px -> s_slots st !! x = Some (m, i) -> 27 <= m_sizeclass (R m) -> False.
Proof.
  intros [aix Hx] Hs H27.
  pose proof (ig_ok _ _ _ IG _ _ _ Hx) as GO'.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hbm] & Hi & Es).
  destruct (Z.eq_dec (m_maplen (R px)) 0) as [ML|ML].
  - destruct (g_nest _ _ _ _ _ _ GO' ML) as (p & i' & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-. lia.
  - destruct (g_top _ _ _ _ _ _ GO' ML) as [Z0 _].
    rewrite (slot_start'_eq _ _ _ IM _ _ i Hbm) in Es. subst x. cbn in Z0.
    pose proof (sstart0 _ _ _ IM _ _ Hbm). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hbm ltac:(lia)).
    destruct (hosts_ok _ _ _ IG _ _ Hbm) as (ai0 & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
Qed.

Lemma ups_in l k b : In b (ups st l k) -> up st l = Some b \/ exists x, In x (ups st l k) /\ up st x = Some b.
Proof.
  revert l. induction k as [|k IH]; intros l Hin; [destruct Hin|].
  cbn in Hin |- *. destruct (up st l) as [b0|] eqn:U; [| destruct Hin].
  destruct Hin as [->|Hin]; [left; reflexivity|].
  right. destruct (IH b0 Hin) as [U0|(x & Hx & Ux)]; [exists b0; split; [left; reflexivity| exact U0]| exists x; split; [right; exact Hx| exact Ux]].
Qed.

Lemma ups_hosted l k x : In x (ups st l k) -> exists p, hosts st x p.
Proof.
  revert l. induction k as [|k IH]; intros l Hin; [destruct Hin|].
  cbn in Hin. destruct (up st l) as [b0|] eqn:U; [| destruct Hin].
  destruct Hin as [<-|Hin]; [| exact (IH b0 Hin)].
  destruct (up_inv l b0 U) as (p & i & _ & Hp). exists p. exact Hp.
Qed.

Lemma heavy_root_cover kr : In kr (RG st) -> heavyb kr = true ->
  In (fst kr, 0) (AF st) \/ exists k, In k BL /\ bigb k = true /\ fst (bslot k) = fst kr.
Proof.
  intros Hin HV. set (b := (fst kr, 0)).
  assert (Hroot : In b roots) by (unfold roots; apply in_map_iff; exists kr; split; [reflexivity| exact Hin]).
  destruct (roots_top b Hroot) as (m & ai & Hg & ML & B0).
  assert (H27 : 27 <= m_sizeclass (R m)).
  { unfold heavyb, topclass in HV. fold b in HV. rewrite Hg in HV. apply Z.leb_le in HV. exact HV. }
  destruct (group_cover_n X st L BL LS INV 48 b m ai Hg ltac:(intros; lia)) as [A|(l & k & Hl & Hk & Hinb)]; [left; exact A| right].
  assert (Hbm : hosts st b m) by (exists ai; exact Hg).
  (* [comment removed for export] *)
  assert (U1 : up st l = Some b).
  { destruct (ups_in l k b Hinb) as [U|(x & Hx & Ux)]; [exact U| exfalso].
    destruct (ups_hosted l k x Hx) as (px & Hpx). destruct (up_inv x b Ux) as (p & i & Hs & Hp).
    pose proof (hosts_fun b p m Hp Hbm) as ->. exact (heavy_no_nest x px m i Hpx Hs H27). }
  destruct (up_inv l b U1) as (p & i & Hs & Hp). pose proof (hosts_fun b p m Hp Hbm) as ->.
  unfold leaves in Hl. rewrite !in_app_iff in Hl. destruct Hl as [Hl|[Hl|Hl]].
  - apply in_map_iff in Hl as (k0 & <- & Hk0). exists k0. split; [exact Hk0|]. split.
    + unfold bigb. apply Z.ltb_lt. exact (is_cls _ _ _ IS k0 m i Hk0 Hs H27).
    + destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & Es). rewrite (slot_start'_eq _ _ _ IM _ _ i Hbm) in Es. rewrite Es. reflexivity.
  - exfalso. unfold pend_list in Hl. rewrite HXP in Hl. destruct Hl.
  - exfalso. unfold AF, af_list in Hl. apply in_map_iff in Hl as ([l' h] & E & Hf). cbn [fst] in E. subst l'. apply filter_In in Hf as [Hf _].
    assert (Hgl : s_groups st !! l = Some h) by (apply elem_of_map_to_list; apply list_elem_of_In; exact Hf).
    destruct h as [[pl|] ail]; [| exact (ig_nometa _ _ _ IG _ _ Hgl)].
    exact (heavy_no_nest l pl m i (ex_intro _ ail Hgl) Hs H27).
Qed.

Lemma NoDup_map_filter {A B} (f : A -> B) (g : A -> bool) l : List.NoDup (map f l) -> List.NoDup (map f (List.filter g l)).
Proof.
  induction l as [|x l IH]; cbn; intros ND; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct (g x); cbn; [| apply IH; exact ND]. apply List.NoDup_cons; [| apply IH; exact ND].
  intros Hin. apply NI. apply in_map_iff in Hin as (y & E & Hy). apply filter_In in Hy as [Hy _]. apply in_map_iff. exists y. auto.
Qed.

Lemma heavy_length : (length (List.filter heavyb (RG st)) <= 48 + length (List.filter bigb BL))%nat.
Proof.
  pose proof (AF_length X st L BL LS INV) as AFL.
  assert (H : (length (map (fun kr : N * region => (fst kr, 0%Z)) (List.filter heavyb (RG st)))
               <= length (AF st ++ map (fun k => (fst (bslot k), 0%Z)) (List.filter bigb BL)))%nat).
  { apply count_incl.
    - apply NoDup_map_filter. exact roots_nodup.
    - intros b Hb. apply in_map_iff in Hb as (kr & <- & Hkr). apply filter_In in Hkr as [Hin HV].
      apply in_app_iff. destruct (heavy_root_cover kr Hin HV) as [A|(k & Hk & Bk & Ek)]; [left; exact A| right].
      apply in_map_iff. exists k. split; [rewrite Ek; reflexivity| apply filter_In; auto]. }
  rewrite app_length, !map_length in H. unfold AF in AFL. rewrite ?map_length in AFL. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma big_slot_block b m : hosts st b m -> m_sizeclass (R m) = 63 -> In (slot_start' (R m) 0) (map bslot BL).
Proof.
  intros Hb S63. destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & Hg & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[[_ S48] _]|(_ & L0 & ML & _)]; [lia|].
  destruct (g_big0 _ _ _ _ _ _ GO S63) as [A0 F0].
  pose proof (is_part _ _ _ IS b m ai 0 Hg ltac:(rewrite L0; lia)) as P. cbn zeta in P.
  unfold one5, tbit in P. rewrite A0, F0, !Z.bits_0, HXP in P. destruct P as (P & _).
  set (s := slot_start' (R m) 0) in *.
  assert (Hs : s_slots st !! s = Some (m, 0)) by (apply (is_total _ _ _ IS b); [exact Hb| rewrite L0; lia]).
  destruct P as [E|[E|[U|[NG|PE]]]]; [discriminate| discriminate| exact U| | discriminate].
  exfalso. destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs'; [| exact (ig_nometa _ _ _ IG _ _ Hs')| exact (NG eq_refl)].
  pose proof (ig_ok _ _ _ IG _ _ _ Hs') as GO'.
  destruct (Z.eq_dec (m_maplen (R m')) 0) as [ML'|ML'].
  - destruct (g_nest _ _ _ _ _ _ GO' ML') as (p & i & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-. lia.
  - destruct (g_top _ _ _ _ _ _ GO' ML') as [Z0 _].
    subst s. rewrite (slot_start'_eq _ _ _ IM _ _ 0 Hb) in Z0. cbn in Z0. rewrite (sstart0 _ _ _ IM _ _ Hb) in Z0.
    pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Definition bigblk (kr : N * region) : option blk :=
  match s_groups st !! (fst kr, 0) with
  | Some (mkGhdr (Some m) _) =>
      if m_sizeclass (R m) =? 63 then List.find (fun k => aptr_eqb (bslot k) (slot_start' (R m) 0)) BL else None
  | _ => None
  end.

Lemma bigblk_some kr k : bigblk kr = Some k -> In k BL /\ fst (bslot k) = fst kr.
Proof.
  unfold bigblk. intros H. destruct (s_groups st !! (fst kr, 0)) as [[[m|] ai]|] eqn:Hg; try discriminate.
  destruct (Z.eqb_spec (m_sizeclass (R m)) 63) as [S63|]; [| discriminate].
  apply find_some in H as [Hin E]. destruct (aptr_eqb_spec (bslot k) (slot_start' (R m) 0)) as [E2|]; [| discriminate].
  split; [exact Hin|]. rewrite E2, (slot_start'_eq _ _ _ IM _ (fst kr, 0) 0 (ex_intro _ ai Hg)). reflexivity.
Qed.

Lemma RG_cost1 kr : In kr (RG st) ->
  mmap_len (r_len (snd kr)) <= 2^16 + (if heavyb kr then 2^20 else 0) + match bigblk kr with Some k => bsize k | None => 0 end.
Proof.
  intros Hin. destruct kr as [rid r]. apply In_RG in Hin as [Hr K]. cbn [fst snd].
  destruct (ig_top _ _ _ IG rid r Hr K ltac:(rewrite HXO; discriminate)) as (m & Hb & ML).
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & Hg & GO). unfold bigblk, heavyb, topclass. cbn [fst]. rewrite Hg.
  destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r' & Hr' & _ & EQ & _). cbn in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
  rewrite mmap_len_round_up.
  destruct (g_sc _ _ _ _ _ _ GO) as [[[S0 S48] M256]|(S63 & L0 & _ & _)].
  - replace (m_sizeclass (R m) =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- EQ.
    destruct (Z.leb_spec 27 (m_sizeclass (R m))) as [H27|H26]; [lia|].
    pose proof (g_small _ _ _ _ _ _ GO ltac:(lia)) as M16. change (2^16) with 65536. lia.
  - rewrite S63. cbn [Z.eqb Pos.eqb]. change (27 <=? 63) with true. cbn iota.
    pose proof (big_slot_block _ _ Hb S63) as HB.
    destruct (List.find _ BL) as [k|] eqn:F.
    + apply find_some in F as [Hk E]. destruct (aptr_eqb_spec (bslot k) (slot_start' (R m) 0)) as [E2|]; [| discriminate].
      assert (Hs : s_slots st !! (bslot k) = Some (m, 0)) by (rewrite E2; apply (is_total _ _ _ IS _ _ _ Hb); rewrite L0; lia).
      destruct (is_big _ _ _ IS k m 0 Hk Hs S63) as (r2 & Hr2 & _ & LEN).
      rewrite E2, (slot_start'_eq _ _ _ IM _ _ 0 Hb) in Hr2. cbn in Hr2. rewrite Hr in Hr2. injection Hr2 as <-.
      rewrite LEN. destruct (is_blocks _ _ _ IS k Hk) as (_ & _ & _ & _ & B0 & _).
      pose proof (MI_Cnt.round_up_pg_spec (bsize k + IB + UNIT)) as [RS _]. unfold IB, UNIT in *. lia.
    + exfalso. apply in_map_iff in HB as (k & Ek & Hk). pose proof (find_none _ _ F k Hk) as NF. cbn in NF.
      rewrite Ek, aptr_eqb_refl in NF. discriminate.
Qed.

Lemma sumw_if {A} (f : A -> bool) (c : Z) l : sumw (fun x => if f x then c else 0) l = Z.of_nat (length (List.filter f l)) * c.
Proof.
  induction l as [|x l IH]; [rewrite sumw_nil; cbn; lia|]. rewrite sumw_cons, IH. cbn [List.filter].
  destruct (f x); cbn [length]; [rewrite Nat2Z.inj_succ|]; lia.
Qed.

Lemma RG_cost : sumw (fun kr => mmap_len (r_len (snd kr))) (RG st)
  <= Z.of_nat (length (RG st)) * 2^16 + Z.of_nat (length (List.filter heavyb (RG st))) * 2^20 + sumw bsize BL.
Proof.
  eapply Z.le_trans; [apply sumw_le; intros kr Hkr; apply (RG_cost1 kr Hkr)|].
  rewrite (sumw_add (fun kr => 2^16 + (if heavyb kr then 2^20 else 0)) (fun kr => match bigblk kr with Some k => bsize k | None => 0 end)).
  rewrite (sumw_add (fun _ => 2^16) (fun kr => if heavyb kr then 2^20 else 0)).
  rewrite sumw_const, sumw_if, sumw_omapl. apply Zplus_le_compat_l.
  apply sumw_sub.
  - apply NoDup_omapl; [apply NoDup_of_fst; apply RG_nodup|].
    intros x y b Hx Hy Fx Fy. apply (NoDup_map_inj fst (RG st) x y (RG_nodup st) Hx Hy).
    destruct (bigblk_some _ _ Fx) as [_ <-]. destruct (bigblk_some _ _ Fy) as [_ <-]. reflexivity.
  - intros k Hk. apply In_omapl in Hk as (kr & _ & F). exact (proj1 (bigblk_some _ _ F)).
  - intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (_ & _ & _ & _ & B0 & _). exact B0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pages_areas rid r K : s_regions st !! rid = Some r -> is_metakind r -> 0 <= K -> (K + 1) * PGSZ <= frontier st rid r ->
  K <= Z.of_nat (size (s_areas st)).
Proof.
  intros Hr MK K0 FR.
  pose proof (size_ge_sub (s_areas st) (map (fun q => (rid, q * PGSZ)) (zrange 1 (Z.to_nat K)))) as H.
  rewrite map_length, zrange_length in H.
  enough (HH : (Z.to_nat K <= size (s_areas st))%nat) by lia. apply H.
  - apply Finite.Injective_map_NoDup_in; [| apply zrange_nodup]. intros x y _ _ E. injection E as E. unfold PGSZ in E. lia.
  - intros a Ha. apply in_map_iff in Ha as (q & <- & Hq). apply In_zrange in Hq. rewrite Z2Nat.id in Hq by lia.
    apply (ir_pages _ _ _ IR rid r q Hr MK); [lia| unfold PGSZ in *; lia| rewrite HXF; discriminate].
Qed.

Lemma frontier_other rid r : (forall off, c_avail_meta_areas cx <> Some (rid, off)) -> frontier st rid r = r_len r.
Proof.
  intros NC. unfold frontier. destruct (c_avail_meta_areas cx) as [[rid0 off0]|] eqn:E; [| reflexivity].
  destruct (N.eqb_spec rid0 rid) as [->|]; [| reflexivity]. exfalso. exact (NC off0 eq_refl).
Qed.

(* [comment removed for export] *)
Lemma meta_full_areas rid r j : s_regions st !! rid = Some r -> r_kind r = RKMeta -> 0 <= j -> r_len r = 2^j * PGSZ ->
  (forall off, c_avail_meta_areas cx <> Some (rid, off)) -> 2^j - 1 <= Z.of_nat (size (s_areas st)).
Proof.
  intros Hr K Hj LEN NC. apply (pages_areas rid r); [exact Hr| right; exact K| pose proof (Z.pow_pos_nonneg 2 j); lia|].
  rewrite (frontier_other rid r NC), LEN. lia.
Qed.

(* [comment removed for export] *)
Lemma shift_areas : 2^(c_meta_alloc_shift cx - 1) - 1 <= Z.of_nat (size (s_areas st)).
Proof.
  pose proof (ir_shift _ _ _ IR) as [S0 _]. pose proof (ir_mshift _ _ _ IR) as (MA & MB & MC).
  set (sh := c_meta_alloc_shift cx) in *.
  destruct (Z.le_gt_cases sh 1) as [LE|GT].
  { assert (2^(sh - 1) <= 1); [| lia]. destruct (Z.eq_dec sh 1) as [->|NE]; [cbn; lia|]. rewrite Z.pow_neg_r by lia. lia. }
  destruct (MC sh ltac:(lia)) as (ridA & rA & HrA & KA & LA).
  destruct (MC (sh - 1) ltac:(lia)) as (ridB & rB & HrB & KB & LB).
  assert (NAB : ridA <> ridB).
  { intros ->. rewrite HrA in HrB. injection HrB as ->. rewrite LB in LA.
    replace sh with (Z.succ (sh - 1)) in LA at 2 by lia. rewrite Z.pow_succ_r in LA by lia. pose proof (Z.pow_pos_nonneg 2 (sh - 1)). unfold PGSZ in *. lia. }
  destruct (c_avail_meta_areas cx) as [[rid0 off0]|] eqn:EC.
  - destruct (N.eq_dec rid0 ridA) as [->|NE].
    + apply (meta_full_areas ridB rB (sh - 1) HrB KB ltac:(lia) LB). intros off E. rewrite EC in E. injection E as E _. exact (NAB E).
    + eapply Z.le_trans; [| apply (meta_full_areas ridA rA sh HrA KA ltac:(lia) LA); intros off E; rewrite EC in E; injection E as E _; exact (NE E)].
      replace sh with (Z.succ (sh - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. pose proof (Z.pow_pos_nonneg 2 (sh - 1)). lia.
  - eapply Z.le_trans; [| apply (meta_full_areas ridA rA sh HrA KA ltac:(lia) LA); intros off E; rewrite EC in E; discriminate].
    replace sh with (Z.succ (sh - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. pose proof (Z.pow_pos_nonneg 2 (sh - 1)). lia.
Qed.

(* [comment removed for export] *)
Lemma brk_len rid r : s_regions st !! rid = Some r -> r_kind r = RKBrk ->
  r_len r mod PGSZ = 0 /\ 2 * PGSZ <= r_len r /\ r_len r / PGSZ - 1 <= Z.of_nat (size (s_areas st)).
Proof.
  intros Hr K. destruct (ir_shape _ _ _ IR rid r Hr) as (_ & _ & _ & _ & _ & MK). specialize (MK ltac:(left; exact K)) as [MOD TWO].
  split; [exact MOD|]. split; [exact TWO|].
  apply (pages_areas rid r); [exact Hr| left; exact K| unfold PGSZ in *; Z.div_mod_to_equations; lia|].
  rewrite (ir_brkfront _ _ _ IR rid r Hr K). unfold PGSZ in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition jof (kr : N * region) : Z := Z.log2 (r_len (snd kr) / PGSZ).

Lemma RM_j kr : In kr (RM st) -> 1 <= jof kr <= c_meta_alloc_shift cx /\ r_len (snd kr) = 2^(jof kr) * PGSZ.
Proof.
  intros Hin. destruct kr as [rid r]. apply In_RM in Hin as [Hr K]. pose proof (ir_mshift _ _ _ IR) as (MA & _ & _).
  destruct (MA rid r Hr K) as (j & Hj & LEN). unfold jof. cbn [snd]. rewrite LEN. unfold PGSZ.
  rewrite Z.div_mul, Z.log2_pow2 by lia. split; [exact Hj| reflexivity].
Qed.

Lemma RM_j_nodup : List.NoDup (map jof (RM st)).
Proof.
  apply Finite.Injective_map_NoDup_in; [| apply NoDup_of_fst; apply RM_nodup].
  intros x y Hx Hy E. apply (NoDup_map_inj fst (RM st) x y (RM_nodup st) Hx Hy).
  destruct (RM_j x Hx) as [_ LX]. destruct (RM_j y Hy) as [_ LY]. rewrite E in LX. rewrite <- LY in LX.
  destruct x as [rx x'], y as [ry y']. cbn in LX |- *. apply In_RM in Hx as [Hx Kx]. apply In_RM in Hy as [Hy Ky].
  pose proof (ir_mshift _ _ _ IR) as (_ & MB & _). exact (MB rx ry x' y' Hx Hy Kx Ky LX).
Qed.

Lemma RM_length : Z.of_nat (length (RM st)) <= c_meta_alloc_shift cx.
Proof.
  pose proof (ir_shift _ _ _ IR) as [S0 _].
  pose proof (count_incl (map jof (RM st)) (zrange 1 (Z.to_nat (c_meta_alloc_shift cx))) RM_j_nodup) as H.
  rewrite map_length, zrange_length in H. enough ((length (RM st) <= Z.to_nat (c_meta_alloc_shift cx))%nat) by lia.
  apply H. intros j Hj. apply in_map_iff in Hj as (kr & <- & Hkr). apply In_zrange. pose proof (RM_j kr Hkr) as [B _]. lia.
Qed.

Lemma sumw_scale {A} (c : Z) (w : A -> Z) l : sumw (fun x => w x * c) l = sumw w l * c.
Proof. induction l as [|x l IH]; [rewrite !sumw_nil; lia|]. rewrite !sumw_cons, IH. lia. Qed.

Lemma RM_cost : sumw (fun kr => mmap_len (r_len (snd kr))) (RM st) <= (2^(c_meta_alloc_shift cx + 1) - 2) * PGSZ.
Proof.
  pose proof (ir_shift _ _ _ IR) as [S0 _].
  rewrite (sumw_ext _ (fun kr => 2^(jof kr) * PGSZ)).
  2:{ intros kr Hkr. destruct (RM_j kr Hkr) as [B LEN]. rewrite LEN. apply mmap_len_of_aligned; [pose proof (Z.pow_pos_nonneg 2 (jof kr)); unfold PGSZ; lia| unfold PGSZ; apply Z_mod_mult]. }
  rewrite <- (sumw_map jof (fun j => 2^j * PGSZ)). rewrite sumw_scale, <- geo_sum by lia. apply Z.mul_le_mono_nonneg_r; [unfold PGSZ; lia|].
  apply sumw_sub; [apply RM_j_nodup| | intros j _; apply Z.pow_nonneg; lia].
  intros j Hj. apply in_map_iff in Hj as (kr & <- & Hkr). apply In_zrange. pose proof (RM_j kr Hkr) as [B _]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ltotal_regions :
  sum_glen (ld_groups L) = sumw (fun kr => mmap_len (r_len (snd kr))) (RG st)
  /\ sum_mlen (ld_metas L) = sumw (fun kr => mmap_len (r_len (snd kr))) (RM st)
  /\ length (ld_groups L) = length (RG st) /\ length (ld_metas L) = length (RM st).
Proof.
  pose proof (ir_groups _ _ _ IR) as PG. pose proof (ir_metas _ _ _ IR) as PM.
  change (List.filter _ _) with (RG st) in PG. change (List.filter _ _) with (RM st) in PM.
  rewrite sum_glen_sumw, sum_mlen_sumw, (sumw_perm _ _ _ PG), (sumw_perm _ _ _ PM), !sumw_map. cbn [fst snd].
  rewrite (Permutation_length PG), (Permutation_length PM), !map_length. auto.
Qed.

Lemma lbrk_bound : lbrk_bytes L <= (Z.of_nat (size (s_areas st)) + 1) * PGSZ /\ 0 <= lbrk_cnt L <= Z.of_nat (size (s_areas st)).
Proof.
  assert (NG : match ld_brk L with BPGuard _ => False | _ => True end).
  { pose proof (ir_brk _ _ _ IR) as B. destruct (c_brk cx); [destruct B as [-> _]| rewrite B| destruct B as [-> _]]; exact I. }
  unfold lbrk_bytes, lbrk_cnt. destruct (ld_brk L); try (exfalso; exact NG);
    (destruct (ld_brkreg L) as [[b l]|] eqn:ER; [| unfold PGSZ; lia]);
    (destruct (proj1 (ir_brkreg _ _ _ IR b l) ER) as (rid & r & Hr & K & _ & <-);
     destruct (brk_len rid r Hr K) as (MOD & TWO & CNT); unfold PGSZ in *; Z.div_mod_to_equations; nia).
Qed.

(* [comment removed for export] *)
Theorem footprint (ACAP : Z) :
  Z.of_nat (size (s_areas st)) <= ACAP -> ACAP < 2047 ->
  ltotal L <= (Z.of_nat (length BL) + 97) * 2^16 + (nbig + 48) * 2^20 + sumw bsize BL + (2^12 - 2) * PGSZ + (ACAP + 1) * PGSZ
  /\ lcount L <= Z.of_nat (length BL) + 97 + 11 + ACAP
  /\ 0 <= c_meta_alloc_shift cx <= 11.
Proof.
  intros HA HC. pose proof (ir_shift _ _ _ IR) as [S0 _]. pose proof heavy_length as NH. unfold nbig.
  assert (SH : c_meta_alloc_shift cx <= 11).
  { pose proof shift_areas as SA. destruct (Z.le_gt_cases (c_meta_alloc_shift cx) 11) as [LE|GT]; [exact LE|]. exfalso.
    assert (2^11 <= 2^(c_meta_alloc_shift cx - 1)) by (apply Z.pow_le_mono_r; lia). change (2^11) with 2048 in H. lia. }
  destruct ltotal_regions as (EG & EM & LG & LM). destruct lbrk_bound as [BB BC].
  pose proof RG_cost as CG. pose proof RM_cost as CM. pose proof RG_length as NG. pose proof RM_length as NM.
  assert (P11 : 2^(c_meta_alloc_shift cx + 1) <= 2^12) by (apply Z.pow_le_mono_r; lia).
  pose proof (sumw_nonneg bsize BL ltac:(intros k Hk; destruct (is_blocks _ _ _ IS k Hk) as (_ & _ & _ & _ & B0 & _); exact B0)).
  unfold ltotal, lcount. rewrite EG, EM, LG, LM. unfold PGSZ in *. split; [nia| split; [lia| lia]].
Qed.

End FOOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem footprint2 st L BL LS st' L' BL' LS' (ACAP : Z) :
  INVL x0 st L BL LS -> INVL x0 st' L' BL' LS' -> strip st' = strip st ->
  Z.of_nat (size (s_areas st)) <= ACAP -> ACAP < 2047 ->
  ltotal L <= (Z.of_nat (length BL') + 97) * 2^16 + (nbig BL' + 48) * 2^20 + sumw bsize BL' + (2^12 - 2) * PGSZ + (ACAP + 1) * PGSZ
  /\ lcount L <= Z.of_nat (length BL') + 97 + 11 + ACAP
  /\ 0 <= c_meta_alloc_shift (s_ctx st) <= 11.
Proof.
  intros INV INV' ES HA HC.
  assert (ER : s_regions st' = s_regions st) by (apply (f_equal s_regions) in ES; exact ES).
  assert (EG : RG st' = RG st) by (unfold RG; rewrite ER; reflexivity).
  pose proof (ir_shift _ _ _ (proj1 INV)) as [S0 _].
  assert (SH : c_meta_alloc_shift (s_ctx st) <= 11).
  { pose proof (shift_areas x0 st L BL LS INV eq_refl) as SA. destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 11) as [LE|GT]; [exact LE|]. exfalso.
    assert (2^11 <= 2^(c_meta_alloc_shift (s_ctx st) - 1)) by (apply Z.pow_le_mono_r; lia). change (2^11) with 2048 in H. lia. }
  destruct (ltotal_regions x0 st L BL LS INV) as (E1 & E2 & L1 & L2). destruct (lbrk_bound x0 st L BL LS INV eq_refl) as [BB BC].
  pose proof (RG_cost x0 st' L' BL' LS' INV' eq_refl eq_refl) as CG. rewrite EG in CG.
  pose proof (RG_length x0 st' L' BL' LS' INV' eq_refl eq_refl) as NG. rewrite EG in NG.
  pose proof (heavy_length x0 st' L' BL' LS' INV' eq_refl eq_refl) as NH. rewrite EG in NH. unfold nbig.
  pose proof (RM_cost x0 st L BL LS INV) as CM. pose proof (RM_length x0 st L BL LS INV) as NM.
  assert (P11 : 2^(c_meta_alloc_shift (s_ctx st) + 1) <= 2^12) by (apply Z.pow_le_mono_r; lia).
  pose proof (sumw_nonneg bsize BL' ltac:(intros k Hk; destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV')))))) k Hk) as (_ & _ & _ & _ & B0 & _); exact B0)).
  unfold ltotal, lcount. rewrite E1, E2, L1, L2. unfold PGSZ in *. split; [nia| split; [lia| lia]].
Qed.
