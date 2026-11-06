(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree Malloc KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4 MI_WFree2 MI_Cnt
  LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf LB_QM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zrange_nodup lo n : List.NoDup (zrange lo n).
Proof.
  unfold zrange. apply Finite.Injective_map_NoDup; [| apply seq_NoDup]. intros a b E. lia.
Qed.

Lemma nodup_map_inj' {A B} (f : A -> B) (l : list A) x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND Hx Hy E; [destruct Hx|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [->|Hx]; destruct Hy as [->|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma zlen_zrange lo n : 0 <= n -> zlen (zrange lo n) = n.
Proof. intros Hn. unfold zlen, zrange. rewrite length_map, length_seq. lia. Qed.

Lemma zcount_flat_map {A B} (g : A -> list B) (p : B -> bool) l : zcount p (flat_map g l) = zsum (map (fun x => zcount p (g x)) l).
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [flat_map map]. rewrite zcount_app, zsum_cons, IH. reflexivity. Qed.

Lemma zcount_mapf {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

Lemma zcount_true {A} (l : list A) : zcount (fun _ => true) l = zlen l.
Proof. induction l as [|a l IH]; [reflexivity|]. rewrite zcount_cons, zlen_cons, IH. reflexivity. Qed.

Lemma zcount_const {A} (b : bool) (l : list A) : zcount (fun _ => b) l = if b then zlen l else 0.
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

Lemma in_slots_of m i : In (m, i) slots_of <-> (exists b, hosts st b m) /\ 0 <= i <= m_last_idx (MR st m).
Proof.
  unfold slots_of. rewrite in_flat_map. split.
  - intros ([m' b] & Hin & Hmi). apply in_map_iff in Hmi as (i' & E & Hi). inversion E. subst. cbn in Hi.
    apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
    apply in_zrange in Hi; [| unfold cnt_of; lia]. split; [exists b, ai; exact Hb| unfold cnt_of in Hi; lia].
  - intros ([b [ai Hb]] & Hi). exists (m, b). split; [apply gmetas_in; exists ai; exact Hb|]. cbn.
    apply in_map_iff. exists i. split; [reflexivity|]. apply in_zrange; unfold cnt_of; [pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)); lia| lia].
Qed.

Lemma slots_of_nodup : List.NoDup slots_of.
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
Lemma gcnt_slots c : gcnt st c = zcount (fun mi => m_sizeclass (MR st (fst mi)) =? c) slots_of.
Proof.
  rewrite gcnt_gmetas. unfold slots_of. rewrite zcount_flat_map. f_equal. apply map_ext_in. intros [m b] Hin. cbn.
  rewrite zcount_mapf. cbn. rewrite zcount_const. destruct (m_sizeclass (MR st m) =? c); [| reflexivity].
  apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
  rewrite zlen_zrange; unfold cnt_of; lia.
Qed.

(* [comment removed for export] *)
Lemma nsc_le_gcnt c : nsc st c <= gcnt st c.
Proof.
  unfold nsc. rewrite gcnt_gmetas. apply zsum_map_le. intros [m b] Hin. cbn. unfold cls.
  apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
  destruct (m_sizeclass (MR st m) =? c); cbn; [destruct (stdg st m); cbn; unfold cnt_of; lia| lia].
Qed.
Lemma nsc_nonneg c : 0 <= nsc st c.
Proof.
  unfold nsc. apply zsum_map_nonneg. intros [m b] Hin. cbn. apply gmetas_in in Hin as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
  destruct (_ && _); unfold cnt_of; lia.
Qed.

(* [comment removed for export] *)
Lemma nstd_le_gcnt c : 0 <= c < 48 -> nstd st c * cmax c <= gcnt st c.
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
Lemma nstd_nonneg c : 0 <= nstd st c.
Proof. unfold nstd. apply zcount_nonneg. Qed.

(* [comment removed for export] *)
Lemma dec_mi : forall x y : aptr * Z, {x = y} + {x <> y}.
Proof. intros x y. apply (decide (x = y)). Qed.

Definition slot_of_blk (k : blk) : aptr * Z := match s_slots st !! bslot k with Some mi => mi | None => ((0%N, 0), 0) end.

Lemma LS_le_gcnt c : LB_Inv.LS st BL c <= gcnt st c.
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

Lemma addr_slot m i : In (m, i) (slots_of st) -> s_slots st !! addr (m, i) = Some (m, i).
Proof. intros H. apply (in_slots_of X st L BL LS INV) in H as [[b Hb] Hi]. exact (is_total _ _ _ IS b m i Hb Hi). Qed.

Lemma addr_inj mi1 mi2 : In mi1 (slots_of st) -> In mi2 (slots_of st) -> addr mi1 = addr mi2 -> mi1 = mi2.
Proof.
  destruct mi1 as [m1 i1], mi2 as [m2 i2]. intros H1 H2 E.
  pose proof (addr_slot _ _ H1) as S1. pose proof (addr_slot _ _ H2) as S2. rewrite E in S1. rewrite S1 in S2. congruence.
Qed.

(* [comment removed for export] *)
Lemma stride_nonneg m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> 0 <= get_stride (MR st m).
Proof.
  intros Hb. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_maplen _ _ _ _ _ _ GO) as ML0.
  unfold get_stride.
  destruct (Z.eqb_spec (m_last_idx (MR st m)) 0) as [LZ|LNZ]; destruct (Z.eqb_spec (m_maplen (MR st m)) 0) as [MZ|MNZ]; cbn [andb negb].
  all: try (unfold UNIT; lia).
  all: destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(SC & LI0 & ML & _)]; [pose proof (size_class_pos _ SC); unfold UNIT; lia| first [congruence| lia]].
Qed.

Lemma addr_pos m i : In (m, i) (slots_of st) -> 0 < snd (addr (m, i)).
Proof.
  intros H. apply (in_slots_of X st L BL LS INV) in H as [[b [ai Hb]] Hi]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  unfold addr, slot_start', sstart. cbn. pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
  unfold gbase. rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ ai Hb)). cbn.
  pose proof (stride_nonneg m b ai Hb). assert (0 <= get_stride (MR st m) * i) by (apply Z.mul_nonneg_nonneg; lia). unfold UNIT. lia.
Qed.

Lemma zcount_cover3 {A} (p q1 q2 q3 : A -> bool) l :
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

Lemma dec_blk : forall x y : blk, {x = y} + {x <> y}. Proof. intros x y. apply (decide (x = y)). Qed.
Lemma dec_mb : forall x y : aptr * aptr, {x = y} + {x <> y}. Proof. intros x y. apply (decide (x = y)). Qed.
Lemma dec_ap : forall x y : aptr, {x = y} + {x <> y}. Proof. intros x y. apply (decide (x = y)). Qed.

Lemma find_some {A} (p : A -> bool) l x : find p l = Some x -> In x l /\ p x = true.
Proof. induction l as [|a l IH]; cbn; [discriminate|]. destruct (p a) eqn:E; [intros H; inversion H; subst; auto| intros H; destruct (IH H); auto]. Qed.
Lemma existsb_find {A} (p : A -> bool) l : existsb p l = true -> exists x, find p l = Some x.
Proof. induction l as [|a l IH]; cbn; [discriminate|]. destruct (p a); [intros _; eexists; reflexivity| exact IH]. Qed.

(* [comment removed for export] *)
Theorem all_in_use c : 0 <= c < 48 -> x_fresh X = None -> active st c = None ->
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

Lemma zcount_cover2 {A} (p q1 q2 : A -> bool) l :
  (forall x, In x l -> p x = true -> q1 x = true \/ q2 x = true) -> zcount p l <= zcount q1 l + zcount q2 l.
Proof.
  intros H. pose proof (zcount_cover3 p q1 q2 (fun _ => false) l ltac:(intros x Hx Hp; destruct (H x Hx Hp); auto)) as C.
  rewrite (zcount_false (fun _ => false)) in C by auto. lia.
Qed.

(* [comment removed for export] *)
Lemma zcount_by_class {A} (cf : A -> Z) (p : A -> bool) (l : list A) :
  (forall x, In x l -> p x = true -> 0 <= cf x < 48) ->
  zcount p l = zsum (map (fun c => zcount (fun x => p x && (cf x =? c)) l) classes).
Proof.
  intros H. rewrite zcount_eq_zsum.
  rewrite (zsum_by_class (fun x => if p x then cf x else 0) (fun x => if p x then 1 else 0) l).
  2:{ intros x Hx. destruct (p x) eqn:E; [apply H; assumption| lia]. }
  apply zsum_map_ext. intros c Hc. rewrite zcount_eq_zsum. apply zsum_map_ext. intros x Hx.
  destruct (p x); cbn; [reflexivity|]. destruct c; reflexivity.
Qed.

Lemma classes_zrange : classes = zrange 0 48.
Proof. reflexivity. Qed.

Lemma zsum_lt_indicator (v c : Z) : 0 <= c <= 48 -> zsum (map (fun c' => if c' <? c then v else 0) classes) = v * c.
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

Lemma HOSTSTD_guest c' : 0 <= c' <= 6 -> HOSTSTD P c' = 0.
Proof.
  intros Hc. unfold HOSTSTD. transitivity (zsum (map (fun _ : Z => 0) guests)); [| rewrite zsum_map_const; lia].
  apply zsum_map_ext. intros g Hg. assert (G : 0 <= g <= 6) by (unfold guests in Hg; cbn in Hg; lia).
  destruct (tab_host_small g G) as (_ & BH & _). destruct (Z.eqb_spec (bighost g) c'); [lia| reflexivity].
Qed.

Lemma nstd_cap c' : 0 <= c' <= 6 -> nstd st c' <= (CAP0 P c' + 32) / cmax c'.
Proof.
  intros Hc. pose proof (nstd_le_gcnt X st L BL LS INV c' ltac:(lia)) as N1. pose proof (aq_slots _ _ _ HAQ c' ltac:(lia)) as A2.
  unfold CAP in A2. rewrite (HOSTSTD_guest c' Hc) in A2. pose proof (tab_basic_ok c' ltac:(lia)) as (_ & CM & _).
  apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
Theorem hosted_le c : 0 <= c < 48 -> hosted st c <= HOSTSTD P c + (if c <=? 23 then 160 * c else 0).
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
Lemma LS_le_LR_MIS c : 0 <= c < 48 -> LB_Inv.LS st BL c <= LR BL c + MIS st BL c.
Proof.
  intros Hc. unfold LB_Inv.LS, LR, MIS. apply zcount_cover2. intros k Hk Hs.
  destruct (sg_cls _ _ SGH k Hk) as (m & i & Es & C48 & _). unfold slotcls in Hs |- *. rewrite Es in Hs |- *. unfold cls in Hs |- *.
  apply Z.eqb_eq in Hs. destruct (C48 ltac:(lia)) as [SM [E|E]].
  - left. unfold isbig. rewrite E, Hs, Z.eqb_refl. destruct (Z.leb_spec MMAP_THRESHOLD (bsize k)); [lia| reflexivity].
  - right. rewrite Hs, E, Hs, !Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem creation_room c : 0 <= c < 48 -> x_fresh X = None -> active st c = None -> gcnt st c <= CAP P c.
Proof.
  intros Hc HF HA.
  pose proof (all_in_use X st L BL LS INV c Hc HF HA) as A.
  pose proof (LS_le_LR_MIS c Hc) as B1. pose proof (aq_live _ _ _ HAQ c Hc) as B2. pose proof (sg_mis _ _ SGH c) as B3.
  pose proof (hosted_le X st L BL LS P INV SGH HAQ c Hc) as B4.
  unfold CAP, CAP0. destruct (x_pend X); lia.
Qed.

(* [comment removed for export] *)
Definition slot0_blk (mb : aptr * aptr) : blk :=
  match find (fun k => aptr_eqb (bslot k) (slot_start' (MR st (fst mb)) 0)) BL with Some k => k | None => ((0%N, 0), 0, 0) end.

Lemma n63g_le : zcount (fun mb => m_sizeclass (MR st (fst mb)) =? 63) (gmetas st) <= n63 BL.
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

Theorem ngroups_le : ngroups st <= NG P.
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
Theorem ncarved_le_groups d : QM X st d -> c_free_meta_head (ctx st) = None -> x_zomb X = [] ->
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
