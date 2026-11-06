(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngGeoX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition plt (k : nat) (p : sptr) : Prop := (prid p < k)%nat.
Definition olt (k : nat) (o : option sptr) : Prop := match o with Some p => plt k p | None => True end.
Definition svlt (k : nat) (v : sval) : Prop := match v with VP p => plt k p | _ => True end.
Definition loclt (k : nat) (l : loc) : Prop := match l with LMem p => plt k p | LCtx _ => True end.
Definition celllt (k : nat) (c : mcell) : Prop := loclt k (mc_loc c) /\ svlt k (mc_val c).

(* [comment removed for export] *)
Definition XNM (X : list sptr) (s : astate) : Prop := forall x, In x X -> MT s x = Some MRaw \/ MT s x = Some (MFree None None).

Lemma XNM_nil : forall s, XNM [] s.
Proof. intros s x []. Qed.

Lemma XNU_of_XNM : forall X s, XNM X s -> XNU X s.
Proof. intros X s H x Hx a E. destruct (H x Hx) as [E2|E2]; rewrite E in E2; discriminate E2. Qed.

Lemma memb_In' : forall (g : sptr) X, memb g X = true -> In g X.
Proof.
  intros g X. induction X as [|x t IH]; cbn; [discriminate|].
  destruct (sptr_eqb g x) eqn:E; [intros _; left; symmetry; apply sptr_eqb_eq; exact E | intros H; right; exact (IH H)].
Qed.

Lemma chain_members : forall lk prev l first x p n, chain lk prev l first -> In x l -> lk x = Some (Some p, Some n) ->
  (In p l \/ p = prev) /\ (In n l \/ n = first).
Proof.
  intros lk prev l. revert prev. induction l as [|y rest IH]; intros prev first x p n H Hin Hx; [destruct Hin|].
  cbn in H. destruct H as [Hy Hr]. destruct Hin as [<-|Hin].
  - rewrite Hy in Hx. injection Hx as <- <-. split; [right; reflexivity|].
    destruct rest as [|z rest']; cbn; [right; reflexivity | left; right; left; reflexivity].
  - destruct (IH y first x p n Hr Hin Hx) as [[A|A] [B|B]]; (split; [| ]); first [ (left; right; exact A) | (left; left; exact A) | idtac ];
      first [ (left; right; exact B) | (right; exact B) | idtac ].
    + subst p. left. left. reflexivity.
    + subst p. left. left. reflexivity.
Qed.

Lemma last_In_l : forall (l : list sptr) d, l <> [] -> In (last l d) l.
Proof.
  intros l d. induction l as [|x t IH]; intros H; [exfalso; exact (H eq_refl)|].
  destruct t as [|y t']; [left; reflexivity|]. right. apply IH. discriminate.
Qed.

Lemma cycle_members : forall lk ms x p n, cycle_ok lk ms -> In x ms -> lk x = Some (Some p, Some n) -> In p ms /\ In n ms.
Proof.
  intros lk ms x p n (_ & H) Hin Hx. destruct ms as [|m0 rest]; [destruct Hin|].
  destruct (chain_members lk _ _ _ x p n H Hin Hx) as [[A|A] [B|B]].
  - split; assumption.
  - split; [exact A | subst n; left; reflexivity].
  - split; [subst p; apply last_In_l; discriminate | exact B].
  - split; [subst p; apply last_In_l; discriminate | subst n; left; reflexivity].
Qed.

Section LT.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv X R U s.

#[using="Type"] Lemma region_lt : forall r rg, region_of s r = Some rg -> (r < length (st_regions s))%nat.
Proof. intros r rg H. exact (region_of_lt s r rg H). Qed.

#[using="X R U HI"] Lemma area_lt : forall a, In a (st_areas s) -> plt (length (st_regions s)) a.
Proof.
  intros a Ha. pose proof (inv_areas HI) as (_ & A2 & _). destruct (A2 a Ha) as (r & o & rga & -> & _ & _ & Hr & _).
  unfold plt. cbn [prid]. exact (region_lt r rga Hr).
Qed.

#[using="X R U HI"] Lemma key_lt : forall q, In q (keys s) -> plt (length (st_regions s)) q.
Proof.
  intros q Hq. pose proof (inv_keys HI) as (_ & KP & _). destruct (KP q Hq) as (a & j & Ha & _ & ->).
  pose proof (area_lt a Ha) as H. unfold plt in *. rewrite prid_padd. exact H.
Qed.

#[using="X R U HI"] Lemma MT_lt : forall q x, MT s q = Some x -> plt (length (st_regions s)) q.
Proof. intros q x H. apply key_lt. exact (MT_Some_In_keys s q x H). Qed.

#[using="R U HI"] Lemma MTX_lt : forall q x, MTX X s q = Some x -> plt (length (st_regions s)) q.
Proof. intros q x H. unfold MTX in H. destruct (memb q X); [discriminate|]. exact (MT_lt q x H). Qed.

#[using="R U HI"] Lemma alinks_lt : forall sc q v, alinks X s sc q = Some v -> plt (length (st_regions s)) q.
Proof.
  intros sc q v H. unfold alinks in H. destruct (MTX X s q) as [x|] eqn:E; [|discriminate]. exact (MTX_lt q x E).
Qed.

#[using="R U HI"] Lemma flinks_lt : forall q v, flinks X s q = Some v -> plt (length (st_regions s)) q.
Proof.
  intros q v H. unfold flinks in H. destruct (MTX X s q) as [x|] eqn:E; [|discriminate]. exact (MTX_lt q x E).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ring_members_lt : forall lk hd ms, ring_ok lk hd ms -> (forall q v, lk q = Some v -> plt (length (st_regions s)) q) ->
  forall q, In q ms -> plt (length (st_regions s)) q.
Proof.
  intros lk hd ms Hr Hlk q Hq. destruct (ring_links lk hd ms q Hr Hq) as (pr & nx & E). exact (Hlk q _ E).
Qed.

#[using="X R U HI"] Lemma active_hd_lt : forall sc, 0 <= sc < 48 -> olt (length (st_regions s)) (active_hd s sc).
Proof.
  intros sc Hsc. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & _).
  destruct (active_hd s sc) as [h|] eqn:E; [|exact I]. cbn [olt].
  destruct (ring_head_In _ _ _ Rg) as [Hin _]. exact (ring_members_lt _ _ _ Rg (alinks_lt sc) h Hin).
Qed.

#[using="X R U HI"] Lemma free_head_lt : olt (length (st_regions s)) (st_free_meta_head s).
Proof.
  destruct (inv_rings HI) as ((ms & Rg & _) & _ & _).
  destruct (st_free_meta_head s) as [h|] eqn:E; [|exact I]. cbn [olt].
  destruct (ring_head_In _ _ _ Rg) as [Hin _]. exact (ring_members_lt _ _ _ Rg flinks_lt h Hin).
Qed.

#[using="R U HI"] Lemma used_links_lt : forall g am, usedX X s g am -> olt (length (st_regions s)) (am_prev am) /\ olt (length (st_regions s)) (am_next am).
Proof.
  intros g am Hu. destruct (inv_rings HI) as (_ & A & DU).
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Hcl & _).
  destruct Hcl as [(S63 & _) | (Ssc & _)].
  - destruct (DU g am Hu S63) as (-> & ->). split; exact I.
  - destruct (A (am_sc am) Ssc) as (ms & Rg & Hin & _).
    destruct (am_prev am) as [pr|] eqn:Ep; destruct (am_next am) as [nx|] eqn:En.
    4: { split; exact I. }
    all: assert (Hg : In g ms) by (apply (proj2 (Hin g am Hu eq_refl)); rewrite Ep, En; discriminate).
    all: assert (Ea : alinks X s (am_sc am) g = Some (am_prev am, am_next am)) by (unfold alinks; unfold usedX in Hu; rewrite Hu, Z.eqb_refl; reflexivity).
    all: destruct (ring_links _ _ _ g Rg Hg) as (p' & n' & E); rewrite Ea in E; injection E as E1 E2; rewrite Ep in E1; rewrite En in E2.
    all: try discriminate.
    injection E1 as E1. injection E2 as E2. subst p' n'.
    destruct (cycle_members _ _ g pr nx (proj1 Rg) Hg ltac:(rewrite Ea, Ep, En; reflexivity)) as (P1 & P2).
    split; cbn [olt]; [exact (ring_members_lt _ _ _ Rg (alinks_lt _) pr P1) | exact (ring_members_lt _ _ _ Rg (alinks_lt _) nx P2)].
Qed.

#[using="R U HI"] Lemma free_links_lt : forall g pr nx, MTX X s g = Some (MFree pr nx) -> olt (length (st_regions s)) pr /\ olt (length (st_regions s)) nx.
Proof.
  intros g pr nx Hg. destruct (inv_rings HI) as ((ms & Rg & Hall) & _ & _).
  pose proof (Hall g pr nx Hg) as Hin. destruct (ring_links _ _ _ g Rg Hin) as (p' & n' & E).
  unfold flinks in E. rewrite Hg in E. injection E as -> ->.
  destruct (cycle_members _ _ g p' n' (proj1 Rg) Hin ltac:(unfold flinks; rewrite Hg; reflexivity)) as (P1 & P2).
  split; cbn [olt]; [exact (ring_members_lt _ _ _ Rg flinks_lt p' P1) | exact (ring_members_lt _ _ _ Rg flinks_lt n' P2)].
Qed.

#[using="X R U HI"] Lemma avail_meta_lt : st_areas s <> [] -> plt (length (st_regions s)) (st_avail_meta s).
Proof.
  intros Hne. pose proof (inv_keys HI) as (_ & _ & _ & E & _). rewrite (E Hne). unfold plt. rewrite prid_padd.
  apply area_lt. apply last_In_l. exact Hne.
Qed.

#[using="X R U HI"] Lemma head_tail_lt : olt (length (st_regions s)) (st_area_head s) /\ olt (length (st_regions s)) (st_area_tail s).
Proof.
  pose proof (inv_areas HI) as (_ & _ & Eh & Et & _). rewrite Eh, Et. split.
  - destruct (st_areas s) as [|a t] eqn:E; [exact I|]. cbn [hd_error olt]. apply area_lt. rewrite E. left. reflexivity.
  - destruct (st_areas s) as [|a t] eqn:E; [exact I|]. cbn [olt]. apply area_lt. rewrite E. apply last_In_l. discriminate.
Qed.

#[using="X R U HI"] Lemma brk_lt : forall r p, st_brk s = BrkCur r p -> (r < length (st_regions s))%nat.
Proof.
  intros r p Hb. pose proof (inv_areas HI) as (_ & _ & _ & _ & _ & _ & B & _). rewrite Hb in B.
  destruct B as (_ & rg & Hr & _). exact (region_lt r rg Hr).
Qed.

(* [comment removed for export] *)
#[using="X R U HI"] Lemma ama_lt : (st_areas s <> [] \/ 0 < st_avail_meta_area_count s) -> plt (length (st_regions s)) (st_avail_meta_areas s).
Proof.
  intros H. pose proof (inv_areas HI) as (_ & _ & _ & _ & _ & _ & _ & C & _ & AMA).
  destruct H as [H|H].
  - destruct (AMA H) as (rg & Hr). exact (region_lt _ rg Hr).
  - destruct (C H) as (r & o & rg & E & Hr & _). rewrite E. exact (region_lt r rg Hr).
Qed.

(* [comment removed for export] *)
#[using="X R U HI"] Lemma footprint_lt : forall rg, In rg (footprint s) -> loclt (length (st_regions s)) (fst rg).
Proof.
  intros rg H. unfold footprint in H. destruct H as [<-|H]; [exact I|]. apply in_app_iff in H as [H|H].
  - apply in_map_iff in H as (a & <- & Ha). exact (area_lt a Ha).
  - apply in_flat_map in H as (k & Hk & H). apply in_seq in Hk.
    destruct (region_of s k) as [rgk|]; [|destruct H]. destruct (rg_kind rgk); try destruct H. destruct (rg_live rgk); [|destruct H].
    destruct H as [<-|[]]. unfold loclt, plt. cbn. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma In_areas_cells_next : forall l c, In c (areas_cells s l) ->
  exists a next, In a l /\ (next = None \/ exists b, next = Some b /\ In b l) /\ In c (area_cells s a next).
Proof.
  intros l. induction l as [|a t IH]; intros c H; cbn [areas_cells] in H; [destruct H|].
  apply in_app_iff in H as [H|H].
  - exists a, (hd_error t). split; [left; reflexivity|]. split; [|exact H].
    destruct t as [|b t']; [left; reflexivity | right; exists b; split; [reflexivity | right; left; reflexivity]].
  - destruct (IH c H) as (a' & next & Ha & Hn & Hc). exists a', next. split; [right; exact Ha|].
    split; [|exact Hc]. destruct Hn as [->|(b & -> & Hb)]; [left; reflexivity | right; exists b; split; [reflexivity | right; exact Hb]].
Qed.

#[using="R U HI"] Theorem image_lt : XNM X s -> forall c, In c (image s) -> celllt (length (st_regions s)) c.
Proof.
  intros HX c Hc. set (k := length (st_regions s)).
  assert (OLT : forall o, olt k o -> svlt k (optr o)) by (intros [p|] H; exact H).
  unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
  - (* [comment removed for export] *)
    split; [destruct (In_ctx_cells s c Hc) as (off & -> & _); exact I|].
    unfold ctx_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
    + cbn [In] in Hc. repeat (destruct Hc as [<-|Hc]; [cbn [mc_val svlt]|]); try destruct Hc.
      all: try exact I.
      * destruct (st_init_done s); exact I.
      * apply OLT. exact free_head_lt.
      * destruct (st_areas s) as [|a t] eqn:E; [exact I|]. apply avail_meta_lt. rewrite E. discriminate.
      * apply OLT. exact (proj1 head_tail_lt).
      * apply OLT. exact (proj2 head_tail_lt).
      * destruct (match st_areas s with [] => true | _ => false end && (st_avail_meta_area_count s =? 0)) eqn:E; [exact I|].
        cbn [svlt]. apply ama_lt. destruct (st_areas s) as [|a t] eqn:Ea.
        -- right. cbn in E. apply Z.eqb_neq in E. pose proof (inv_ctx HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc0 & _). lia.
        -- left. discriminate.
      * destruct (st_brk s) as [| |r p] eqn:Eb; try exact I. cbn [svlt plt prid]. exact (brk_lt r p Eb).
    + apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]]].
      * apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj. cbn [mc_val]. apply OLT.
        pose proof (active_hd_lt (Z.of_nat j) ltac:(lia)) as H. unfold active_hd in H. rewrite Nat2Z.id in H. exact H.
      * apply in_map_iff in Hc as (j & <- & _). exact I.
      * apply in_map_iff in Hc as (j & <- & _). exact I.
      * apply in_map_iff in Hc as (j & <- & _). exact I.
  - (* [comment removed for export] *)
    destruct (In_areas_cells_next (st_areas s) c Hc) as (a & next & Ha & Hn & Hc').
    pose proof (area_lt a Ha) as Pa. unfold area_cells in Hc'. apply in_app_iff in Hc' as [Hc'|Hc'].
    + cbn [In] in Hc'. unfold celllt, loclt, plt in *.
      destruct Hc' as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_val svlt]; rewrite ?prid_padd; split; try exact Pa; try exact I.
      destruct Hn as [->|(b & -> & Hb)]; [exact I | exact (area_lt b Hb)].
    + apply in_flat_map in Hc' as (j & _ & Hc').
      set (q := padd a (AREA_HDR + META_SIZE * Z.of_nat j)) in *.
      assert (Pq : plt k q) by (unfold q, plt in *; rewrite prid_padd; exact Pa).
      assert (LOC : forall d v w, loclt k (mc_loc (MCell (LMem (padd q d)) w v))) by (intros d v w; unfold loclt, plt in *; cbn; rewrite prid_padd; exact Pq).
      destruct (mlookup (st_metas s) q) as [[pr nx | | am]|] eqn:Eq.
      * (* [comment removed for export] *)
        assert (Hl : olt k pr /\ olt k nx).
        { destruct (memb q X) eqn:Em.
          - destruct (HX q (memb_In' q X Em)) as [E|E]; unfold MT in E; rewrite Eq in E; [discriminate E|].
            injection E as -> ->. split; exact I.
          - apply (free_links_lt q pr nx). unfold MTX. rewrite Em. exact Eq. }
        cbn [meta_slot_cells In] in Hc'. repeat (destruct Hc' as [<-|Hc']; [split; [apply LOC | cbn [mc_val]]|]); try destruct Hc'.
        all: first [exact I | apply OLT; tauto].
      * cbn [meta_slot_cells In] in Hc'. repeat (destruct Hc' as [<-|Hc']; [split; [apply LOC | exact I]|]). destruct Hc'.
      * (* [comment removed for export] *)
        assert (Hu : usedX X s q am).
        { destruct (memb q X) eqn:Em.
          - destruct (HX q (memb_In' q X Em)) as [E|E]; unfold MT in E; rewrite Eq in E; discriminate E.
          - apply usedX_intro; [exact Em | exact Eq]. }
        destruct (used_links_lt q am Hu) as (Lp & Ln).
        pose proof (used_group_prid_lt X R U s q am HI Hu) as Pm.
        cbn [meta_slot_cells In] in Hc'. repeat (destruct Hc' as [<-|Hc']; [split; [apply LOC | cbn [mc_val]]|]); try destruct Hc'.
        all: first [exact I | (apply OLT; assumption) | exact Pm].
      * cbn [meta_slot_cells In] in Hc'. repeat (destruct Hc' as [<-|Hc']; [split; [apply LOC | exact I]|]). destruct Hc'.
  - (* [comment removed for export] *)
    apply in_flat_map in Hc as ([g am] & Hg & Hc'). cbn [fst snd] in Hc'.
    apply (used_metas_usedX_X X R U s g am HI (XNU_of_XNM X s HX)) in Hg.
    pose proof (used_group_prid_lt X R U s g am HI Hg) as Pm.
    assert (Pg : plt k g) by (exact (MT_lt g _ (proj1 (usedX_MT X s g am Hg)))).
    destruct (In_group_cells X R U s g am c HI Hg Hc') as (d & E & _). split; [rewrite E; unfold loclt, plt; rewrite prid_padd; exact Pm|].
    unfold group_cells in Hc'. apply in_app_iff in Hc' as [Hc'|Hc'].
    + cbn [In] in Hc'. destruct Hc' as [<-|[<-|[]]]; [exact Pg|]. destruct (am_maplen am =? 0); exact I.
    + apply in_flat_map in Hc' as (i & _ & Hc'). unfold slot_cells in Hc'.
      apply in_app_iff in Hc' as [Hc'|Hc']; [cbn [In] in Hc'; destruct Hc' as [<-|[]]; exact I|].
      apply in_app_iff in Hc' as [Hc'|Hc'].
      * destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hc']. cbn [In] in Hc'. destruct Hc' as [<-|[<-|[]]]; exact I.
      * destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hc']. destruct (fr_off fr =? 0); [destruct Hc'|].
        cbn [In] in Hc'. destruct Hc' as [<-|[<-|[<-|[]]]]; exact I.
Qed.

End LT.
