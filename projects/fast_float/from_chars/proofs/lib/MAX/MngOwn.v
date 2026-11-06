(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap AXG_ffpost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cut1 (b : Z * Z) (r : ivl) : list ivl := [(fst r, Z.min (snd r) (fst b)); (Z.max (fst r) (fst b + snd b), snd r)].

Fixpoint carve (bs : list (Z * Z)) (r : ivl) : list ivl :=
  match bs with [] => [r] | b :: t => flat_map (carve t) (cut1 b r) end.

Lemma outside_app2 : forall (A B : list ivl) x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof. induction A as [|[lo hi] A IH]; intros B x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma outside_flat_map : forall {X} (f : X -> list ivl) (l : list X) x, outside (flat_map f l) x <-> (forall y, In y l -> outside (f y) x).
Proof.
  intros X f l x. induction l as [|y t IH]; cbn [flat_map In]; [split; [intros _ y []|intros _; exact I]|].
  rewrite outside_app2, IH. split; [intros [H1 H2] y' [<-|Hy]; [exact H1 | exact (H2 y' Hy)] | intros H; split; [apply H; left; reflexivity | intros y' Hy; apply H; right; exact Hy]].
Qed.

Lemma outside_carve : forall bs r x, (forall b, In b bs -> 0 <= snd b) ->
  (outside (carve bs r) x <-> ~ (fst r <= x < snd r) \/ exists b, In b bs /\ fst b <= x < fst b + snd b).
Proof.
  induction bs as [|b t IH]; intros [lo hi] x Hpos; cbn [carve].
  - cbn [outside fst snd]. split; [intros [H _]; left; exact H | intros [H | (b & [] & _)]; split; [exact H | exact I]].
  - rewrite outside_flat_map. unfold cut1. cbn [fst snd In].
    assert (Hb : 0 <= snd b) by (apply Hpos; left; reflexivity).
    assert (Ht : forall b', In b' t -> 0 <= snd b') by (intros b' Hb'; apply Hpos; right; exact Hb').
    split.
    + intros H. pose proof (H _ (or_introl eq_refl)) as H1. pose proof (H _ (or_intror (or_introl eq_refl))) as H2.
      rewrite (IH _ x Ht) in H1. rewrite (IH _ x Ht) in H2. cbn [fst snd] in H1, H2.
      destruct H1 as [H1 | (b' & Hb' & Hx)]; [|right; exists b'; split; [right; exact Hb' | exact Hx]].
      destruct H2 as [H2 | (b' & Hb' & Hx)]; [|right; exists b'; split; [right; exact Hb' | exact Hx]].
      destruct (Z_lt_le_dec x (fst b)) as [Lt|Ge]; [left; lia|].
      destruct (Z_lt_le_dec x (fst b + snd b)) as [Lt2|Ge2]; [right; exists b; split; [left; reflexivity | lia] | left; lia].
    + intros H y Hy. rewrite (IH _ x Ht). cbn [fst snd].
      destruct H as [H | (b' & [<-|Hb'] & Hx)].
      * destruct Hy as [<-|[<-|[]]]; left; cbn [fst snd]; lia.
      * destruct Hy as [<-|[<-|[]]]; left; cbn [fst snd]; lia.
      * right. exists b'. split; [exact Hb' | exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_loc : forall L r o, loc_addr L (LMem (SP r o)) = ly_reg L r + o.
Proof. reflexivity. Qed.

Lemma markers_home : forall s L c, WF s -> In c (markers s) ->
  exists rg, In rg (footprint s) /\ range_incl (cell_range L c) (crange L rg).
Proof.
  intros s L c HW Hc.
  destruct (In_markers_inv s c Hc) as [(g & am & i & fr & HF & Kf & Hc') | (g & am & Hu & ->)].
  - destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfr). apply (used_metas_usedX s g am HW) in Hu as Hux.
    pose proof (inv_groups HW g am Hux) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (N0 & O0 & F0 & _) & _).
    destruct (marker_cells_span am i fr c ltac:(clear - O0; lia) N0 F0 Hc') as (q & Eq & Hq1 & Hq2 & Hq3).
    destruct (used_group_region [] None U0 s g am HW Hux) as (rgH & HrH & HkH & HlH & Ho0H & HextH & _).
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rgH). split; [apply footprint_region_In; assumption|].
    pose proof (slot_in_span [] None U0 s HW g am i Hux Hi) as [SL1 SL2].
    unfold range_incl, cell_range, crange. cbn [fst snd]. rewrite Eq. destruct q as [rq oq]. rewrite !region_loc.
    cbn [prid poff] in *. rewrite Hq1 in *. rewrite prid_slot_start in Hq1. unfold group_extent, UNIT, IB in *.
    rewrite prid_slot_start. split; lia.
  - apply (used_metas_usedX s g am HW) in Hu as Hux.
    pose proof (inv_groups HW g am Hux) as ((Mlast & _) & _).
    destruct (used_group_region [] None U0 s g am HW Hux) as (rgH & HrH & HkH & HlH & Ho0H & HextH & _).
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rgH). split; [apply footprint_region_In; assumption|].
    pose proof (slot_in_span [] None U0 s HW g am (am_last am) Hux ltac:(lia)) as [SL1 SL2].
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Hux)) as Sp.
    unfold range_incl, cell_range, crange, gend_cell, slot_end. cbn [fst snd mc_loc mc_w].
    destruct (am_mem am) as [rm om] eqn:Em.
    rewrite (loc_padd L (slot_start am (am_last am)) (stride_of am - IB)).
    unfold slot_start. rewrite Em. rewrite !region_loc. cbn [prid poff padd] in *.
    unfold slot_start in SL1, SL2. rewrite Em in SL1, SL2. cbn [poff padd] in SL1, SL2.
    rewrite region_loc. unfold group_extent, UNIT, IB in *. split; lia.
Qed.

(* [comment removed for export] *)
Lemma regions_apart : forall s L (a1 a2 : ameta) g1 g2 lo1 n1 lo2 n2,
  WF s -> layout_ok L s -> usedX [] s g1 a1 -> usedX [] s g2 a2 -> prid (am_mem a1) <> prid (am_mem a2) ->
  0 <= lo1 -> lo1 + n1 <= poff (am_mem a1) + group_extent a1 + IB ->
  0 <= lo2 -> lo2 + n2 <= poff (am_mem a2) + group_extent a2 + IB ->
  ly_reg L (prid (am_mem a1)) + lo1 + n1 <= ly_reg L (prid (am_mem a2)) + lo2 \/
  ly_reg L (prid (am_mem a2)) + lo2 + n2 <= ly_reg L (prid (am_mem a1)) + lo1.
Proof.
  intros s L a1 a2 g1 g2 lo1 n1 lo2 n2 HW HL U1 U2 Hne H1 H2 H3 H4.
  pose proof HL as (_ & _ & Ldisj & _).
  destruct (used_group_region [] None U0 s g1 a1 HW U1) as (rg1 & Hr1 & Hk1 & Hl1 & Ho1 & He1 & _).
  destruct (used_group_region [] None U0 s g2 a2 HW U2) as (rg2 & Hr2 & Hk2 & Hl2 & Ho2 & He2 & _).
  assert (F1 : In (LMem (SP (prid (am_mem a1)) 0), rg_len rg1) (footprint s)) by (apply footprint_region_In; assumption).
  assert (F2 : In (LMem (SP (prid (am_mem a2)) 0), rg_len rg2) (footprint s)) by (apply footprint_region_In; assumption).
  destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj F1 F2 ltac:(intro E; injection E; intros; contradiction)) as [D|D];
    unfold ranges_disjoint in D; cbn [crange fst snd loc_addr] in D; rewrite ?region_loc in D; unfold IB in *; lia.
Qed.

Lemma markers_outside_blocks : forall s L c b, WF s -> layout_ok L s -> In c (markers s) -> In b (user_blocks s) ->
  ranges_disjoint (cell_range L c) (block_range L b).
Proof.
  intros s L c b HW HL Hc Hb.
  destruct (in_user_blocks_inv s b Hb) as (h & ah & j & f & Hh & Hj & Hf & Kf & ->).
  apply (used_metas_usedX s h ah HW) in Hh as Uh.
  pose proof (inv_groups HW h ah Uh) as (_ & _ & Gslh & _). pose proof (Gslh j Hj) as (_ & _ & T3). rewrite Hf in T3.
  destruct T3 as (_ & _ & (Nf & Of & Ff & _) & _).
  pose proof (slot_in_span [] None U0 s HW h ah j Uh Hj) as [SJ1 SJ2].
  pose proof (stride_pos _ _ _ _ _ (inv_groups HW h ah Uh)) as Sh.
  unfold ranges_disjoint, cell_range, block_range, frame_ptr. cbn [fst snd].
  destruct (In_markers_inv s c Hc) as [(g & am & i & fr & HF & Kfr & Hc') | (g & am & Hu & ->)].
  - destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfr). apply (used_metas_usedX s g am HW) in Hu as Ug.
    pose proof (inv_groups HW g am Ug) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3.
    destruct S3 as (_ & _ & (N0 & O0 & F0 & _) & _).
    destruct (marker_cells_span am i fr c ltac:(clear - O0; lia) N0 F0 Hc') as (q & Eq & Hq1 & Hq2 & Hq3).
    pose proof (slot_in_span [] None U0 s HW g am i Ug Hi) as [SI1 SI2].
    rewrite Eq. destruct q as [rq oq]. rewrite region_loc. cbn [prid poff] in Hq1, Hq2, Hq3. rewrite prid_slot_start in Hq1. subst rq.
    destruct (slot_start ah j) as [rj oj] eqn:Esj. rewrite (loc_padd L (SP rj oj) (UNIT * fr_off f)), region_loc.
    assert (Erj : rj = prid (am_mem ah)) by (rewrite <- (prid_slot_start ah j), Esj; reflexivity). subst rj.
    change oj with (poff (SP (prid (am_mem ah)) oj)). rewrite <- Esj. rewrite <- Esj in SJ1, SJ2.
    destruct (Nat.eq_dec (prid (am_mem am)) (prid (am_mem ah))) as [Er|Er].
    + rewrite Er. destruct (sptr_eq_dec g h) as [<-|Hgh].
      * pose proof (usedX_fun _ _ _ _ _ Ug Uh) as <-. destruct (Z.eq_dec i j) as [->|Hij].
        { rewrite Hfr in Hf. injection Hf as <-. unfold UNIT, IB in *. lia. }
        destruct (user_slots_disjoint s g am i fr g am j f HW Ug Ug Hi Hj Hfr Kfr Hf Kf (or_intror Hij) eq_refl) as [D|D];
          unfold UNIT, IB in *; lia.
      * destruct (user_slots_disjoint s g am i fr h ah j f HW Ug Uh Hi Hj Hfr Kfr Hf Kf (or_introl Hgh) Er) as [D|D];
          unfold UNIT, IB in *; lia.
    + destruct (used_group_region [] None U0 s g am HW Ug) as (rgG & _ & _ & _ & HoG & _).
      destruct (used_group_region [] None U0 s h ah HW Uh) as (rgH & _ & _ & _ & HoH & _).
      destruct (regions_apart s L am ah g h oq (Z.of_nat (mc_w c)) (poff (slot_start ah j) + UNIT * fr_off f) (fr_n f) HW HL Ug Uh Er
                  ltac:(clear - Hq2 SI1 HoG O0 N0; unfold UNIT in *; lia) ltac:(clear - Hq3 SI2; unfold group_extent, UNIT, IB in *; lia)
                  ltac:(clear - SJ1 HoH Of; unfold UNIT in *; lia) ltac:(clear - SJ2 Ff Nf; unfold group_extent, UNIT, IB in *; lia))
        as [D|D]; unfold group_extent, UNIT, IB in *; lia.
  - apply (used_metas_usedX s g am HW) in Hu as Ug.
    pose proof (inv_groups HW g am Ug) as ((Mlast & _) & _).
    pose proof (slot_in_span [] None U0 s HW g am (am_last am) Ug ltac:(clear - Mlast; lia)) as [SL1 SL2].
    pose proof (stride_pos _ _ _ _ _ (inv_groups HW g am Ug)) as Sg.
    unfold gend_cell, slot_end. cbn [mc_loc mc_w].
    destruct (slot_start am (am_last am)) as [rl ol] eqn:Esl. rewrite (loc_padd L (SP rl ol)), region_loc.
    assert (Erl : rl = prid (am_mem am)) by (rewrite <- (prid_slot_start am (am_last am)), Esl; reflexivity). subst rl.
    change ol with (poff (SP (prid (am_mem am)) ol)). rewrite <- Esl. rewrite <- Esl in SL1, SL2.
    destruct (slot_start ah j) as [rj oj] eqn:Esj. rewrite (loc_padd L (SP rj oj) (UNIT * fr_off f)), region_loc.
    assert (Erj : rj = prid (am_mem ah)) by (rewrite <- (prid_slot_start ah j), Esj; reflexivity). subst rj.
    change oj with (poff (SP (prid (am_mem ah)) oj)). rewrite <- Esj. rewrite <- Esj in SJ1, SJ2.
    destruct (Nat.eq_dec (prid (am_mem am)) (prid (am_mem ah))) as [Er|Er].
    + rewrite Er. destruct (gend_vs_user_slot s g am h ah j f HW Ug Uh Hj Hf Kf Er Ff ltac:(clear - Of; lia) Nf) as [D|D];
        unfold UNIT, IB in *; lia.
    + destruct (used_group_region [] None U0 s g am HW Ug) as (rgG & _ & _ & _ & HoG & _).
      destruct (used_group_region [] None U0 s h ah HW Uh) as (rgH & _ & _ & _ & HoH & _).
      destruct (regions_apart s L am ah g h (poff (slot_start am (am_last am)) + stride_of am - IB) 1
                  (poff (slot_start ah j) + UNIT * fr_off f) (fr_n f) HW HL Ug Uh Er
                  ltac:(clear - SL1 HoG Sg; unfold UNIT, IB in *; lia) ltac:(clear - SL2; unfold group_extent, UNIT, IB in *; lia)
                  ltac:(clear - SJ1 HoH Of; unfold UNIT in *; lia) ltac:(clear - SJ2 Ff Nf; unfold group_extent, UNIT, IB in *; lia)) as [D|D];
        unfold group_extent, UNIT, IB in *; lia.
Qed.
