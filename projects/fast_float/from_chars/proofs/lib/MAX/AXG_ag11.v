(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngNtfPre MngNtfC AXG_ag0 AXG_ag5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma used_rev_upd : forall l p x q a, In (q, a) (used_l l) ->
  (q = p /\ mlookup l p = Some (MUsed a)) \/ In (q, a) (used_l (mupdate l p x)).
Proof.
  induction l as [|[k y] t IH]; intros p x q a H; [destruct H|]. cbn [mupdate mlookup].
  destruct (sptr_eqb p k) eqn:E.
  - apply sptr_eqb_eq in E. subst k. unfold used_l in H |- *. cbn [flat_map] in H |- *. apply in_app_iff in H as [H|H].
    + destruct y as [pr nx| |am0]; cbn in H; [destruct H | destruct H |]. destruct H as [Eq|[]]. injection Eq as -> ->. left. auto.
    + right. apply in_app_iff. right. exact H.
  - unfold used_l in H |- *. cbn [flat_map] in H |- *. apply in_app_iff in H as [H|H].
    + right. apply in_app_iff. left. exact H.
    + destruct (IH p x q a H) as [A|A]; [left; exact A | right; apply in_app_iff; right; exact A].
Qed.

(* [comment removed for export] *)
Definition nest_hdr (amg : ameta) (idx : Z) : Z * Z := (idx + 192, (stride_of amg * idx) / UNIT).
Definition nest_slot (amg : ameta) (idx n : Z) : slotst := mkSlot (Some (nest_hdr amg idx)) (Some (mkFrame 0 n FGroup)).
Definition amg' (amg : ameta) (idx n : Z) : ameta := upd_slot amg idx (nest_slot amg idx n).

Lemma msc_upd_slot : forall q am i x, meta_slot_cells q (Some (MUsed (upd_slot am i x))) = meta_slot_cells q (Some (MUsed am)).
Proof. intros q am i x. reflexivity. Qed.

(* [comment removed for export] *)
Definition hdr_cells (amg : ameta) (idx : Z) : list mcell :=
  [MCell (LMem (padd (slot_start amg idx) (-3))) 1 (VZ (fst (nest_hdr amg idx)));
   MCell (LMem (padd (slot_start amg idx) (-2))) 2 (VZ (snd (nest_hdr amg idx)))].

Lemma slot_cells_nest : forall amg idx n, 0 <= idx -> (Z.to_nat idx < length (am_slots amg))%nat ->
  slot_cells (amg' amg idx n) idx = MCell (LMem (padd (slot_start amg idx) (-4))) 1 (VZ 0) :: hdr_cells amg idx.
Proof.
  intros amg idx n H0 Hl. unfold slot_cells, amg'. rewrite (nth_slot_upd_slot amg idx idx _ H0 H0 Hl). rewrite Z.eqb_refl.
  pose proof (upd_slot_fields amg idx (nest_slot amg idx n)) as (_ & _ & _ & _ & _ & _ & SS). rewrite SS.
  cbn [nest_slot ss_hdr ss_fr fr_off Z.eqb app]. reflexivity.
Qed.

Lemma group_cells_cov_nest : forall g amg idx n c, 0 <= idx <= am_last amg -> (Z.to_nat idx < length (am_slots amg))%nat ->
  In c (group_cells g (amg' amg idx n)) -> In c (group_cells g amg) \/ In c (hdr_cells amg idx).
Proof.
  intros g amg idx n c Hi Hl Hc. pose proof (upd_slot_fields amg idx (nest_slot amg idx n)) as (EM & EL & ESC & EML & _ & _ & SS).
  unfold group_cells in Hc |- *. unfold amg' in Hc. rewrite EM, EL, EML in Hc. cbn [am_aidx upd_slot am_set_slots] in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; left; exact Hc|].
  apply in_flat_map in Hc as (i & Hi' & Hci). apply In_zseq in Hi'.
  destruct (Z.eq_dec i idx) as [->|Hne].
  - change (upd_slot amg idx (nest_slot amg idx n)) with (amg' amg idx n) in Hci. rewrite slot_cells_nest in Hci by lia.
    destruct Hci as [<-|Hci]; [|right; exact Hci]. left. apply in_app_iff. right. apply in_flat_map. exists idx. split; [apply In_zseq; lia|].
    unfold slot_cells. left. reflexivity.
  - left. apply in_app_iff. right. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
    unfold slot_cells in Hci |- *. rewrite SS in Hci. rewrite (nth_slot_upd_slot amg idx i _ ltac:(lia) ltac:(lia) Hl) in Hci.
    replace (i =? idx) with false in Hci by (symmetry; apply Z.eqb_neq; exact Hne). exact Hci.
Qed.

Lemma group_cells_rev_nest : forall g amg idx n c, 0 <= idx <= am_last amg -> (Z.to_nat idx < length (am_slots amg))%nat ->
  ss_fr (nth_slot amg idx) = None ->
  In c (group_cells g amg) -> In c (group_cells g (amg' amg idx n)) \/ (exists c', In c' (hdr_cells amg idx) /\ mc_loc c' = mc_loc c /\ mc_w c' = mc_w c).
Proof.
  intros g amg idx n c Hi Hl Hfr Hc. pose proof (upd_slot_fields amg idx (nest_slot amg idx n)) as (EM & EL & ESC & EML & _ & _ & SS).
  unfold group_cells in Hc |- *. unfold amg'. rewrite EM, EL, EML. cbn [am_aidx upd_slot am_set_slots].
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; left; exact Hc|].
  apply in_flat_map in Hc as (i & Hi' & Hci). apply In_zseq in Hi'.
  destruct (Z.eq_dec i idx) as [->|Hne].
  - unfold slot_cells in Hci. rewrite Hfr in Hci. cbn [app] in Hci. rewrite app_nil_r in Hci. destruct Hci as [<-|Hci].
    + left. apply in_app_iff. right. apply in_flat_map. exists idx. split; [apply In_zseq; lia|].
      change (upd_slot amg idx (nest_slot amg idx n)) with (amg' amg idx n). rewrite slot_cells_nest by lia. left. reflexivity.
    + right. destruct (ss_hdr (nth_slot amg idx)) as [[h3 h16]|]; [|destruct Hci]. destruct Hci as [<-|[<-|[]]].
      * exists (MCell (LMem (padd (slot_start amg idx) (-3))) 1 (VZ (fst (nest_hdr amg idx)))). split; [left; reflexivity | split; reflexivity].
      * exists (MCell (LMem (padd (slot_start amg idx) (-2))) 2 (VZ (snd (nest_hdr amg idx)))). split; [right; left; reflexivity | split; reflexivity].
  - left. apply in_app_iff. right. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
    unfold slot_cells in Hci |- *. rewrite SS. rewrite (nth_slot_upd_slot amg idx i _ ltac:(lia) ltac:(lia) Hl).
    replace (i =? idx) with false by (symmetry; apply Z.eqb_neq; exact Hne). exact Hci.
Qed.

Lemma areas_cov1' : forall s s' g l c, (forall q, q <> g -> meta_slot_cells q (mlookup (st_metas s') q) = meta_slot_cells q (mlookup (st_metas s) q)) ->
  In c (areas_cells s' l) -> In c (areas_cells s l) \/ In c (meta_slot_cells g (mlookup (st_metas s') g)).
Proof.
  intros s s' g l c HQ. induction l as [|a t IH]; intros H; [destruct H|]. cbn [areas_cells] in H |- *.
  apply in_app_iff in H as [H|H]; [|destruct (IH H) as [A|A]; [left; apply in_app_iff; right; exact A | right; exact A]].
  unfold area_cells in H. apply in_app_iff in H as [H|H]; [left; apply in_app_iff; left; unfold area_cells; apply in_app_iff; left; exact H|].
  apply in_flat_map in H as (k & Hk & Hc).
  destruct (sptr_eq_dec (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) as [E|E].
  - right. rewrite <- E. exact Hc.
  - left. apply in_app_iff. left. unfold area_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|].
    rewrite <- (HQ _ E). exact Hc.
Qed.

Lemma areas_rev1' : forall s s' g l c, (forall q, q <> g -> meta_slot_cells q (mlookup (st_metas s') q) = meta_slot_cells q (mlookup (st_metas s) q)) ->
  In c (areas_cells s l) -> In c (areas_cells s' l) \/ In c (meta_slot_cells g (mlookup (st_metas s) g)).
Proof.
  intros s s' g l c HQ. induction l as [|a t IH]; intros H; [destruct H|]. cbn [areas_cells] in H |- *.
  apply in_app_iff in H as [H|H]; [|destruct (IH H) as [A|A]; [left; apply in_app_iff; right; exact A | right; exact A]].
  unfold area_cells in H. apply in_app_iff in H as [H|H]; [left; apply in_app_iff; left; unfold area_cells; apply in_app_iff; left; exact H|].
  apply in_flat_map in H as (k & Hk & Hc).
  destruct (sptr_eq_dec (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) as [E|E].
  - right. rewrite <- E. exact Hc.
  - left. apply in_app_iff. left. unfold area_cells. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|].
    rewrite (HQ _ E). exact Hc.
Qed.

Section SN.
Variables (mt g : sptr) (amg : ameta) (sc cnt0 idx n : Z) (s4 : astate).

Local Notation p := (padd (slot_start amg idx) 0).
Local Notation am_n := (am_set_links (Some mt) (Some mt) (new_am p sc cnt0 (cnt0 - 1) 0 slot_junk)).
Local Notation s6n := (ins_st mt sc cnt0 (cnt0 - 1) 0 p slot_junk (ef_grp_st g amg idx n s4)).

Hypothesis Hne : g <> mt.
Hypothesis Mg : mlookup (st_metas s4) g = Some (MUsed amg).
Hypothesis Hraw : forall am', mlookup (st_metas s4) mt <> Some (MUsed am').
Hypothesis Hidx : 0 <= idx <= am_last amg.
Hypothesis Hlen_sl : (Z.to_nat idx < length (am_slots amg))%nat.
Hypothesis Hfr : ss_fr (nth_slot amg idx) = None.
Hypothesis Hsc : 0 <= sc <= 47.
Hypothesis Hlen_act : length (st_active s4) = 48%nat.
Hypothesis Hlen_usg : length (st_usage s4) = 48%nat.

#[using="Type"] Lemma sn_metas : st_metas s6n = mupdate (mupdate (st_metas s4) g (MUsed (amg' amg idx n))) mt (MUsed am_n).
Proof. LiaFast.lf_pins LiaFast.u0. unfold ins_st, ef_grp_st. cbn [st_metas set_active set_metas set_usage]. rewrite mupdate_twice'. reflexivity. Qed.

#[using="Type"] Lemma sn_lookup : forall q, q <> mt -> q <> g -> mlookup (st_metas s6n) q = mlookup (st_metas s4) q.
Proof. LiaFast.lf_pins LiaFast.u0. intros q H1 H2. rewrite sn_metas. rewrite !mlookup_mupdate_other by assumption. reflexivity. Qed.

#[using="Type"] Lemma sn_lookup_mt : mlookup (st_metas s6n) mt = Some (MUsed am_n).
Proof. LiaFast.lf_pins LiaFast.u0. rewrite sn_metas. apply mlookup_mupdate_same. Qed.

#[using="Hne"] Lemma sn_lookup_g : mlookup (st_metas s6n) g = Some (MUsed (amg' amg idx n)).
Proof. LiaFast.lf_pins (fun (Hne : LiaFast.U) => LiaFast.u0). rewrite sn_metas. rewrite mlookup_mupdate_other by exact Hne. apply mlookup_mupdate_same. Qed.

#[using="Hne Mg"] Lemma sn_msc : forall q, q <> mt -> meta_slot_cells q (mlookup (st_metas s6n) q) = meta_slot_cells q (mlookup (st_metas s4) q).
Proof. LiaFast.lf_pins (fun (Hne Mg : LiaFast.U) => LiaFast.u0).
  intros q Hq. destruct (sptr_eq_dec q g) as [->|Hg]; [|rewrite sn_lookup by assumption; reflexivity].
  rewrite sn_lookup_g, Mg. unfold amg'. apply msc_upd_slot.
Qed.

#[using="Type"] Lemma sn_same : ctx_same6 s4 s6n.
Proof. LiaFast.lf_pins LiaFast.u0. unfold ins_st, ef_grp_st. cbn. repeat split; reflexivity. Qed.

Definition CnewN : list mcell :=
  [usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s6n) 0); act_cell (Z.to_nat sc) (Some mt)]
  ++ meta_slot_cells mt (Some (MUsed am_n)) ++ hdr_cells amg idx ++ group_cells mt am_n.

#[using="Hne Mg Hidx Hlen_sl Hlen_act Hlen_usg"] Theorem covN : forall c, In c (image s6n) -> In c (image s4) \/ In c CnewN.
Proof. LiaFast.lf_pins (fun (Hne Mg Hidx Hlen_sl Hlen_act Hlen_usg : LiaFast.U) => LiaFast.u0).
  intros c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (cov_ctx6 s4 s6n c sn_same Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + left. subst c. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. cbn [In]. unfold ctr_cell.
      replace (st_mmap_counter s6n) with (st_mmap_counter s4) by reflexivity. repeat first [ (left; reflexivity) | right ].
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hk'].
      * right. change (st_active s6n) with (lupd (st_active (ef_grp_st g amg idx n s4)) (Z.to_nat sc) (Some mt)) in A.
        rewrite nth_lupd_same in A by (cbn [st_active ef_grp_st set_metas]; lia). unfold CnewN. right. left. symmetry. exact A.
      * left. change (st_active s6n) with (lupd (st_active (ef_grp_st g amg idx n s4)) (Z.to_nat sc) (Some mt)) in A.
        rewrite nth_lupd_other in A by exact Hk'. change (st_active (ef_grp_st g amg idx n s4)) with (st_active s4) in A.
        subst c. apply act_in_ctx_img. exact Hk.
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hk'].
      * right. unfold CnewN. left. symmetry. exact A.
      * left. change (st_usage s6n) with (zset sc (usage_of (ef_grp_st g amg idx n s4) sc + cnt0) (st_usage (ef_grp_st g amg idx n s4))) in A.
        unfold zset in A. rewrite nth_zupd_other in A by exact Hk'. change (st_usage (ef_grp_st g amg idx n s4)) with (st_usage s4) in A.
        subst c. apply ctx_in_image. apply usage_in_ctx. exact Hk.
  - apply in_app_iff in Hc as [Hc|Hc].
    + change (st_areas s6n) with (st_areas s4) in Hc. destruct (areas_cov1' s4 s6n mt (st_areas s4) c sn_msc Hc) as [A|A].
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. left. exact A.
      * right. rewrite sn_lookup_mt in A. unfold CnewN. apply in_app_iff. right. apply in_app_iff. left. exact A.
    + apply in_flat_map in Hc as ((q & a) & Hq & Hcq). unfold used_metas in Hq. rewrite sn_metas in Hq.
      destruct (used_cov _ mt am_n q a Hq) as [(-> & ->)|A].
      * right. unfold CnewN. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hcq.
      * destruct (used_cov _ g (amg' amg idx n) q a A) as [(-> & ->)|B].
        -- cbn [fst snd] in Hcq. destruct (group_cells_cov_nest g amg idx n c Hidx Hlen_sl Hcq) as [C|C].
           ++ left. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (g, amg). split; [|exact C].
              unfold used_metas. clear - Mg. induction (st_metas s4) as [|[k y] t IH]; [discriminate Mg|]. cbn [mlookup] in Mg.
              unfold used_l. cbn [flat_map]. destruct (sptr_eqb g k) eqn:E.
              ** apply sptr_eqb_eq in E. subst k. injection Mg as ->. cbn. left. reflexivity.
              ** apply in_app_iff. right. exact (IH Mg).
           ++ right. unfold CnewN. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact C.
        -- left. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (q, a). split; [exact B | exact Hcq].
Qed.

#[using="Mg"] Lemma used_g_s4 : In (g, amg) (used_metas s4).
Proof. LiaFast.lf_pins (fun (Mg : LiaFast.U) => LiaFast.u0).
  unfold used_metas. clear - Mg. induction (st_metas s4) as [|[k y] t IH]; [discriminate Mg|]. cbn [mlookup] in Mg.
  unfold used_l. cbn [flat_map]. destruct (sptr_eqb g k) eqn:E.
  - apply sptr_eqb_eq in E. subst k. injection Mg as ->. cbn. left. reflexivity.
  - apply in_app_iff. right. exact (IH Mg).
Qed.

#[using="Hne Hraw"] Lemma used_g_s6 : In (g, amg' amg idx n) (used_metas s6n).
Proof. LiaFast.lf_pins (fun (Hne Hraw : LiaFast.U) => LiaFast.u0).
  unfold used_metas. rewrite sn_metas. apply used_rev; [|apply used_new].
  intros am' E. rewrite mlookup_mupdate_other in E by (intros E'; apply Hne; symmetry; exact E'). exact (Hraw am' E).
Qed.

#[using="Hne Mg Hraw Hidx Hlen_sl Hfr"] Theorem revN : forall L c, In c (image s4) -> In c (image s6n) \/ exists c', In c' CnewN /\ cell_range L c' = cell_range L c.
Proof. LiaFast.lf_pins (fun (Hne Mg Hraw Hidx Hlen_sl Hfr : LiaFast.U) => LiaFast.u0).
  intros L c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (rev_ctx6 s4 s6n c sn_same Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + left. subst c. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. cbn [In]. unfold ctr_cell.
      replace (st_mmap_counter s4) with (st_mmap_counter s6n) by reflexivity. repeat first [ (left; reflexivity) | right ].
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hk'].
      * right. exists (act_cell (Z.to_nat sc) (Some mt)). split; [unfold CnewN; right; left; reflexivity|]. subst c. reflexivity.
      * left. subst c. rewrite <- (nth_lupd_other (st_active s4) (Z.to_nat sc) k (Some mt) None Hk').
        change (lupd (st_active s4) (Z.to_nat sc) (Some mt)) with (st_active s6n). apply act_in_ctx_img. exact Hk.
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hk'].
      * right. exists (usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s6n) 0)). split; [unfold CnewN; left; reflexivity|]. subst c. reflexivity.
      * left. subst c. unfold usg_cell. rewrite <- (nth_zupd_other (st_usage s4) (Z.to_nat sc) k (usage_of s4 sc + cnt0) 0 Hk').
        change (zupd (st_usage s4) (Z.to_nat sc) (usage_of s4 sc + cnt0)) with (st_usage s6n). apply ctx_in_image. apply usage_in_ctx. exact Hk.
  - apply in_app_iff in Hc as [Hc|Hc].
    + destruct (areas_rev1' s4 s6n mt (st_areas s4) c sn_msc Hc) as [A|A].
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. left. exact A.
      * right. destruct (msc_shape mt (mlookup (st_metas s4) mt) (Some (MUsed am_n)) c A) as (c' & Hc' & E1 & E2).
        exists c'. split; [unfold CnewN; apply in_app_iff; right; apply in_app_iff; left; exact Hc'|]. unfold cell_range. rewrite E1, E2. reflexivity.
    + apply in_flat_map in Hc as ((q & a) & Hq & Hcq). unfold used_metas in Hq.
      destruct (used_rev_upd (st_metas s4) g (MUsed (amg' amg idx n)) q a Hq) as [(-> & Ea)|B].
      * rewrite Mg in Ea. injection Ea as <-. cbn [fst snd] in Hcq.
        destruct (group_cells_rev_nest g amg idx n c Hidx Hlen_sl Hfr Hcq) as [C|(c' & Hc' & E1 & E2)].
        -- left. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (g, amg' amg idx n). split; [exact used_g_s6 | exact C].
        -- right. exists c'. split; [unfold CnewN; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hc'|].
           unfold cell_range. rewrite E1, E2. reflexivity.
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (q, a). split; [|exact Hcq].
        unfold used_metas. rewrite sn_metas. apply used_rev; [|exact B].
        intros am' E. rewrite mlookup_mupdate_other in E by (intros E'; apply Hne; symmetry; exact E'). exact (Hraw am' E).
Qed.

#[using="Hne Hraw Hidx Hlen_sl Hsc Hlen_act Hlen_usg"] Theorem inN : KS s6n -> forall c, In c CnewN -> In c (image s6n).
Proof. LiaFast.lf_pins (fun (Hne Hraw Hidx Hlen_sl Hsc Hlen_act Hlen_usg : LiaFast.U) => LiaFast.u0).
  intros HK c Hc. unfold CnewN in Hc. cbn [In app] in Hc. destruct Hc as [<-|[<-|Hc]].
  - apply ctx_in_image. apply usage_in_ctx. lia.
  - replace (Some mt) with (nth (Z.to_nat sc) (st_active s6n) None) by (change (st_active s6n) with (lupd (st_active s4) (Z.to_nat sc) (Some mt)); apply nth_lupd_same; lia).
    apply act_in_ctx_img. lia.
  - apply in_app_iff in Hc as [Hc|Hc].
    + exact (msc_key_in_image s6n mt (MUsed am_n) c HK sn_lookup_mt Hc).
    + apply in_app_iff in Hc as [Hc|Hc].
      * unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (g, amg' amg idx n). split; [exact used_g_s6|].
        cbn [fst snd]. unfold group_cells. apply in_app_iff. right. apply in_flat_map. exists idx. split; [apply In_zseq; pose proof (upd_slot_fields amg idx (nest_slot amg idx n)) as (_ & EL & _); unfold amg'; rewrite EL; lia|].
        rewrite slot_cells_nest by lia. right. exact Hc.
      * unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (mt, am_n). split; [|exact Hc].
        unfold used_metas. rewrite sn_metas. apply used_new.
Qed.
End SN.
