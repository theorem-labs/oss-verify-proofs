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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngNtfPre MngNtfC AXG_ag0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition used_l (l : list (sptr * mslot)) : list (sptr * ameta) :=
  flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) l.

Lemma used_cov : forall l p am q a, In (q, a) (used_l (mupdate l p (MUsed am))) -> (q = p /\ a = am) \/ In (q, a) (used_l l).
Proof.
  induction l as [|[k y] t IH]; intros p am q a H; cbn [mupdate] in H.
  - cbn in H. destruct H as [E|[]]. injection E as -> ->. left. auto.
  - destruct (sptr_eqb p k) eqn:E.
    + apply sptr_eqb_eq in E. subst k. unfold used_l in H. cbn [flat_map] in H. cbn [app] in H. destruct H as [E|H].
      * injection E as -> ->. left. auto.
      * right. unfold used_l. cbn [flat_map]. apply in_app_iff. right. exact H.
    + unfold used_l in H. cbn [flat_map] in H. apply in_app_iff in H as [H|H].
      * right. unfold used_l. cbn [flat_map]. apply in_app_iff. left. exact H.
      * destruct (IH p am q a H) as [A|A]; [left; exact A|]. right. unfold used_l. cbn [flat_map]. apply in_app_iff. right. exact A.
Qed.

Lemma used_rev : forall l p am q a, (forall am', mlookup l p <> Some (MUsed am')) ->
  In (q, a) (used_l l) -> In (q, a) (used_l (mupdate l p (MUsed am))).
Proof.
  induction l as [|[k y] t IH]; intros p am q a Hp H; [destruct H|]. cbn [mupdate]. cbn [mlookup] in Hp.
  destruct (sptr_eqb p k) eqn:E.
  - apply sptr_eqb_eq in E. subst k. unfold used_l in H |- *. cbn [flat_map] in H |- *.
    destruct y as [pr nx | | am0]; [| | exfalso; exact (Hp am0 eq_refl)]; cbn [app] in H; right; exact H.
  - unfold used_l in H |- *. cbn [flat_map] in H |- *. apply in_app_iff in H as [H|H]; apply in_app_iff; [left; exact H|].
    right. exact (IH p am q a Hp H).
Qed.

Lemma used_new : forall l p am, In (p, am) (used_l (mupdate l p (MUsed am))).
Proof.
  induction l as [|[k y] t IH]; intros p am; cbn [mupdate]; [cbn; left; reflexivity|].
  destruct (sptr_eqb p k) eqn:E.
  - apply sptr_eqb_eq in E. subst k. unfold used_l. cbn [flat_map]. cbn [app]. left. reflexivity.
  - unfold used_l. cbn [flat_map]. apply in_app_iff. right. exact (IH p am).
Qed.

Lemma areas_cov1 : forall s s' g l c, (forall q, q <> g -> mlookup (st_metas s') q = mlookup (st_metas s) q) ->
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

Lemma areas_rev1 : forall s s' g l c, (forall q, q <> g -> mlookup (st_metas s') q = mlookup (st_metas s) q) ->
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

(* [comment removed for export] *)
Lemma msc_shape : forall q x y c, In c (meta_slot_cells q x) -> exists c', In c' (meta_slot_cells q y) /\ mc_loc c' = mc_loc c /\ mc_w c' = mc_w c.
Proof.
  intros q x y c H.
  assert (S : forall z, meta_slot_cells q z = [MCell (LMem (padd q META_prev)) 8 (match z with Some (MUsed am) => optr (am_prev am) | Some (MFree pr nx) => optr pr | _ => VZ 0 end);
        MCell (LMem (padd q META_next)) 8 (match z with Some (MUsed am) => optr (am_next am) | Some (MFree pr nx) => optr nx | _ => VZ 0 end);
        MCell (LMem (padd q META_mem)) 8 (match z with Some (MUsed am) => VP (am_mem am) | _ => VZ 0 end);
        MCell (LMem (padd q META_avail)) 4 (match z with Some (MUsed am) => VZ (am_avail am) | _ => VZ 0 end);
        MCell (LMem (padd q META_freed)) 4 (match z with Some (MUsed am) => VZ (am_freed am) | _ => VZ 0 end);
        MCell (LMem (padd q META_bits)) 8 (match z with Some (MUsed am) => VZ (meta_bits am) | _ => VZ 0 end)]).
  { intros [[pr nx | | am]|]; reflexivity. }
  rewrite S in H. rewrite S. cbn [In] in H.
  destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [eexists; split; [left; reflexivity | split; reflexivity] | eexists; split; [right; left; reflexivity | split; reflexivity]
    | eexists; split; [right; right; left; reflexivity | split; reflexivity] | eexists; split; [right; right; right; left; reflexivity | split; reflexivity]
    | eexists; split; [right; right; right; right; left; reflexivity | split; reflexivity]
    | eexists; split; [right; right; right; right; right; left; reflexivity | split; reflexivity]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctr_cell (v : Z) : mcell := MCell (LCtx CTX_mmap_counter) 4 (VZ v).

Definition ctx_same6 (s s' : astate) : Prop :=
  st_init_done s' = st_init_done s /\ st_free_meta_head s' = st_free_meta_head s /\
  st_areas s' = st_areas s /\ st_avail_meta s' = st_avail_meta s /\ st_avail_meta_count s' = st_avail_meta_count s /\
  st_avail_meta_area_count s' = st_avail_meta_area_count s /\ st_meta_alloc_shift s' = st_meta_alloc_shift s /\
  st_area_head s' = st_area_head s /\ st_area_tail s' = st_area_tail s /\ st_avail_meta_areas s' = st_avail_meta_areas s /\
  st_seq s' = st_seq s /\ st_brk s' = st_brk s /\ st_unmap_seq s' = st_unmap_seq s /\ st_bounces s' = st_bounces s.

Lemma cov_ctx6 : forall s s' c, ctx_same6 s s' -> In c (ctx_cells s') ->
  In c (ctx_cells s) \/ c = ctr_cell (st_mmap_counter s') \/ (exists k, (k < 48)%nat /\ c = act_cell k (nth k (st_active s') None)) \/
  (exists k, (k < 48)%nat /\ c = usg_cell k (nth k (st_usage s') 0)).
Proof.
  intros s s' c (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) Hc.
  unfold ctx_cells in Hc. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14 in Hc.
  apply in_app_iff in Hc as [Hc|Hc].
  - cbn [In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [first [ (right; left; reflexivity)
                                           | (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
    destruct Hc.
  - apply in_app_iff in Hc as [Hc|Hc].
    + right. right. left. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + apply in_app_iff in Hc as [Hc|Hc].
      * right. right. right. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
      * left. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

Lemma rev_ctx6 : forall s s' c, ctx_same6 s s' -> In c (ctx_cells s) ->
  In c (ctx_cells s') \/ c = ctr_cell (st_mmap_counter s) \/ (exists k, (k < 48)%nat /\ c = act_cell k (nth k (st_active s) None)) \/
  (exists k, (k < 48)%nat /\ c = usg_cell k (nth k (st_usage s) 0)).
Proof.
  intros s s' c (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) Hc.
  unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc].
  - cbn [In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [first [ (right; left; reflexivity)
                                           | (left; unfold ctx_cells; rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12;
                                              apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
    destruct Hc.
  - apply in_app_iff in Hc as [Hc|Hc].
    + right. right. left. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + apply in_app_iff in Hc as [Hc|Hc].
      * right. right. right. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
      * left. unfold ctx_cells. rewrite E13, E14. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mupdate_twice' : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
  induction l as [|[q z] t IH]; intros p x y; cbn [mupdate]; [rewrite sptr_eqb_refl; reflexivity|].
  destruct (sptr_eqb p q) eqn:E; cbn [mupdate]; rewrite E; [reflexivity | rewrite IH; reflexivity].
Qed.

Section S6.
Variables (mt : sptr) (sc cnt aidx maplen : Z) (r : nat) (s3 : astate) (len : Z).

Local Notation am6 := (am_set_links (Some mt) (Some mt) (new_am (SP r 0) sc cnt aidx maplen slot_zero)).
Local Notation s6 := (ins_st mt sc cnt aidx maplen (SP r 0) slot_zero (ag_s5 s3 len)).

#[using="Type"] Lemma s6_same : ctx_same6 s3 s6.
Proof. LiaFast.lf_pins LiaFast.u0. unfold ins_st, ag_s5. cbn. repeat split; reflexivity. Qed.

#[using="Type"] Lemma s6_metas : st_metas s6 = mupdate (st_metas s3) mt (MUsed am6).
Proof. LiaFast.lf_pins LiaFast.u0. unfold ins_st, ag_s5. cbn [st_metas set_active set_metas set_usage set_mmap_counter set_regions]. apply mupdate_twice'. Qed.

#[using="Type"] Lemma s6_active : st_active s6 = lupd (st_active s3) (Z.to_nat sc) (Some mt).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma s6_usage : st_usage s6 = zset sc (usage_of s3 sc + cnt) (st_usage s3).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma s6_counter : st_mmap_counter s6 = Z.land (st_mmap_counter s3 + 1) (2^32 - 1).
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma s6_regions : st_regions s6 = st_regions s3 ++ [mkRegion RkMap (page_round len) [] true].
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma s6_areas : st_areas s6 = st_areas s3.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma s6_lookup : forall q, q <> mt -> mlookup (st_metas s6) q = mlookup (st_metas s3) q.
Proof. LiaFast.lf_pins LiaFast.u0. intros q Hq. rewrite s6_metas. apply mlookup_mupdate_other. exact Hq. Qed.

#[using="Type"] Lemma s6_lookup_mt : mlookup (st_metas s6) mt = Some (MUsed am6).
Proof. LiaFast.lf_pins LiaFast.u0. rewrite s6_metas. apply mlookup_mupdate_same. Qed.

Definition Cnew6 : list mcell :=
  [ctr_cell (st_mmap_counter s6); usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s6) 0); act_cell (Z.to_nat sc) (Some mt)]
  ++ meta_slot_cells mt (Some (MUsed am6)) ++ group_cells mt am6.

Hypothesis Hsc : 0 <= sc <= 47.
Hypothesis Hlen_act : length (st_active s3) = 48%nat.
Hypothesis Hlen_usg : length (st_usage s3) = 48%nat.
Hypothesis Hraw : forall am', mlookup (st_metas s3) mt <> Some (MUsed am').

#[using="Hlen_act Hlen_usg"] Theorem cov6 : forall c, In c (image s6) -> In c (image s3) \/ In c Cnew6.
Proof. LiaFast.lf_pins (fun (Hlen_act Hlen_usg : LiaFast.U) => LiaFast.u0).
  intros c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (cov_ctx6 s3 s6 c s6_same Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + right. unfold Cnew6. left. symmetry. exact A.
    + rewrite s6_active in A. destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hne].
      * right. rewrite nth_lupd_same in A by lia. unfold Cnew6. right. right. left. symmetry. exact A.
      * left. rewrite nth_lupd_other in A by exact Hne. subst c. apply act_in_ctx_img. exact Hk.
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hne].
      * right. unfold Cnew6. right. left. symmetry. exact A.
      * left. rewrite s6_usage in A. unfold zset in A. rewrite nth_zupd_other in A by exact Hne. subst c. apply ctx_in_image. apply usage_in_ctx. exact Hk.
  - apply in_app_iff in Hc as [Hc|Hc].
    + rewrite s6_areas in Hc. destruct (areas_cov1 s3 s6 mt (st_areas s3) c s6_lookup Hc) as [A|A].
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. left. exact A.
      * right. rewrite s6_lookup_mt in A. unfold Cnew6. apply in_app_iff. right. apply in_app_iff. left. exact A.
    + apply in_flat_map in Hc as ((q & a) & Hq & Hcq). unfold used_metas in Hq. rewrite s6_metas in Hq.
      destruct (used_cov (st_metas s3) mt am6 q a Hq) as [(-> & ->)|A].
      * right. unfold Cnew6. apply in_app_iff. right. apply in_app_iff. right. exact Hcq.
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (q, a). split; [exact A | exact Hcq].
Qed.

#[using="Hraw"] Theorem rev6 : forall L c, In c (image s3) -> In c (image s6) \/ exists c', In c' Cnew6 /\ cell_range L c' = cell_range L c.
Proof. LiaFast.lf_pins (fun (Hraw : LiaFast.U) => LiaFast.u0).
  intros L c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (rev_ctx6 s3 s6 c s6_same Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + right. exists (ctr_cell (st_mmap_counter s6)). split; [unfold Cnew6; left; reflexivity|]. subst c. reflexivity.
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hne].
      * right. exists (act_cell (Z.to_nat sc) (Some mt)). split; [unfold Cnew6; right; right; left; reflexivity|]. subst c. reflexivity.
      * left. subst c. rewrite <- (nth_lupd_other (st_active s3) (Z.to_nat sc) k (Some mt) None Hne). rewrite <- s6_active. apply act_in_ctx_img. exact Hk.
    + destruct (Nat.eq_dec k (Z.to_nat sc)) as [->|Hne].
      * right. exists (usg_cell (Z.to_nat sc) (nth (Z.to_nat sc) (st_usage s6) 0)). split; [unfold Cnew6; right; left; reflexivity|]. subst c. reflexivity.
      * left. subst c. unfold usg_cell. rewrite <- (nth_zupd_other (st_usage s3) (Z.to_nat sc) k (usage_of s3 sc + cnt) 0 Hne).
        change (zupd (st_usage s3) (Z.to_nat sc) (usage_of s3 sc + cnt)) with (st_usage s6). apply ctx_in_image. apply usage_in_ctx. exact Hk.
  - apply in_app_iff in Hc as [Hc|Hc].
    + destruct (areas_rev1 s3 s6 mt (st_areas s3) c s6_lookup Hc) as [A|A].
      * left. unfold image. apply in_app_iff. right. apply in_app_iff. left. rewrite s6_areas. exact A.
      * right. destruct (msc_shape mt (mlookup (st_metas s3) mt) (Some (MUsed am6)) c A) as (c' & Hc' & E1 & E2).
        exists c'. split; [unfold Cnew6; apply in_app_iff; right; apply in_app_iff; left; exact Hc'|]. unfold cell_range. rewrite E1, E2. reflexivity.
    + left. apply in_flat_map in Hc as ((q & a) & Hq & Hcq). unfold image. apply in_app_iff. right. apply in_app_iff. right.
      apply in_flat_map. exists (q, a). split; [|exact Hcq]. unfold used_metas. rewrite s6_metas. exact (used_rev (st_metas s3) mt am6 q a Hraw Hq).
Qed.

#[using="Hsc Hlen_act Hlen_usg"] Theorem in6 : KS s6 -> forall c, In c Cnew6 -> In c (image s6).
Proof. LiaFast.lf_pins (fun (Hsc Hlen_act Hlen_usg : LiaFast.U) => LiaFast.u0).
  intros HK c Hc. unfold Cnew6 in Hc. cbn [In app] in Hc. destruct Hc as [<-|[<-|[<-|Hc]]].
  - apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. cbn [In]. unfold ctr_cell. repeat first [ (left; reflexivity) | right ].
  - apply ctx_in_image. apply usage_in_ctx. lia.
  - replace (Some mt) with (nth (Z.to_nat sc) (st_active s6) None) by (rewrite s6_active; apply nth_lupd_same; lia).
    apply act_in_ctx_img. lia.
  - apply in_app_iff in Hc as [Hc|Hc].
    + exact (msc_key_in_image s6 mt (MUsed am6) c HK s6_lookup_mt Hc).
    + unfold image. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists (mt, am6). split; [|exact Hc].
      unfold used_metas. rewrite s6_metas. apply used_new.
Qed.
End S6.
