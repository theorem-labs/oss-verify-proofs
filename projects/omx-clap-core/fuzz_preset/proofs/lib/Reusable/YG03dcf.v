(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG03.v, with its module paths changed; its addresses are still cgif_file_fuzzer.asan's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG03.v (maybe_drain_okx :1242-1298 and
   free_ok :1432-1439) for fuzz_preset's drain maybe_drain_cf (YG00cf.v), which runs the runtime's MergeBatches where cgif's
   maybe_drain had an mcheck, with structural fuels. New: the preservation lemmas of merge_batches_cf (items kept as a list,
   batch selves kept as a multiset, only empty batches extracted, kBatchBytes per extraction, the quarantine's group shape
   kept). The drain proof follows maybe_drain_okx on the event-free invariant of YG03cf.v and recycles the extracted batches
   with the popped ones; ml_free_cf is free_cf's law, from YG03cf.v's ml_free_with_cf. *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: wfr_fields_d3 / wfr_easy_d3 carry the new field wfr_qsize; RI_merge_cf proves it
   (the merge keeps the items). *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YG03dcf.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfTok YG03cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

Section YG03DCF.
Context {cp : CfParams}.

(* YG03cf.v's field tactics (Ltac does not leave its section), restated for this file. *)
Ltac wfr_fields_d3 W :=
pose proof (wfr_len_regions _ _ _ _ _ W) as Xlr; pose proof (wfr_len_cache _ _ _ _ _ W) as Xlc;
pose proof (wfr_reg0 _ _ _ _ _ W) as Xr0; pose proof (wfr_classes _ _ _ _ _ W) as Xcl;
pose proof (wfr_chunks _ _ _ _ _ W) as Xck; pose proof (wfr_chunks_nodup _ _ _ _ _ W) as Xnd;
pose proof (wfr_chunks_ev _ _ _ _ _ W) as Xcev; pose proof (wfr_prim_ev _ _ _ _ _ W) as Xpev;
pose proof (wfr_live _ _ _ _ _ W) as Xlive; pose proof (wfr_quarantine _ _ _ _ _ W) as Xq;
pose proof (wfr_batches_ev _ _ _ _ _ W) as Xbev; pose proof (wfr_secondary _ _ _ _ _ W) as Xsec;
pose proof (wfr_fakestack _ _ _ _ _ W) as Xfs; pose proof (wfr_depot _ _ _ _ _ W) as Xdep;
pose proof (wfr_nev _ _ _ _ _ W) as Xnev; pose proof (wfr_slack _ _ _ _ _ W) as Xsl;
pose proof (wfr_qinited _ _ _ _ _ W) as Xqi; pose proof (wfr_secs_ev _ _ _ _ _ W) as Xsev;
pose proof (wfr_sec_live _ _ _ _ _ W) as Xslv; pose proof (wfr_qsize _ _ _ _ _ W) as Xqs.
Ltac wfr_easy_d3 :=
first [ assumption
| match goal with H : wf_quar ?s0 |- wf_quar _ => apply (wf_quar_ext s0); [reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : Forall (fun k => ck_n k <= kQuarantineMax) (q_items ?s0) |- Forall (fun k => ck_n k <= kQuarantineMax) (q_items _) =>
apply (qsize_ext s0); [reflexivity | reflexivity | exact H] end
| match goal with H : wf_sec_cf ?s0 |- wf_sec_cf _ => apply (wf_sec_cf_ext s0); [reflexivity | reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : wf_fs ?s0 |- wf_fs _ => apply (wf_fs_ext s0); [reflexivity | exact H] end
| match goal with H : all_batches ?s0 <> [] -> st_cache_inited ?s0 = true |- all_batches _ <> [] -> st_cache_inited _ = true =>
first [ exact H | (intros ?HB; apply H; exact HB) ] end
| match goal with |- Z.of_nat (length (st_secs _)) + _ <= st_nev _ =>
solve [ cbn [st_secs st_nev set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_sec_arr set_sec_reserved
set_cache_inited set_internal_inited set_fs]; lia ] end
| match goal with |- Z.of_nat (length (st_sec_arr _)) <= cf_sec_live_max =>
solve [ cbn [st_sec_arr set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_secs set_sec_reserved
set_cache_inited set_internal_inited set_fs]; lia ] end
| idtac ].

(* ---------------------------------------------------------------------------- *)
(* 1. merge_batches_cf (YG00cf.v:282-296).                                       *)
Definition bok_cf (b : batch) : Prop :=
(1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat /\ Forall (fun k => 0 <= ck_n k) (b_items b).
(* The shape wq_groups (YG01.v:299) gives the global list. *)
Definition qsegs_cf (l : list batch) : Prop :=
exists F GS, l = F ++ concat GS /\ Forall bfull (removelast F) /\ Forall qgroup_ok GS.

Lemma b_bytes_merge_cf : forall x b1 b2, b_bytes (mkBatch x (b_items b1 ++ b_items b2)) + kBatchBytes = b_bytes b1 + b_bytes b2.
Proof. intros x b1 b2. unfold b_bytes. cbn [b_items]. rewrite (fold_right_add_app ck_n). lia. Qed.

Lemma b_bytes_ge_cf : forall b, Forall (fun k => 0 <= ck_n k) (b_items b) -> kBatchBytes <= b_bytes b.
Proof.
intros b H. unfold b_bytes. assert (0 <= fold_right (fun k acc => ck_n k + acc) 0 (b_items b)); [|lia].
induction H as [|k t Hk Ht IH]; cbn [fold_right]; lia.
Qed.

Lemma flat_items_empty_cf : forall ex, Forall (fun b => b_items b = []) ex -> flat_map b_items ex = [].
Proof. intros ex H. induction H as [|b t Hb Ht IH]; [reflexivity|]. cbn [flat_map]. rewrite Hb, IH. reflexivity. Qed.

Lemma perm_front_cf : forall (A B C D E : list Z), Permutation (A ++ B ++ C ++ (D ++ E)) (E ++ A ++ B ++ C ++ D).
Proof.
intros. replace (A ++ B ++ C ++ (D ++ E)) with ((A ++ B ++ C ++ D) ++ E) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_comm.
Qed.

Lemma merge_batches_basic_cf : forall fuel l l' ex, merge_batches_cf fuel l = (l', ex) ->
flat_map b_items l' = flat_map b_items l /\
Permutation (map b_self l) (map b_self l' ++ map b_self ex) /\
Forall (fun b => b_items b = []) ex /\
sum_bytes l = sum_bytes l' + kBatchBytes * Z.of_nat (length ex) /\
(length l' + length ex = length l)%nat /\
(Forall bok_cf l -> Forall bok_cf l').
Proof.
induction fuel as [|f IH]; intros l l' ex H.
- cbn [merge_batches_cf] in H. injection H as <- <-. cbn [map length].
  splits; [reflexivity | rewrite app_nil_r; apply Permutation_refl | constructor | lia | lia | auto].
- destruct l as [|b1 [|b2 t]].
  + cbn [merge_batches_cf] in H. injection H as <- <-. cbn [map length app].
    splits; [reflexivity | apply Permutation_refl | constructor | lia | lia | auto].
  + cbn [merge_batches_cf] in H. injection H as <- <-. cbn [map length app].
    splits; [reflexivity | apply Permutation_refl | constructor | lia | lia | auto].
  + cbn [merge_batches_cf] in H. revert H. destruct (Nat.leb _ _) eqn:E; intros H.
    * revert H. destruct (merge_batches_cf f _) as [rest ex'] eqn:R. intros H. injection H as <- <-.
      destruct (IH _ _ _ R) as (I1 & I2 & I3 & I4 & I5 & I6).
      pose proof (b_bytes_merge_cf (b_self b1) b1 b2) as BB.
      splits.
      -- rewrite I1. cbn [flat_map b_items]. rewrite app_assoc. reflexivity.
      -- cbn [map b_self] in I2 |- *. eapply Permutation_trans; [apply perm_swap|].
         eapply Permutation_trans; [apply perm_skip; exact I2|]. apply Permutation_middle.
      -- constructor; [reflexivity | exact I3].
      -- unfold sum_bytes in *. cbn [fold_right length] in *. rewrite Nat2Z.inj_succ. unfold kBatchBytes in *. lia.
      -- cbn [length] in *. lia.
      -- intros HF. inversion HF as [|? ? Hb1 HF1]; subst. inversion HF1 as [|? ? Hb2 HF2]; subst. apply I6. constructor; [|exact HF2].
         destruct Hb1 as [L1 N1], Hb2 as [L2 N2]. apply Nat.leb_le in E.
         split; cbn [b_items]; [rewrite length_app; lia | apply Forall_app; split; assumption].
    * revert H. destruct (merge_batches_cf f _) as [rest ex'] eqn:R. intros H. injection H as <- <-.
      destruct (IH _ _ _ R) as (I1 & I2 & I3 & I4 & I5 & I6).
      splits.
      -- change (flat_map b_items (b1 :: rest)) with (b_items b1 ++ flat_map b_items rest). rewrite I1. reflexivity.
      -- cbn [map app]. apply perm_skip. exact I2.
      -- exact I3.
      -- unfold sum_bytes in *. cbn [fold_right] in *. lia.
      -- cbn [length] in *. lia.
      -- intros HF. inversion HF as [|? ? Hb1 HF1]; subst. constructor; [exact Hb1 | exact (I6 HF1)].
Qed.

(* A merge needs a non-full batch followed by a non-full one. Inside the global list only the last batch of
   a segment is non-full, so a merge absorbs a one-batch segment into the end of the segment before it, whose
   bytes only grow: the group shape survives. *)
Lemma merge_batches_segs_cf : forall fuel F GS l' ex,
F <> [] -> Forall bfull (removelast F) -> Forall qgroup_ok GS -> Forall bok_cf (F ++ concat GS) ->
merge_batches_cf fuel (F ++ concat GS) = (l', ex) ->
exists F' GS', l' = F' ++ concat GS' /\ F' <> [] /\ Forall bfull (removelast F') /\ Forall qgroup_ok GS' /\ sum_bytes F <= sum_bytes F'.
Proof.
induction fuel as [|f IH]; intros F GS l' ex HF HFF HG HB H.
- cbn [merge_batches_cf] in H. injection H as <- <-. exists F, GS. splits; auto; lia.
- destruct F as [|b1 F1]; [contradiction|].
  destruct F1 as [|b2 F2].
  + destruct GS as [|g1 GS1].
    * cbn [app concat merge_batches_cf] in H. injection H as <- <-. exists [b1], [].
      splits; [cbn; reflexivity | discriminate | constructor | constructor | lia].
    * inversion HG as [|? ? Hg1 HG1]; subst. destruct Hg1 as (Gne & Gfull & Gbytes).
      destruct g1 as [|c1 g1']; [contradiction|].
      cbn [app concat] in H, HB. inversion HB as [|? ? Bb1 HB1]; subst. inversion HB1 as [|? ? Bc1 HB2]; subst.
      cbn [merge_batches_cf] in H. revert H. destruct (Nat.leb _ _) eqn:E; intros H.
      -- destruct g1' as [|c2 g1''].
         2:{ exfalso. cbn [removelast] in Gfull. inversion Gfull as [|? ? Hc1 _]; subst. unfold bfull in Hc1.
             apply Nat.leb_le in E. destruct Bb1 as [[Lb1 _] _]. lia. }
         revert H. destruct (merge_batches_cf f _) as [rest ex'] eqn:R. intros H. injection H as <- <-.
         assert (BM : bok_cf (mkBatch (b_self b1) (b_items b1 ++ b_items c1))).
         { destruct Bb1 as [L1 N1], Bc1 as [L2 N2]. apply Nat.leb_le in E.
           split; cbn [b_items]; [rewrite length_app; lia | apply Forall_app; split; assumption]. }
         destruct (IH [mkBatch (b_self b1) (b_items b1 ++ b_items c1)] GS1 rest ex' ltac:(discriminate) ltac:(constructor) HG1
           ltac:(constructor; [exact BM | exact HB2]) R) as (F' & GS' & -> & Fne & Ffull & HG' & Hsum).
         exists F', GS'. splits; [reflexivity | exact Fne | exact Ffull | exact HG' |].
         unfold sum_bytes in *. cbn [fold_right] in *. pose proof (b_bytes_merge_cf (b_self b1) b1 c1) as BB.
         pose proof (b_bytes_ge_cf c1 (proj2 Bc1)) as BG. lia.
      -- revert H. destruct (merge_batches_cf f _) as [rest ex'] eqn:R. intros H. injection H as <- <-.
         destruct (IH (c1 :: g1') GS1 rest ex' ltac:(discriminate) Gfull HG1 ltac:(constructor; [exact Bc1 | exact HB2]) R)
           as (F' & GS' & -> & Fne & Ffull & HG' & Hsum).
         exists [b1], (F' :: GS').
         splits; [reflexivity | discriminate | constructor | constructor; [split; [exact Fne | split; [exact Ffull | lia]] | exact HG'] | lia].
  + cbn [app] in H, HB. cbn [removelast] in HFF. inversion HFF as [|? ? Fb1 HFF1]; subst.
    inversion HB as [|? ? Bb1 HB1]; subst. inversion HB1 as [|? ? Bb2 HB2]; subst.
    cbn [merge_batches_cf] in H. revert H. destruct (Nat.leb _ _) eqn:E; intros H.
    { exfalso. apply Nat.leb_le in E. unfold bfull in Fb1. destruct Bb2 as [[Lb2 _] _]. lia. }
    revert H. destruct (merge_batches_cf f _) as [rest ex'] eqn:R. intros H. injection H as <- <-.
    destruct (IH (b2 :: F2) GS rest ex' ltac:(discriminate) HFF1 HG ltac:(constructor; [exact Bb2 | exact HB2]) R)
      as (F' & GS' & -> & Fne & Ffull & HG' & Hsum).
    exists (b1 :: F'), GS'. splits; [reflexivity | discriminate | | exact HG' |].
    * destruct F' as [|f0 F'']; [contradiction|]. cbn [removelast]. constructor; [exact Fb1 | exact Ffull].
    * unfold sum_bytes in *. cbn [fold_right] in *. lia.
Qed.

Lemma merge_batches_qsegs_cf : forall fuel l l' ex, qsegs_cf l -> Forall bok_cf l -> merge_batches_cf fuel l = (l', ex) -> qsegs_cf l'.
Proof.
intros fuel l l' ex (F & GS & -> & HF & HG) HB H.
destruct F as [|b F1].
- destruct GS as [|g1 GS1].
  + assert (E : merge_batches_cf fuel ([] ++ concat []) = ([], [])) by (destruct fuel; reflexivity).
    rewrite E in H. injection H as <- <-. exists [], []. splits; [reflexivity | constructor | constructor].
  + inversion HG as [|? ? Hg1 HG1]; subst. destruct Hg1 as (Gne & Gfull & Gbytes).
    destruct (merge_batches_segs_cf fuel g1 GS1 l' ex Gne Gfull HG1 HB H) as (F' & GS' & -> & Fne & Ffull & HG' & Hsum).
    exists [], (F' :: GS'). splits; [reflexivity | constructor | constructor; [split; [exact Fne | split; [exact Ffull | lia]] | exact HG']].
- destruct (merge_batches_segs_cf fuel (b :: F1) GS l' ex ltac:(discriminate) HF HG HB H) as (F' & GS' & -> & _ & Ffull & HG' & _).
  exists F', GS'. splits; [reflexivity | exact Ffull | exact HG'].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. maybe_drain_cf (YG00cf.v:302-318), with its merge choice and its tail named. *)
Definition merge_choice_cf (g : qcache) : qcache * list batch :=
let L := Z.of_nat (length (qc_list g)) in
if (kBatchBytes * L <? qc_bytes g) && (qc_bytes g <? 2 * (kBatchBytes * L))
then let '(l', ex) := merge_batches_cf (length (qc_list g)) (qc_list g) in
(mkQC l' (qc_bytes g - kBatchBytes * Z.of_nat (length ex)), ex)
else (g, []).
Definition drain_tail_cf (gm : qcache) (ex : list batch) : M unit :=
let '(g', popped) := pop_batches (S (length (qc_list gm))) gm [] in
modify (set_qglobal g') ;;
do_recycle (length (ex ++ popped)) (ex ++ popped).
Lemma maybe_drain_cf_eq : forall s, maybe_drain_cf s =
(s0 <- get ;;
if qc_bytes (st_qthread s0) <=? kQuarantineCacheMax then ret tt
else
let g := mkQC (qc_list (st_qglobal s0) ++ qc_list (st_qthread s0)) (qc_bytes (st_qglobal s0) + qc_bytes (st_qthread s0)) in
put (set_qglobal g (set_qthread qc0 s0)) ;;
if qc_bytes g <=? kQuarantineMax then ret tt
else let '(gm, ex) := merge_choice_cf g in drain_tail_cf gm ex) s.
Proof. reflexivity. Qed.

Definition mres_cf (g gm : qcache) (ex : list batch) : Prop :=
flat_map b_items (qc_list gm) = flat_map b_items (qc_list g) /\
Permutation (map b_self (qc_list g)) (map b_self (qc_list gm) ++ map b_self ex) /\
Forall (fun b => b_items b = []) ex /\
qc_bytes gm - sum_bytes (qc_list gm) = qc_bytes g - sum_bytes (qc_list g) /\
(length (qc_list gm) + length ex = length (qc_list g))%nat /\
(Forall bok_cf (qc_list g) -> Forall bok_cf (qc_list gm) /\ (qsegs_cf (qc_list g) -> qsegs_cf (qc_list gm))).

Lemma merge_choice_mres_cf : forall g gm ex, merge_choice_cf g = (gm, ex) -> mres_cf g gm ex.
Proof.
intros g gm ex H. unfold merge_choice_cf in H. cbv zeta in H. revert H.
destruct (_ && _) eqn:EB; intros H.
- revert H. destruct (merge_batches_cf _ _) as [l' ex'] eqn:R. intros H. injection H as <- <-.
  destruct (merge_batches_basic_cf _ _ _ _ R) as (I1 & I2 & I3 & I4 & I5 & I6).
  unfold mres_cf. cbn [qc_list qc_bytes]. splits; try assumption; try lia.
  intros HB. split; [exact (I6 HB) | intros HS; exact (merge_batches_qsegs_cf _ _ _ _ HS HB R)].
- injection H as <- <-. unfold mres_cf. cbn [map length].
  splits; [reflexivity | rewrite app_nil_r; apply Permutation_refl | constructor | lia | lia |].
  intros HB. split; [exact HB | intros HS; exact HS].
Qed.

Lemma class_elems_pop_incl_cf : forall s P rest bytes c y, qc_list (st_qglobal s) = P ++ rest ->
In y (class_elems (set_qglobal (mkQC rest bytes) s) c) -> In y (class_elems s c).
Proof.
intros s P rest bytes c y EP H. unfold class_elems in *.
change (reg (set_qglobal ?g s) c) with (reg s c) in H. change (cache (set_qglobal ?g s) c) with (cache s c) in H.
rewrite (chunk_offs_begs_cf s (set_qglobal _ s)) in H by reflexivity.
rewrite !in_app_iff in H |- *. destruct H as [H|[H|[H|H]]]; [tauto | tauto | tauto |]. right; right; right.
unfold batch_offs, all_batches in *. cbn [st_qthread st_qglobal set_qglobal qc_list] in H. rewrite EP.
destruct (c =? kBatchClass); [|destruct H].
rewrite !map_app, !in_app_iff in *. tauto.
Qed.

Lemma class_elems_global_cf : forall s b, In b (qc_list (st_qglobal s)) ->
In (b_self b - region_off kBatchClass) (class_elems s kBatchClass).
Proof.
intros s b H. unfold class_elems. rewrite !in_app_iff. right; right; right. rewrite batch_offs_24_cf.
apply (in_map (fun b => b_self b - region_off kBatchClass)).
unfold all_batches. apply in_app_iff. right. exact H.
Qed.

(* After the merge, the extracted batches float as RI_cf's do (YG03cf.v), and every invariant field holds. *)
Lemma RI_merge_cf : forall U pp cc bb s gm ex,
WfR_cf U pp cc bb s -> mres_cf (st_qglobal s) gm ex ->
RI_cf U pp cc bb (set_qglobal gm s) ex.
Proof.
intros U pp cc bb s gm ex W (M1 & M2 & M3 & M4 & M5 & M6). wfr_fields_d3 W. quar_fields Xq.
assert (BOK : Forall bok_cf (qc_list (st_qglobal s))).
{ apply Forall_forall. intros b Hb. split.
  - exact (proj1 (Forall_forall _ _) Qbat b ltac:(unfold all_batches; apply in_app_iff; right; exact Hb)).
  - apply Forall_forall. intros k Hk.
    assert (HQ : In k (q_items s)) by (unfold q_items, all_batches; rewrite flat_map_app; apply in_app_iff; right; apply in_flat_map; exists b; split; assumption).
    pose proof (proj1 (proj1 (Forall_forall _ _) Qit k HQ)) as HC.
    pose proof (proj1 (Forall_forall _ _) Xck k HC) as [HR _].
    unfold ck_n, req_size. destruct (ck_req k =? 0); lia. }
destruct (M6 BOK) as [BOK' SEG'].
set (s' := set_qglobal gm s).
assert (AB' : all_batches s' = qc_list (st_qthread s) ++ qc_list gm) by reflexivity.
assert (QI : q_items s' = q_items s).
{ unfold q_items. rewrite AB'. unfold all_batches. rewrite !flat_map_app, M1. reflexivity. }
assert (PS : Permutation (map b_self (all_batches s)) (map b_self (all_batches s') ++ map b_self ex)).
{ rewrite AB'. unfold all_batches. rewrite !map_app, <- app_assoc. apply Permutation_app_head. exact M2. }
assert (LB : (length (all_batches s') + length ex = length (all_batches s))%nat).
{ rewrite AB'. unfold all_batches. rewrite !length_app. lia. }
pose proof (Xcl kBatchClass ltac:(unfold kBatchClass; lia)) as C24. unfold wf_class_cf in C24.
assert (PE : Permutation (fa_elems (class_size kBatchClass) (rg_free (reg s kBatchClass)) ++ pc_chunks (cache s kBatchClass) ++ chunk_offs s kBatchClass ++ batch_offs s kBatchClass)
(map (fun b => b_self b - region_off kBatchClass) ex ++ class_elems s' kBatchClass)).
{ unfold class_elems. subst s'. change (reg (set_qglobal ?g s) ?c) with (reg s c). change (cache (set_qglobal ?g s) ?c) with (cache s c).
  rewrite (chunk_offs_begs_cf s (set_qglobal _ s)) by reflexivity. rewrite !batch_offs_24_cf, !boffs_map_cf.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_head; apply Permutation_app_head; apply Permutation_map; exact PS|].
  rewrite map_app. apply perm_front_cf. }
split; [|split; [|split; [|split; [|split]]]].
- constructor; wfr_easy_d3.
  + intros c Hc. unfold wf_class_cf. subst s'. cbn [st_cache_inited set_qglobal].
    change (reg (set_qglobal ?g s) c) with (reg s c). change (cache (set_qglobal ?g s) c) with (cache s c).
    rewrite (chunk_offs_begs_cf s) by reflexivity. pose proof (Xcl c Hc) as C. unfold wf_class_cf in C.
    destruct (Z.eq_dec c kBatchClass) as [->|Hne].
    * eapply (cls_ok_repart_cf _ _ _ _ _ _ _ _ _ _ _ (map (fun b => b_self b - region_off kBatchClass) ex)); try reflexivity;
      [exact C | exact (wrc_runs _ _ _ _ _ _ C) | exact (wrc_fa_len _ _ _ _ _ _ C) | exact (wrc_cache _ _ _ _ _ _ C) |].
      unfold class_elems in PE. exact PE.
    * rewrite !batch_offs_other_cf in * by exact Hne. exact C.
  + constructor; subst s'; cbn [st_qthread st_qglobal st_chunks set_qglobal]; try assumption.
    * rewrite Qbg in M4. lia.
    * rewrite AB'. apply Forall_app. split.
      -- unfold all_batches in Qbat. apply Forall_app in Qbat as [Q1 _]. exact Q1.
      -- eapply Forall_impl; [|exact BOK']. intros b [Hb _]. exact Hb.
    * rewrite QI. exact Qit.
    * rewrite QI. exact Qnd.
    * exact (SEG' Qgr).
  + subst s'. cbn [st_nev set_qglobal]. lia.
  + subst s'. cbn [st_cache_inited set_qglobal]. intros NE. apply Xqi. intros E. apply NE.
    destruct (all_batches (set_qglobal gm s)) as [|b0 l0] eqn:EA; [reflexivity|]. exfalso.
    rewrite ?EA, E in LB. cbn [length] in LB. lia.
  + (* wfr_qsize: the merge keeps the items (mres_cf's first conjunct, QI) *)
    rewrite QI. exact Xqs.
- rewrite (flat_items_empty_cf ex M3). constructor.
- rewrite (flat_items_empty_cf ex M3). cbn [app]. rewrite QI. exact Qnd.
- eapply Forall_impl; [|exact M3]. cbv beta. intros b Hb. rewrite Hb. cbn [length]. lia.
- pose proof (Forall_Permutation _ _ _ PE (wrc_elems _ _ _ _ _ _ C24)) as FE. apply Forall_app in FE as [FE _].
  pose proof (Permutation_NoDup PE (wrc_nodup _ _ _ _ _ _ C24)) as ND. apply NoDup_app_iff in ND as (ND1 & _ & ND3).
  apply Forall_forall. intros b Hb.
  pose proof (proj1 (Forall_forall _ _) FE _ (in_map (fun b => b_self b - region_off kBatchClass) _ _ Hb)) as [E1 E2].
  change (reg s' kBatchClass) with (reg s kBatchClass). split; [exact E1 | split; [exact E2|]].
  intros Hin. exact (ND3 _ (in_map (fun b => b_self b - region_off kBatchClass) _ _ Hb) Hin).
- pose proof (Permutation_NoDup PE (wrc_nodup _ _ _ _ _ _ C24)) as ND. apply NoDup_app_iff in ND as (ND1 & _).
  rewrite boffs_map_cf in ND1. apply NoDup_map_inv in ND1. exact ND1.
Qed.

(* The extracted batches and the popped ones go to do_recycle together. *)
Lemma RIx_merge_pop_cf : forall U pp cc bb s ex P rest bytes',
RI_cf U pp cc bb s ex -> Forall (fun b => b_items b = []) ex -> qc_list (st_qglobal s) = P ++ rest ->
RI_cf U pp cc bb (set_qglobal (mkQC rest bytes') s) P ->
RIx_cf U pp cc bb (set_qglobal (mkQC rest bytes') s) [] (ex ++ P) [].
Proof.
intros U pp cc bb s ex P rest bytes' (W1 & IT1 & ND1 & BL1 & SF1 & NS1) HE EP (W2 & IT2 & ND2 & BL2 & SF2 & NS2).
unfold RIx_cf. cbn [app]. rewrite flat_map_app, (flat_items_empty_cf ex HE). cbn [app]. splits.
- exact W2.
- exact IT2.
- exact ND2.
- apply Forall_app. split; [|exact BL2]. eapply Forall_impl; [|exact HE]. cbv beta. intros b Hb. rewrite Hb. cbn [length]. lia.
- rewrite map_app. apply Forall_app. split.
  + apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
    destruct (proj1 (Forall_forall _ _) SF1 b Hb) as (Z1 & Z2 & Z3).
    change (reg (set_qglobal (mkQC rest bytes') s) kBatchClass) with (reg s kBatchClass).
    split; [exact Z1 | split; [exact Z2|]]. intros Hin. exact (Z3 (class_elems_pop_incl_cf s P rest bytes' kBatchClass _ EP Hin)).
  + apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb). exact (proj1 (Forall_forall _ _) SF2 b Hb).
- rewrite map_app. apply NoDup_app_iff. split; [exact NS1|]. split; [exact NS2|].
  intros x Hx1 Hx2. apply in_map_iff in Hx1 as (b1 & <- & Hb1). apply in_map_iff in Hx2 as (b2 & E2 & Hb2).
  destruct (proj1 (Forall_forall _ _) SF1 b1 Hb1) as (_ & _ & Z3). apply Z3. rewrite <- E2.
  apply class_elems_global_cf. rewrite EP. apply in_app_iff. left. exact Hb2.
Qed.

Lemma unq_merge_cf : forall s gm, flat_map b_items (qc_list gm) = flat_map b_items (qc_list (st_qglobal s)) ->
unq_cf (set_qglobal gm s) = unq_cf s.
Proof. intros s gm E. unfold unq_cf, quar_n. rewrite !queued_n_eq_cf. cbn [st_chunks st_qthread st_qglobal set_qglobal]. rewrite E. reflexivity. Qed.

Lemma xfr_merge_cf : forall s gm ex, mres_cf (st_qglobal s) gm ex ->
xfr_cf s (set_qglobal gm s) (fun c' => if c' =? kBatchClass then - Z.of_nat (length ex) else 0).
Proof.
intros s gm ex (M1 & M2 & M3 & M4 & M5 & M6). unfold xfr_cf.
splits; try (intros c' Hc'); [reflexivity | apply Z.le_refl | | apply Z.le_refl | apply Z.le_refl | reflexivity |].
- unfold class_elems. match goal with |- context [reg ?S c'] => change (reg S c') with (reg s c'); change (cache S c') with (cache s c'); change (chunk_offs S c') with (chunk_offs s c') end.
  unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qglobal].
  destruct (c' =? kBatchClass); [|lia]. rewrite !length_app, !length_map, !length_app, !Nat2Z.inj_add. lia.
- unfold all_batches. cbn [st_qthread st_qglobal set_qglobal]. rewrite !length_app. lia.
Qed.

(* The drain, cgif's maybe_drain_okx (YG03.v:1242-1298) with the merge and the structural fuels. No premise
   beyond the invariant: the fuels are the lists' own lengths. *)
Lemma maybe_drain_cf_okx : forall U pp cc bb s ns,
WfR_cf U pp cc bb s ->
atok ns (maybe_drain_cf s) (fun ns' res => (WfR_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\
unq_cf (snd res) = unq_cf s) /\ xfr_cf s (snd res) (fun _ => 0)).
Proof.
intros U pp cc bb s ns W.
rewrite maybe_drain_cf_eq. apply atok_bind. apply atok_get. cbn [fst snd].
destruct (qc_bytes (st_qthread s) <=? kQuarantineCacheMax) eqn:E1.
{ apply atok_ret. apply Z.leb_le in E1. cbn [snd]. split; [|apply xfr_refl_cf]. splits; [exact W | apply fframe_refl_cf | exact E1 | lia | reflexivity]. }
apply atok_bind. apply atok_put. cbn [fst snd].
pose proof (WfR_transfer_cf U pp cc bb s W ltac:(apply Z.leb_gt; exact E1)) as WT. cbv zeta in WT. set (sT := set_qglobal _ _) in *.
assert (FFT : fframe_cf s sT).
{ subst sT. unfold fframe_cf. cbn [st_nev st_fs st_depot set_qglobal set_qthread]. splits; try reflexivity. intros r0 sm0 E0; exists sm0; auto. }
pose proof (unq_transfer_cf s) as UQT. fold sT in UQT.
pose proof (xfr_transfer_cf s) as XFT. fold sT in XFT.
match goal with |- atok _ ((if ?b then _ else _) _) _ => destruct b eqn:E2 end.
{ apply atok_ret. apply Z.leb_le in E2. cbn [snd]. split; [|exact XFT].
  splits; [exact WT | exact FFT | subst sT; cbn; kc; lia | subst sT; cbn [st_qglobal set_qglobal set_qthread] in E2 |- *; lia | exact UQT]. }
assert (EG0 : st_qglobal sT = mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s))) by reflexivity.
rewrite <- EG0.
destruct (merge_choice_cf (st_qglobal sT)) as [gm ex] eqn:EMR.
pose proof (merge_choice_mres_cf _ _ _ EMR) as MR.
unfold drain_tail_cf. cbv beta iota zeta.
destruct (pop_batches (S (length (qc_list gm))) gm []) as [g' popped] eqn:EP. pose proof EP as EP0.
apply pop_batches_spec_cf in EP as (P & -> & EL & EB). cbn [rev app] in *.
destruct g' as [gl gb]. cbn [qc_list qc_bytes] in EL, EB. subst gb.
apply atok_bind. apply atok_modify. cbn [fst snd].
pose proof MR as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (RI_merge_cf U pp cc bb sT gm ex WT MR) as RIM.
pose proof (RI_pop_cf U pp cc bb (set_qglobal gm sT) P gl (proj1 RIM) EL) as RIP.
pose proof (RIx_merge_pop_cf U pp cc bb (set_qglobal gm sT) ex P gl _ RIM M3 EL RIP) as RX.
change (set_qglobal (mkQC gl (qc_bytes (st_qglobal (set_qglobal gm sT)) - sum_bytes P)) (set_qglobal gm sT))
  with (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) sT) in RX.
eapply atok_mono; [|apply (do_recycle_okx_cf U pp cc bb (ex ++ P) (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) sT) _ (length (ex ++ P)) RX (le_n _))].
intros b [u s'] ((W' & FF' & TQ' & TG' & UQ') & XF'). cbn [snd] in TQ', TG', UQ', XF' |- *.
assert (FFP : fframe_cf sT (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) sT)).
{ unfold fframe_cf. cbn [st_nev st_fs st_depot set_qglobal]. splits; try reflexivity. intros r0 sm0 E0; exists sm0; auto. }
pose proof (unq_merge_cf sT gm M1) as UQM.
pose proof (unq_pop_cf (set_qglobal gm sT) P gl (qc_bytes gm - sum_bytes P) EL) as UQP.
change (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) (set_qglobal gm sT)) with (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) sT) in UQP.
pose proof (xfr_merge_cf sT gm ex MR) as XFM.
pose proof (xfr_pop_cf (set_qglobal gm sT) P gl (qc_bytes gm - sum_bytes P) EL) as XFP.
change (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) (set_qglobal gm sT)) with (set_qglobal (mkQC gl (qc_bytes gm - sum_bytes P)) sT) in XFP.
split.
- split; [exact W'|]. split; [eapply fframe_trans_cf; [exact FFT | eapply fframe_trans_cf; [exact FFP | exact FF']]|].
  split; [rewrite TQ'; subst sT; cbn; kc; lia|]. split.
  + rewrite TG'. cbn [st_qglobal set_qglobal qc_bytes].
    destruct (pop_batches_stop_cf _ _ _ _ _ EP0 (Nat.lt_succ_diag_r _)) as [Hmin|Hnil].
    * cbn [qc_bytes] in Hmin. kc. lia.
    * cbn [qc_list] in Hnil. subst gl. rewrite app_nil_r in EL.
      pose proof (wq_bytes_g _ (wfr_quarantine _ _ _ _ _ WT)) as QB.
      rewrite <- EL, M4, QB. kc. lia.
  + rewrite UQ', UQP, UQM, UQT, flat_map_app, (flat_items_empty_cf ex M3), items_n_app, items_n_nil_cf. lia.
- eapply xfr_trans_cf; [exact XFT | eapply xfr_trans_cf; [exact XFM | eapply xfr_trans_cf; [exact XFP | exact XF' | intros; reflexivity] | intros; reflexivity] |].
  intros c' _. cbn beta. rewrite length_app, Nat2Z.inj_add. destruct (c' =? kBatchClass); lia.
Qed.

(* drain_spec_cf (YG03cf.v) holds for maybe_drain_cf: Compl0 survives because the drain's cdef delta is 0. *)
Lemma maybe_drain_cf_ok : forall U, drain_spec_cf U maybe_drain_cf.
Proof.
intros U pp cc bb s ns W.
eapply atok_mono; [|exact (maybe_drain_cf_okx U pp cc bb s ns (WfR_of_WfP_cf _ _ _ _ _ W))].
intros b r ((W' & F' & T' & G' & Q') & XF). splits; try assumption.
apply WfP_of_WfR_cf; [exact W'|]. intros c Hc. rewrite (xfr_cdef_cf _ _ _ XF c Hc), (wfc_compl0 _ _ _ _ _ W c Hc). lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. free_cf's law. The universe premise is a Section Hypothesis, as cgif's      *)
(* model_laws_ok (YG05.v:139) takes it; batch_room_cf is YG00cf.v's.            *)
Section FREECF.
Variable U : Univ.
Hypothesis HU : universe_ok U.

Lemma free_cf_with_drain : forall p tr s, free_cf p tr s = free_with_cf maybe_drain_cf p tr s.
Proof. reflexivity. Qed.

Theorem ml_free_cf : forall s p n tr, Wf_cf U s -> batch_room_cf s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok_cf true (free_cf p tr s) (free_post_ycf U s p n).
Proof.
intros s p n tr W Hr Hp Htr. rewrite free_cf_with_drain.
exact (ml_free_with_cf U HU maybe_drain_cf (maybe_drain_cf_ok U) s p n tr W Hr Hp Htr).
Qed.
End FREECF.
End YG03DCF.
