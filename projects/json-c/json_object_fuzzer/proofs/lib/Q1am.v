(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QPiB Qatc QSfG QdBa QpFQ Ql2m QYTG QjcB QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QLaA.Mq0.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma In_map_to_list_regions st rid r : In (rid, r) (map_to_list (s_regions st)) <-> s_regions st !! rid = Some r.
Proof.
split.
- intros H. apply elem_of_map_to_list. apply list_elem_of_In. exact H.
- intros H. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact H.
Qed.

Section RANGES.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : inv_R X st L.

#[using="RC__ X IR"] Lemma lranges_iff x : In x (lranges L) <-> In x (live_ranges st).
Proof.
unfold lranges, live_ranges. rewrite (ir_resv _ _ _ IR). rewrite !in_app_iff. split.
- intros [H|[H|[H|H]]]; [left; exact H| right| right| right].
+ apply in_map_iff in H as ([b l] & <- & Hg). cbn.
pose proof (Permutation_in _ (ir_groups _ _ _ IR) Hg) as Hin. apply in_map_iff in Hin as ([rid r] & E & Hf). cbn in E. inversion E. subst.
apply filter_In in Hf as [Hf Hk]. cbn in Hk. apply in_map_iff. exists (rid, r). split; [| exact Hf].
cbn. unfold region_live_range. destruct (r_kind r); try discriminate; reflexivity.
+ apply in_map_iff in H as ([[b l] kk] & <- & Hm). cbn.
pose proof (Permutation_in _ (ir_metas _ _ _ IR) Hm) as Hin. apply in_map_iff in Hin as ([rid r] & E & Hf). cbn in E. inversion E. subst.
apply filter_In in Hf as [Hf Hk]. cbn in Hk. apply in_map_iff. exists (rid, r). split; [| exact Hf].
cbn. unfold region_live_range. destruct (r_kind r); try discriminate; reflexivity.
+ destruct (ld_brkreg L) as [[b l]|] eqn:EB; [| destruct H]. destruct H as [<-|[]].
destruct (proj1 (ir_brkreg _ _ _ IR b l) EB) as (rid & r & Hr & Hk & <- & <-).
apply in_map_iff. exists (rid, r). split; [| apply In_map_to_list_regions; exact Hr].
cbn. unfold region_live_range. rewrite Hk. reflexivity.
- intros [H|H]; [left; exact H| right].
apply in_map_iff in H as ([rid r] & <- & Hin). cbn. apply In_map_to_list_regions in Hin.
unfold region_live_range. destruct (r_kind r) eqn:Hk.
+ right. right. rewrite (proj2 (ir_brkreg _ _ _ IR (r_base r) (r_len r))); [left; reflexivity| exists rid, r; auto].
+ right. left.
assert (Hf : In (rid, r) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st)))).
{ apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk; reflexivity]. }
pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1)) _ _ Hf) as Hm.
pose proof (Permutation_in _ (Permutation_sym (ir_metas _ _ _ IR)) Hm) as Hm'.
apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
+ left.
assert (Hf : In (rid, r) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st)))).
{ apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk; reflexivity]. }
pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ Hf) as Hm.
pose proof (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR)) Hm) as Hm'.
apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
Qed.

#[using="Type"] Lemma forallb_ext {A} (f : A -> bool) l1 l2 : (forall x, In x l1 <-> In x l2) -> forallb f l1 = forallb f l2.
Proof.
intros H. destruct (forallb f l1) eqn:E1; destruct (forallb f l2) eqn:E2; try reflexivity.
- rewrite forallb_forall in E1. assert (E2' : forallb f l2 = true) by (apply forallb_forall; intros x Hx; apply E1; apply H; exact Hx). congruence.
- rewrite forallb_forall in E2. assert (E1' : forallb f l1 = true) by (apply forallb_forall; intros x Hx; apply E2; apply H; exact Hx). congruence.
Qed.

#[using="RC__ X IR"] Lemma ranges_free_eq a n : ranges_free (lranges L) a n = ranges_free (live_ranges st) a n.
Proof. unfold ranges_free. apply forallb_ext. apply lranges_iff. Qed.

#[using="X IR"] Lemma mmap_answer_ok_eq len r : mmap_answer_ok (lranges L) len r = mmap_answer_ok (live_ranges st) len r.
Proof. unfold mmap_answer_ok. rewrite ranges_free_eq. reflexivity. Qed.

#[using="X IR"] Lemma brk_pages_ok_eq lo len : lbrk_pages_ok L lo len = brk_pages_ok st lo len.
Proof. unfold lbrk_pages_ok, brk_pages_ok. rewrite ranges_free_eq. reflexivity. Qed.

#[using="Type"] Lemma ranges_free_regions a n rid r : ranges_free (live_ranges st) a n = true -> s_regions st !! rid = Some r ->
let '(b, l) := region_live_range r in a + n <= b \/ b + l <= a.
Proof.
intros H Hr. unfold ranges_free in H. rewrite forallb_forall in H.
specialize (H (region_live_range r)). destruct (region_live_range r) as [b l] eqn:E.
assert (Hin : In (b, l) (live_ranges st)).
{ unfold live_ranges. apply in_app_iff. right. apply in_map_iff. exists (rid, r). rewrite <- E. split; [reflexivity| apply In_map_to_list_regions; exact Hr]. }
specialize (H Hin). cbn in H. unfold iv_disjoint in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; [apply Z.leb_le in H| apply Z.leb_le in H]; lia.
Qed.
End RANGES.

#[using="Type"] Lemma mmap_ok_facts live len r :
mmap_answer_ok live len r = true -> is_err r = false ->
0 < r /\ r mod PGSZ = 0 /\ r + round_up_pg len <= alloc_ceiling /\ ranges_free live r (round_up_pg len) = true.
Proof.
unfold mmap_answer_ok, is_errno_form, is_err. intros H E.
apply Bool.orb_true_iff in H. destruct H as [H|H].
- apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_ge in E. unfold TWO64 in *. lia.
- apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

#[using="Type"] Lemma regions_insert_perm (st : mstate) rid r (F : N * region -> bool) :
s_regions st !! rid = None ->
Permutation (List.filter F (map_to_list (<[rid := r]> (s_regions st)))) (List.filter F ((rid, r) :: map_to_list (s_regions st))).
Proof. intros H. apply perm_filter. apply map_to_list_insert. exact H. Qed.

Section NEW_GROUP_REGION.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r len : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = None.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Hypothesis HLEN : 0 < len < LEN_MAX.
Let rid := s_next_rid st.
Let st' := fst (new_region RKGroup r len st).
Let L' := Qfya.set_groups ((r, len) :: ld_groups L) L.
Let X' := xorph X (Some rid).

#[using="RC__ X L BL LS INV"] Lemma ng_fresh : s_regions st !! rid = None.
Proof.
destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
#[using="Type"] Lemma ng_lookup q : s_regions st' !! q = if (q =? rid)%N then Some (mkRegion RKGroup r len) else s_regions st !! q.
Proof. unfold st'. apply lookup_new_region. Qed.
#[using="RC__ X L BL LS INV rid"] Lemma ng_keep q rq : s_regions st !! q = Some rq -> s_regions st' !! q = Some rq.
Proof. intros H. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite ng_fresh in H; discriminate| exact H]. Qed.
#[using="Type"] Lemma ng_some q rq : s_regions st' !! q = Some rq -> (q = rid /\ rq = mkRegion RKGroup r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
#[using="Type"] Lemma ng_frontier q rq : frontier st' q rq = frontier st q rq. Proof. reflexivity. Qed.

#[using="INV HO HOK NERR HLEN"] Theorem INVL_new_group_region : INVL X' st' L' BL LS.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (mmap_ok_facts _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
pose proof (round_up_ge len) as RU.
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; cbn -[new_region st' frontier region_live_range round_up_pg Z.mul Z.pow Z.add filter].
+ intros q rq Hq. unfold st'. rewrite s_next_rid_new_region. apply ng_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
+ intros q rq Hq. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros [K|K]; discriminate.
+ intros q1 q2 r1 r2 H1 H2 NE.
apply ng_some in H1 as [[-> ->]|[N1 H1]]; apply ng_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D.
destruct (region_live_range r2) as [b2 l2]. lia.
* pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D.
destruct (region_live_range r1) as [b1 l1]. cbn. lia.
+ exact ir_resv.
+ unfold L'. cbn. eapply Permutation_trans; [apply perm_skip; exact ir_groups|].
fold rid.
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ ng_fresh)].
cbn. apply Permutation_refl.
+ unfold L'. cbn. eapply Permutation_trans; [exact ir_metas|].
fold rid.
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ ng_fresh)].
cbn. erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn. rewrite ng_frontier. reflexivity.
+ intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite ng_frontier. exact (ir_metalen q rq Hq K).
+ intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite ng_frontier. exact (ir_brkfront q rq Hq K).
+ destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
right. exists q, rq. split; [apply ng_keep; exact Hq| auto].
+ intros b l. unfold L'. cbn. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
* split; [apply ng_keep; exact Hq| auto].
* apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
+ intros q1 q2 r1 r2 H1 H2 K1 K2. apply ng_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply ng_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
+ unfold L'. cbn. revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
* destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
* exact IBK.
* destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply ng_keep; exact Hq| auto].
+ destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply ng_keep; exact Hq| auto].
+ intros q Hq. unfold X' in Hq. cbn in Hq. inversion Hq. subst q. exists (mkRegion RKGroup r len).
split; [rewrite ng_lookup, N.eqb_refl; reflexivity|]. split; [reflexivity|].
intros b Hb. change (s_groups st') with (s_groups st). destruct (s_groups st !! b) as [h|] eqn:E; [| reflexivity]. exfalso.
destruct (ig_region _ _ _ IG _ _ E) as (rq & Hrq & _). rewrite Hb in Hrq. fold rid in Hrq. rewrite ng_fresh in Hrq. discriminate.
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite ng_frontier. split; [apply ng_keep; exact Hq| auto].
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
- apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
* intros q rq Hq K E. apply ng_keep. exact Hq.
* apply (group_ok_X X); [reflexivity|]. exact (G1 m b ai Hb).
+ exact G2.
+ exact G3.
+ intros q rq Hq K Ho. apply ng_some in Hq as [[-> ->]|[NE Hq]].
* exfalso. apply Ho. reflexivity.
* apply (G4 q rq Hq K). rewrite HO. discriminate.
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply ng_keep; exact Hq| exact K].
- apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
Qed.
End NEW_GROUP_REGION.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QSfG.Mq0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB QdBa.Mq2 Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QaiD QLaA.Mq0.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition TF (st : mstate) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> 12 <= o mod 16.

Definition TKS (st : mstate) (T : N) : Prop :=
forall rid sh, s_shadow st !! rid = Some sh ->
(forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Definition DOMS (st0 st : mstate) : Prop :=
forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup.

#[using="Type"] Lemma TKS_of X st L BL LS : INVL X st L BL LS -> TKS st (s_tick st).
Proof. intros INV. exact (ish_ticks _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.
#[using="Type"] Lemma DOMS_of X st L BL LS : INVL X st L BL LS -> DOMS st st.
Proof. intros INV. exact (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

#[using="Type"] Lemma TF_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF (set_tick t st).
Proof.
intros TK LT rid sh o v t' Hsh Ho E. cbn in E, Hsh. subst t'. destruct (TK rid sh Hsh) as (C & _ & _). destruct (C o v t Ho) as [_ LE]. exfalso. lia.
Qed.

#[using="Type"] Lemma get_shadow_cells_some st rid o c : r_cells (get_shadow st rid) !! o = Some c -> exists sh, s_shadow st !! rid = Some sh /\ r_cells sh !! o = Some c.
Proof.
unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn; [intros H; exists sh; auto|]. rewrite lookup_empty. discriminate.
Qed.

#[using="Type"] Lemma TF_wr8 st q v : TF st -> 12 <= snd q mod 16 -> TF (wr8 q v st).
Proof.
intros H Hq rid sh o w t. rewrite (wr8_shadow_lookup st q v rid). destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
intros E. inversion E. subst sh. cbn. destruct (Z.eq_dec o (snd q)) as [->|NEo].
- rewrite lookup_insert_eq. intros _ _. exact Hq.
- rewrite lookup_insert_ne by congruence. intros Ho Et. destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
Qed.

#[using="Type"] Lemma TF_hdr_havoc st b : TF st -> TF (hdr_havoc b st).
Proof.
intros H rid sh o w t. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE].
- rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn. intros Ho Et.
destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
- rewrite lookup_insert_ne by congruence. apply H.
Qed.

#[using="Type"] Lemma TF_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF st -> TF st'.
Proof. intros E1 E2 H rid sh o v t. rewrite E1, E2. apply H. Qed.

#[using="Type"] Lemma TKS_hdr_havoc st b : TKS st (s_tick st) -> TKS (hdr_havoc b st) (s_tick st).
Proof.
intros TK rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn.
assert (G : forall P : shadow -> Prop, (forall sh, s_shadow st !! fst b = Some sh -> P sh) -> P shadow0 -> P (get_shadow st (fst b))).
{ intros P H1 H0. unfold get_shadow. destruct (s_shadow st !! fst b) eqn:Es; [apply H1; reflexivity| exact H0]. }
split; [| split].
- apply (G (fun sh => forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (TK _ _ Hsh))| intros o w t Ho; cbn in Ho; rewrite lookup_empty in Ho; discriminate].
- intros u hl ch. destruct (Z.eq_dec u (snd b / 16)) as [->|NEu].
+ rewrite lookup_insert_eq. intros E2. inversion E2. subst hl. unfold hav_add. cbn. intros [<-|Hin]; [cbn; lia|].
apply (proj2 (list_elem_of_In _ _)) in Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin.
revert Hin. apply (G (fun sh => In ch (default [] (r_hav sh !! (snd b / 16))) -> (snd ch <= s_tick st)%N)).
* intros sh Hsh Hin. destruct (r_hav sh !! (snd b / 16)) as [hl0|] eqn:Eh; cbn in Hin; [| destruct Hin]. exact (proj1 (proj2 (TK _ _ Hsh)) _ hl0 ch Eh Hin).
* cbn. rewrite lookup_empty. cbn. tauto.
+ rewrite lookup_insert_ne by congruence.
apply (G (fun sh => r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (proj2 (TK _ _ Hsh)) u hl ch)|].
cbn. rewrite lookup_empty. discriminate.
- apply (G (fun sh => forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N)); [intros sh Hsh; exact (proj2 (proj2 (TK _ _ Hsh)))|].
intros pg t Hp. cbn in Hp. rewrite lookup_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma DOMS_wr8 st0 st q v : DOMS st0 st -> (exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wr8 q v st).
Proof. intros D Hq. unfold DOMS. apply (wr8_dom st q v (fun rid => exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup) D Hq). Qed.
#[using="Type"] Lemma DOMS_hdr_havoc st0 st b : DOMS st0 st -> (exists r, s_regions st0 !! fst b = Some r /\ r_kind r = RKGroup) -> DOMS st0 (hdr_havoc b st).
Proof.
intros D Hb rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [intros _; exact Hb|].
rewrite lookup_insert_ne by congruence. apply D.
Qed.
#[using="Type"] Lemma TKS_wr8 st q v T : (s_tick st <= T)%N -> TKS st T -> TKS (wr8 q v st) T.
Proof. intros LE TK. exact (wr8_tks st q v T LE TK). Qed.

#[using="Type"] Lemma sh_ticks_of st rid : TKS st (s_tick st) -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
intros TK. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
- destruct (TK _ _ E) as (_ & A & B). split; [exact A| exact B].
- split; [intros u hl ch H; rewrite lookup_empty in H; discriminate| intros pg t H; rewrite lookup_empty in H; discriminate].
Qed.

Fixpoint wrs (l : list (aptr * Z)) (st : mstate) : mstate :=
match l with [] => st | (q, v) :: l' => wrs l' (wr8 q v st) end.

#[using="Type"] Lemma wrs_app l1 l2 st : wrs (l1 ++ l2) st = wrs l2 (wrs l1 st).
Proof. revert st. induction l1 as [|[q v] l1 IH]; intros st; cbn; [reflexivity| apply IH]. Qed.

Section WRS.

#[using="Type"] Lemma wrs_ctrl l st : ctrl_eq st (wrs l st) /\ s_tick (wrs l st) = s_tick st.
Proof.
revert st. induction l as [|[q v] l IH]; intros st; cbn; [split; [apply ctrl_eq_refl| reflexivity]|].
destruct (IH (wr8 q v st)) as [C T]. split; [eapply ctrl_eq_trans; [apply ctrl_eq_wr8| exact C]| rewrite T; reflexivity].
Qed.

#[using="Type"] Lemma wrs_read_other l st q : ~ In q (map fst l) ->
cell_read (get_shadow (wrs l st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
revert st. induction l as [|[q' v] l IH]; intros st Hn; cbn; [reflexivity|].
rewrite IH by (cbn in Hn; tauto). apply cell_read_wr8_other. cbn in Hn. intros ->. apply Hn. left. reflexivity.
Qed.

#[using="Type"] Lemma wrs_TKS l st T : (s_tick st <= T)%N -> TKS st T -> TKS (wrs l st) T.
Proof.
revert st. induction l as [|[q v] l IH]; intros st LE TK; cbn; [exact TK|].
apply IH; [cbn; exact LE|]. apply TKS_wr8; assumption.
Qed.

#[using="Type"] Lemma wrs_DOMS l st0 st : DOMS st0 st -> (forall q, In q (map fst l) -> exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wrs l st).
Proof.
revert st. induction l as [|[q v] l IH]; intros st D H; cbn; [exact D|].
apply IH; [apply DOMS_wr8; [exact D| apply H; left; reflexivity]| intros q' Hq'; apply H; right; exact Hq'].
Qed.

#[using="Type"] Lemma wrs_TF l st : TF st -> (forall q, In q (map fst l) -> 12 <= snd q mod 16) -> TF (wrs l st).
Proof.
revert st. induction l as [|[q v] l IH]; intros st H Hl; cbn; [exact H|].
apply IH; [apply TF_wr8; [exact H| apply Hl; left; reflexivity]| intros q' Hq'; apply Hl; right; exact Hq'].
Qed.

#[using="Type"] Lemma wrs_read_last l1 q v l2 st :
~ In q (map fst l2) -> TKS st (s_tick st) ->
cell_read (get_shadow (wrs (l1 ++ (q, v) :: l2) st) (fst q)) (snd q) = Known (Z.land v 255).
Proof.
intros Hn TK. rewrite wrs_app. cbn. rewrite wrs_read_other by exact Hn.
destruct (wrs_ctrl l1 st) as [C T].
apply cell_read_wr8_same. apply sh_ticks_of. rewrite T. apply wrs_TKS; [lia| exact TK].
Qed.
End WRS.

Fixpoint zlist (p : aptr) (size : Z) (i : Z) (n : nat) : list (aptr * Z) :=
match n with O => [] | S n' => (aadd p (UNIT + i * size - 4), 0) :: zlist p size (i + 1) n' end.

#[using="Type"] Lemma zero_hdrs_wrs p size i n st : zero_hdrs p size i n st = wrs (zlist p size i n) st.
Proof. revert i st. induction n as [|n IH]; intros; cbn; [reflexivity| apply IH]. Qed.

#[using="Type"] Lemma in_zlist p size q : forall n i, In q (map fst (zlist p size i n)) <-> exists k, i <= k < i + Z.of_nat n /\ q = aadd p (UNIT + k * size - 4).
Proof.
induction n as [|n IH]; intros i; cbn.
- split; [tauto| intros (k & Hk & _); lia].
- rewrite IH. split.
+ intros [<-|(k & Hk & ->)]; [exists i; split; [lia| reflexivity]| exists k; split; [lia| reflexivity]].
+ intros (k & Hk & ->). destruct (Z.eq_dec k i) as [->|NE]; [left; reflexivity| right; exists k; split; [lia| reflexivity]].
Qed.

#[using="Type"] Lemma zlist_split p size i n k : i <= k < i + Z.of_nat n ->
exists l1 l2, zlist p size i n = l1 ++ (aadd p (UNIT + k * size - 4), 0) :: l2
/\ (forall q, In q (map fst l2) -> exists k', k < k' < i + Z.of_nat n /\ q = aadd p (UNIT + k' * size - 4)).
Proof.
revert i. induction n as [|n IH]; intros i Hk; [cbn in Hk; lia|].
cbn. destruct (Z.eq_dec k i) as [->|NE].
- exists [], (zlist p size (i + 1) n). split; [reflexivity|]. intros q Hq. apply in_zlist in Hq as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
- destruct (IH (i + 1) ltac:(lia)) as (l1 & l2 & E & H). exists ((aadd p (UNIT + i * size - 4), 0) :: l1), l2.
rewrite E. split; [reflexivity|]. intros q Hq. destruct (H q Hq) as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
Qed.

Section NL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (aig idx j size cnt : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let p : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some p.
Hypothesis STR : get_stride (MR st g) = UNIT * size_class j.
Hypothesis SZ16 : size mod 16 = 0.
Hypothesis SZ0 : 16 <= size.
Hypothesis CNT : 1 <= cnt.
Hypothesis FIT : UNIT + cnt * size <= get_stride (MR st g).
Hypothesis HTF : TF st.
Let q : Z := (snd p - (snd bg + UNIT)) / UNIT.
Let st' := nest_layout st g idx j size cnt.

Definition nl_list : list (aptr * Z) :=
[(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5);
(aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ zlist p size 0 (Z.to_nat (cnt + 1)).

#[using="aig Hg"] Lemma g_hosts : hosts st bg g. Proof. exists aig. exact Hg. Qed.
#[using="RC__ X L BL LS aig INV Hg"] Lemma p_eq : slot_start' (MR st g) idx = p. Proof. unfold p. apply (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ g_hosts). Qed.
#[using="RC__ X L BL LS aig INV Hg"] Lemma bg_gbase : gbase (MR st g) = bg. Proof. apply (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ g_hosts). Qed.

#[using="RC__ X L BL LS aig INV Hg STR"] Lemma nl_eq : st' = wrs nl_list st.
Proof.
unfold st', nest_layout, enframe_at. fold (MR st g). cbn [negb Z.eqb].
change (aadd (default (0%N, 0) (m_mem (MR st g))) (UNIT + get_stride (MR st g) * idx)) with (slot_start' (MR st g) idx).
rewrite p_eq. unfold set_size.
replace (snd (aadd p (get_stride (MR st g) - IB)) - snd p - (UNIT * size_class j - IB)) with 0
by (unfold aadd; cbn [fst snd]; rewrite STR; unfold UNIT, IB; lia).
change (5 <=? 0) with false. change (0 =? 0) with true. cbn [negb].
unfold nl_list. rewrite wrs_app. cbn [wrs app]. rewrite zero_hdrs_wrs. unfold wr16.
unfold q. fold (gbase (MR st g)). rewrite bg_gbase. reflexivity.
Qed.

#[using="RC__ X L BL LS aig size INV Hg Hidx SZ0 q"] Lemma p_mod16 : snd p mod 16 = 0.
Proof.
unfold p. cbn. unfold sstart. rewrite bg_gbase.
pose proof (g_align _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as [_ A].
pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [_ SM].
pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2.
unfold UNIT in *. rewrite A in D1. rewrite SM in D2.
replace (snd bg + 16 + get_stride (MR st g) * idx) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * idx) * 16) by nia.
apply Z_mod_mult.
Qed.

#[using="st g bg idx size p q"] Lemma res16 a d : a mod 16 = 0 -> (a + d) mod 16 = d mod 16.
Proof. intros H. rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.

#[using="RC__ X L BL LS aig j INV Hg Hidx STR SZ16 SZ0 CNT FIT"] Lemma nl_residues r : In r (map fst nl_list) -> 12 <= snd r mod 16.
Proof.
pose proof p_mod16 as PM. clearbody p. unfold nl_list. rewrite map_app, in_app_iff. unfold aadd. cbn [map fst snd In]. intros [H|H].
- destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; rewrite <- ?Z.add_assoc, (res16 _ _ PM); cbn; lia.
- apply in_zlist in H as (k & Hk & ->). cbn [snd]. rewrite (res16 _ _ PM). unfold UNIT.
replace (16 + k * size - 4) with (k * size + 12) by lia. rewrite res16; [cbn; lia|].
rewrite Z.mul_mod, SZ16, Z.mul_0_r by lia. reflexivity.
Qed.

#[using="RC__ X L BL LS aig j INV Hg STR SZ16 SZ0 CNT FIT"] Lemma nl_in_T r : In r (map fst nl_list) ->
inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r \/ r = (fst bg, sstart (MR st g) (idx + 1) - 4).
Proof.
unfold nl_list. rewrite map_app, in_app_iff. rewrite sstart_succ. unfold inT, p, aadd. cbn [map fst snd In]. intros [H|H].
- left. pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [SG _].
destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold UNIT in *; lia.
- apply in_zlist in H as (k & Hk & ->). cbn [fst snd]. unfold UNIT in *. rewrite Z2Nat.id in Hk by lia.
destruct (Z.eq_dec (16 + k * size) (get_stride (MR st g))) as [E|NE].
+ right. unfold aadd. cbn [fst snd]. f_equal. lia.
+ left. unfold aadd. cbn [fst snd]. split; [reflexivity|]. assert (k * size <= cnt * size) by nia. lia.
Qed.
#[using="RC__ X L BL LS aig j INV Hg STR SZ16 SZ0 CNT FIT"] Lemma nl_regions r : In r (map fst nl_list) -> fst r = fst bg.
Proof. intros H. destruct (nl_in_T r H) as [[E _]| ->]; [exact E| reflexivity]. Qed.

#[using="aig INV Hg Hidx HP STR SZ16 SZ0 CNT FIT HTF"] Theorem nest_layout_ok :
INVL X st' L BL LS /\ TF st' /\ ctrl_eq st st' /\ s_tick st' = s_tick st
/\ known st' (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
/\ known st' (aadd p (-2)) (Z.land q 255) /\ known st' (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr q 8) 255)
/\ (forall k, 0 <= k <= cnt -> known st' (aadd p (UNIT + k * size - 4)) 0)
/\ (forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
cell_read (get_shadow st' (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
Proof.
rewrite nl_eq. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (wrs_ctrl nl_list st) as [CE TK].
pose proof (TKS_of _ _ _ _ _ INV) as TK0. pose proof (DOMS_of _ _ _ _ _ INV) as DM0.
assert (RD : forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
cell_read (get_shadow (wrs nl_list st) (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
{ intros r Hr. destruct (in_dec aptr_eq_dec r (map fst nl_list)) as [Hin|Hn]; [| apply wrs_read_other; exact Hn].
destruct (nl_in_T r Hin) as [HT| ->]; [exfalso; exact (Hr HT)|].

pose proof (ish_hdr0 _ _ ISH bg g (idx + 1) g_hosts ltac:(unfold cnt_of; lia)) as K0. unfold known, SHd, IB in K0. cbn [fst snd] in K0 |- *. rewrite K0.
assert (E : (fst bg, sstart (MR st g) (idx + 1) - 4) = aadd p (UNIT + cnt * size - 4) /\ UNIT + cnt * size = get_stride (MR st g)).
{ unfold nl_list in Hin. rewrite map_app in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
- exfalso. cbn [map fst In] in Hin. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold p, aadd in E; cbn [fst snd] in E; rewrite sstart_succ in E; unfold UNIT in *; lia.
- apply in_zlist in Hin as (k & Hk & Ek). rewrite Z2Nat.id in Hk by lia. apply (f_equal snd) in Ek. unfold p, aadd in Ek. cbn [fst snd] in Ek.
rewrite sstart_succ in Ek. destruct (Z.eq_dec k cnt) as [->|NEk].
+ split; [unfold p, aadd; cbn [fst snd]; rewrite sstart_succ; f_equal; unfold UNIT in *; lia| unfold UNIT in *; lia].
+ exfalso. assert (k * size <= (cnt - 1) * size) by nia. unfold UNIT in *. lia. }
destruct E as [E1 E2]. apply (f_equal snd) in E1. cbn [snd] in E1. rewrite E1.
destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) cnt ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & EZ & Hl2).
change (cell_read (get_shadow (wrs nl_list st) (fst (aadd p (UNIT + cnt * size - 4)))) (snd (aadd p (UNIT + cnt * size - 4))) = Known (Z.land 0 255)).
unfold nl_list. rewrite EZ.
rewrite (app_assoc _ l1) || rewrite app_assoc.
apply wrs_read_last; [| exact TK0].
intros Hin2. destruct (Hl2 _ Hin2) as (k' & Hk' & _). rewrite Z2Nat.id in Hk' by lia. lia. }
pose proof (is_part _ _ _ IS _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite p_eq, HP in P5. unfold one5 in P5.
assert (NH : s_groups st !! p = None).
{ destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
assert (NB : forall k, In k BL -> bslot k <> p).
{ intros k Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk. }
assert (REG : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hg).
split; [| split; [| split; [exact CE| split; [exact TK|]]]].
- split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
apply (inv_SH_write_T X st (wrs nl_list st) BL LS IM IG IS ISH g bg idx g_hosts Hidx NH NB CE TK RD).
+ apply wrs_DOMS; [exact DM0|]. intros r Hr. rewrite (nl_regions r Hr). exact REG.
+ apply wrs_TKS; [lia| exact TK0].
- apply wrs_TF; [exact HTF| apply nl_residues].
-
assert (KN : forall l1 r v l2, nl_list = l1 ++ (r, v) :: l2 -> ~ In r (map fst l2) -> known (wrs nl_list st) r (Z.land v 255)).
{ intros l1 r v l2 E Hn. unfold known, SHd. rewrite E. apply wrs_read_last; [exact Hn| exact TK0]. }
pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
assert (ZL : forall r, In r (map fst (zlist p size 0 (Z.to_nat (cnt + 1)))) -> snd p + 12 <= snd r).
{ intros r Hr. apply in_zlist in Hr as (k & Hk & ->). cbn. unfold UNIT. nia. }
split; [| split; [| split; [| split; [| exact RD]]]].
+ apply (KN [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5)] (aadd p (-3)) _ (zlist p size 0 (Z.to_nat (cnt + 1))) eq_refl).
intros Hin. pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
+ rewrite <- (Z.land_assoc q 255 255 : Z.land (Z.land q 255) 255 = Z.land q (Z.land 255 255)) || idtac.
replace (Z.land q 255) with (Z.land (Z.land q 255) 255) by (rewrite <- Z.land_assoc; reflexivity).
replace (Z.land (Z.land q 255) 255) with (Z.land q 255) by (rewrite <- Z.land_assoc; reflexivity).
apply (KN [] (aadd p (-2)) q _ eq_refl).
cbn [map fst app]. intros [E|[E|[E|[E|Hin]]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
+ apply (KN [(aadd p (-2), q)] (aadd (aadd p (-2)) 1) (Z.shiftr q 8) _ eq_refl).
cbn [map fst app]. intros [E|[E|[E|Hin]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
+ intros k Hk. destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) k ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & E & Hl2).
change (known (wrs nl_list st) (aadd p (UNIT + k * size - 4)) (Z.land 0 255)).
apply (KN ([(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5); (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ l1) _ 0 l2).
* unfold nl_list. rewrite E. rewrite <- app_assoc. reflexivity.
* intros Hin. destruct (Hl2 _ Hin) as (k' & Hk' & E'). unfold aadd in E'. apply (f_equal snd) in E'. cbn in E'. unfold UNIT in E'. nia.
Qed.
End NL.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; unfold zsum in *; cbn in *; lia. Qed.

#[using="Type"] Lemma round_up_ge_k x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

Definition gterm (st : mstate) (sc : Z) (bh : aptr * ghdr) : Z :=
match g_meta (snd bh) with
| Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0
| None => 0
end.
#[using="Type"] Lemma gcnt_unfold st sc : gcnt st sc = zsum (map (gterm st sc) (map_to_list (s_groups st))).
Proof. reflexivity. Qed.

#[using="Type"] Lemma gcnt_delete st st' p h sc :
s_groups st !! p = Some h -> s_groups st' = delete p (s_groups st) -> s_metas st' = s_metas st ->
gcnt st sc = gterm st sc (p, h) + gcnt st' sc.
Proof.
intros Hp HG HM. rewrite !gcnt_unfold, HG.
rewrite <- (zsum_perm _ _ (Permutation_map (gterm st sc) (map_to_list_delete (s_groups st) p h Hp))). cbn. f_equal.
f_equal. apply map_ext. intros [b hb]. unfold gterm. cbn. unfold MR, get_meta_rec. rewrite HM. reflexivity.
Qed.

Section KILL.
Variables (X : extras) (st st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g p : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! p = Some (mkGhdr (Some g) ai).
Hypothesis HF : x_fresh X = Some g.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis HO : x_orph X = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst p, sstart (MR st g) i).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Let sc := m_sizeclass (MR st g).
Let cnt := m_last_idx (MR st g) + 1.

Hypothesis S1 : exists U, st1 = upd_ctx (fun c => set_usage_map U c) st.
Hypothesis U1 : forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc'.
Hypothesis U2 : forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48.
Let st' := del_slots p (get_stride (MR st g)) cnt (del_group p st1).
Let nested := m_maplen (MR st g) =? 0.
Let X' := mkX (x_idle X) (g :: x_zomb X) (if nested then Some p else None) (if nested then None else Some (fst p)) None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="ai Hg"] Lemma g_hosts : hosts st p g. Proof. exists ai. exact Hg. Qed.
#[using="RC__ L BL INV Hg IG"] Lemma GO : group_ok X st LS g p ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
#[using="RC__ X L BL LS p ai INV Hg sc cnt IG"] Lemma stride_pos : 0 < get_stride (MR st g).
Proof. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [H _]. unfold UNIT in H. lia. Qed.
#[using="RC__ X L BL LS ai INV Hg IM"] Lemma gbase_p : gbase (MR st g) = p. Proof. exact (hosts_gbase _ _ _ IM _ _ g_hosts). Qed.
#[using="RC__ X L BL LS ai INV Hg IM"] Lemma slot_g j : slot_start' (MR st g) j = (fst p, snd p + UNIT + get_stride (MR st g) * j).
Proof. rewrite slot_start'_sstart. unfold sstart. rewrite gbase_p. reflexivity. Qed.
#[using="RC__ X L BL LS ai INV Hg IM"] Lemma sstart_g j : sstart (MR st g) j = snd p + UNIT + get_stride (MR st g) * j.
Proof. unfold sstart. rewrite gbase_p. reflexivity. Qed.

#[using="sc S1 U1 U2"] Lemma K_metas : s_metas st' = s_metas st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_MR x : MR st' x = MR st x. Proof. unfold MR, get_meta_rec. rewrite K_metas. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_regions : s_regions st' = s_regions st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_shadow : s_shadow st' = s_shadow st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_areas : s_areas st' = s_areas st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_tick : s_tick st' = s_tick st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_next_rid : s_next_rid st' = s_next_rid st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_secret : s_secret st' = s_secret st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_reserved : s_reserved st' = s_reserved st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_groups : s_groups st' = delete p (s_groups st). Proof. destruct S1 as [U ->]. reflexivity. Qed.
#[using="Type"] Lemma K_ctx : s_ctx st' = s_ctx st1. Proof. reflexivity. Qed.

#[using="sc S1 U1 U2"] Lemma K_c (P : mctx -> Prop) : (forall c U, P c -> P (set_usage_map U c)) -> P (s_ctx st) -> P (s_ctx st').
Proof. intros HPU H0. rewrite K_ctx. destruct S1 as [U ->]. cbn. apply HPU. exact H0. Qed.
#[using="S1"] Lemma K_cf :
c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st) /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st)
/\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st)
/\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)
/\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st)
/\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) /\ c_active (s_ctx st') = c_active (s_ctx st)
/\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st) /\ c_bounces (s_ctx st') = c_bounces (s_ctx st)
/\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st) /\ c_usage (s_ctx st') = c_usage (s_ctx st1).
Proof. destruct S1 as [U E]. rewrite K_ctx, E. cbn. repeat split; reflexivity. Qed.
#[using="Type"] Lemma K_usage sc' : usage st' sc' = usage st1 sc'.
Proof. reflexivity. Qed.

#[using="sc S1 U1 U2"] Lemma K_get_head h : get_head st' h = get_head st h.
Proof. destruct S1 as [U ->]. destruct h; reflexivity. Qed.
#[using="sc S1 U1 U2"] Lemma K_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite K_ctx. destruct S1 as [U ->]. reflexivity. Qed.

Definition gslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = slot_start' (MR st g) j.
#[using="RC__ X L BL LS ai i INV Hg Hi sc S1 U1 U2 IM IG"] Lemma K_slots s : s_slots st' !! s = s_slots st !! s /\ ~ gslot s \/ s_slots st' !! s = None /\ gslot s.
Proof.
pose proof stride_pos as SP. pose proof (g_li _ _ _ _ _ _ GO) as LI.
unfold st'. rewrite lookup_del_slots; [| unfold cnt; lia| exact SP].
replace (s_slots (del_group p st1)) with (s_slots st) by (destruct S1 as [U ->]; reflexivity).
set (d := snd s - snd p - UNIT).
destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod get_stride (MR st g) =? 0) && (d / get_stride (MR st g) <? cnt)) eqn:E.
- right. split; [reflexivity|]. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
exists (d / get_stride (MR st g)). split; [split; [apply Z.div_pos; lia| exact E4]|].
rewrite slot_g. pose proof (Z.div_mod d (get_stride (MR st g)) ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. unfold d in DM. lia.
- left. split; [reflexivity|]. intros (j & Hj & Es). rewrite slot_g in Es. subst s. cbn in d.
assert (Ed : d = get_stride (MR st g) * j) by (unfold d; lia).
rewrite N.eqb_refl in E. cbn in E.
assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
assert (E3 : (d mod get_stride (MR st g) =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult).
rewrite E3 in E. cbn in E.
assert (E4 : (d / get_stride (MR st g) <? cnt) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia).
rewrite E4 in E. discriminate.
Qed.
#[using="RC__ X L BL LS ai i INV Hg Hi sc S1 U1 U2 IM IG"] Lemma K_slots_other s : ~ gslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros NG. destruct (K_slots s) as [[E _]|[_ G]]; [exact E| tauto]. Qed.
#[using="RC__ X L BL LS ai i INV Hg Hi sc S1 U1 U2 IM IG"] Lemma K_slots_g s : gslot s -> s_slots st' !! s = None.
Proof. intros G. destruct (K_slots s) as [[_ NG]|[E _]]; [tauto| exact E]. Qed.
#[using="RC__ X L BL LS ai i INV Hg Hi sc S1 U1 U2 IM IG"] Lemma K_slots_some s v : s_slots st' !! s = Some v -> s_slots st !! s = Some v /\ ~ gslot s.
Proof. intros H. destruct (K_slots s) as [[E NG]|[E G]]; [rewrite <- E; auto| congruence]. Qed.

#[using="Type"] Lemma none_of {A} (o : option A) : (o <> None -> False) -> o = None.
Proof. destruct o; [intros H; exfalso; apply H; discriminate| reflexivity]. Qed.

#[using="RC__ L LS ai INV Hg HP ALL sc cnt IM IG IS"] Lemma g_slot_free j : 0 <= j <= m_last_idx (MR st g) ->
~ In (fst p, sstart (MR st g) j) (map bslot BL) /\ s_groups st !! (fst p, sstart (MR st g) j) = None
/\ (x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
Proof.
intros Hj. pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts) in P. unfold one5 in P.
destruct P as (_ & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
assert (PJ : x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
{ intros HPj. rewrite HP in HPj. inversion HPj.
destruct (Z.lt_total j i) as [LT|[E|LT]]; [| exact E|]; exfalso.
- pose proof (sstart_lt _ _ _ IG _ _ j i g_hosts LT). pose proof stride_pos. lia.
- pose proof (sstart_lt _ _ _ IG _ _ i j g_hosts LT). pose proof stride_pos. lia. }
destruct (Z.eq_dec j i) as [->|NE].
- rewrite HP in *. split; [intros C; apply nCE; auto|]. split; [| auto]. apply none_of. intros Hh. apply nDE. auto.
- destruct (ALL j Hj NE) as [A|B].
+ split; [intros C; exact (nAC (conj A C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nAD (conj A Hh)).
+ split; [intros C; exact (nBC (conj B C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nBD (conj B Hh)).
Qed.
#[using="RC__ X L LS p ai i INV Hg HP ALL sc cnt IM IG IS"] Lemma g_slot_free' j : 0 <= j <= m_last_idx (MR st g) ->
~ In (slot_start' (MR st g) j) (map bslot BL) /\ s_groups st !! (slot_start' (MR st g) j) = None.
Proof. intros Hj. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). destruct (g_slot_free j Hj) as (A & B & _). auto. Qed.

#[using="sc"] Lemma gslot_range s : gslot s -> exists j, 0 <= j <= m_last_idx (MR st g) /\ s = slot_start' (MR st g) j.
Proof. intros (j & Hj & E). exists j. unfold cnt in Hj. split; [lia| exact E]. Qed.

#[using="RC__ X L BL LS p ai INV Hg sc IS"] Lemma other_slot_not_g m b j : hosts st b m -> m <> g -> 0 <= j <= m_last_idx (MR st m) -> ~ gslot (slot_start' (MR st m) j).
Proof.
intros Hm NE Hj G. destruct (gslot_range _ G) as (j' & Hj' & E).
destruct (slot_key_inj _ _ _ IS _ _ _ _ _ _ Hm g_hosts Hj Hj' E) as [Em _]. exact (NE Em).
Qed.
#[using="RC__ X L BL LS p ai INV Hg sc IS"] Lemma entry_not_g s m j : s_slots st !! s = Some (m, j) -> m <> g -> ~ gslot s.
Proof.
intros Hs NE. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). exact (other_slot_not_g m b j Hb NE Hj).
Qed.

#[using="RC__ X L BL LS INV sc IS"] Lemma entry_g_gslot s j : s_slots st !! s = Some (g, j) -> gslot s.
Proof.
intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hj & ->). exists j. unfold cnt. split; [lia| reflexivity].
Qed.

#[using="sc S1 U1 U2"] Lemma hosts_K b m : hosts st' b m <-> hosts st b m /\ b <> p.
Proof.
unfold hosts. rewrite K_groups. split.
- intros [a H]. apply lookup_delete_Some in H as [NE H]. split; [exists a; exact H| congruence].
- intros [[a H] NE]. exists a. rewrite lookup_delete_ne by congruence. exact H.
Qed.
#[using="RC__ X L BL LS ai INV Hg sc S1 U1 U2 IM"] Lemma hosts_K_neq b m : hosts st' b m -> m <> g.
Proof. intros H. apply hosts_K in H as [H NE]. intros ->. exact (NE (hosts_inj _ _ _ IM _ _ _ H g_hosts)). Qed.
#[using="ai Hg sc S1 U1 U2"] Lemma live_K m : live_group st m -> m <> g -> live_group st' m.
Proof.
intros [b Hb] NE. exists b. apply hosts_K. split; [exact Hb|]. intros ->. exact (NE (hosts_fun _ _ _ _ Hb g_hosts)).
Qed.
#[using="RC__ X st L BL INV NL"] Lemma g_unlisted_K h : ~ In g (LS h).
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h). Qed.

#[using="RC__ X L BL LS ai INV Hg sc IM IG"] Lemma p_not_gslot : ~ gslot p.
Proof.
intros (j & Hj & E). rewrite slot_g in E. pose proof stride_pos.
assert (snd p = snd p + UNIT + get_stride (MR st g) * j) by (rewrite E at 1; reflexivity). unfold UNIT in *. nia.
Qed.
#[using="RC__ X L BL LS g INV sc cnt IM IG IS"] Lemma slots_pos s m j : s_slots st !! s = Some (m, j) -> 0 < snd s.
Proof.
intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn.
pose proof (sstart0 _ _ _ IM _ _ Hb). pose proof (sstart_mono _ _ _ IG _ _ 0 j Hb ltac:(lia)).
destruct (hosts_ok _ _ _ IG _ _ Hb) as (a & _ & GOm). pose proof (g_align _ _ _ _ _ _ GOm) as [A _]. unfold UNIT in *. lia.
Qed.

#[using="RC__ X L BL LS ai i INV Hg HP ALL sc cnt IM IG IS"] Lemma top_region_empty b h : m_maplen (MR st g) <> 0 -> s_groups st !! b = Some h -> fst b = fst p -> b = p.
Proof.
intros Hml Hb Hf. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hmem & _).
assert (Hm : hosts st b m) by (destruct h as [hm ha]; cbn in Em; subst hm; exists ha; exact Hb).
destruct (aptr_eq_dec m g) as [->|NE]; [exact (hosts_inj _ _ _ IM _ _ _ Hm g_hosts)|]. exfalso.
destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Hml'|Hml'].
- destruct (@top_chain _ _ _ _ IM IG IS m b Hm Hml') as (t & j & c & bt & Ha & Ht & Htop & Hft).
assert (t = g) by (apply (@top_unique _ _ _ IG t g bt p Ht g_hosts Htop Hml); congruence). subst t.
destruct (@anc_hostslot _ _ _ _ IM IG IS m g j c Ha) as (bp & Hp & Hsl).
pose proof (hosts_inj _ _ _ IM _ _ _ Hp g_hosts). subst bp.
destruct (@anc_facts _ _ _ _ IM IG IS m g j c Ha) as (bm' & bp' & _ & _ & _ & Hj & _).
destruct (g_slot_free j Hj) as (_ & N & _). exact (Hsl N).
- apply NE. apply (@top_unique _ _ _ IG m g b p Hm g_hosts Hml' Hml Hf).
Qed.

#[using="ai Hg S1 U1 U2"] Lemma gcnt_K sc' : gcnt st sc' = (if sc =? sc' then cnt else 0) + gcnt st' sc'.
Proof.
rewrite (gcnt_delete st st' p _ sc' Hg K_groups K_metas). unfold gterm. cbn. fold sc. fold cnt. reflexivity.
Qed.

#[using="ai i INV Hg HF NL HO Hi HP ALL sc S1 U1 U2 IR IA IM IL IG IS ISH"] Theorem INVL_kill : INVL X' st' L BL LS.
Proof.
pose proof GO as GOg. pose proof g_hosts as Hgh.
assert (NGm : forall b m, hosts st b m -> m <> g -> b <> p).
{ intros b m Hm NE ->. exact (NE (hosts_fun _ _ _ _ Hm g_hosts)). }
split; [| split; [| split; [| split; [| split; [| split]]]]].
-  destruct IR; constructor; rewrite ?K_regions, ?K_next_rid, ?K_reserved; try assumption.
+ eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite K_frontier. reflexivity.
+ intros rid r H1 H2. rewrite K_frontier. exact (ir_metalen rid r H1 H2).
+ intros rid r H1 H2. rewrite K_frontier. exact (ir_brkfront rid r H1 H2).
+ apply (K_c (fun c => 0 <= c_meta_alloc_shift c /\ (c_meta_alloc_shift c = 0 \/ exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2 ^ c_meta_alloc_shift c * PGSZ))); [intros c U H; exact H| exact ir_shift].
+ apply (K_c (fun c => match c_brk c with
| BrkUntried => ld_brk L = BPUntried /\ forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
| BrkDead => ld_brk L = BPDead
| BrkLive rid off => ld_brk L = BPLive /\ exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off end));
[intros c U H; exact H| exact ir_brk].
+ apply (K_c (fun c => 0 <= c_avail_meta_area_count c /\
(0 < c_avail_meta_area_count c -> c_avail_meta_areas c <> None) /\
(forall rid off, c_avail_meta_areas c = Some (rid, off) -> exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
/\ off + c_avail_meta_area_count c * PGSZ = r_len r /\ (0 < c_avail_meta_area_count c -> r_kind r = RKMeta))));
[intros c U H; exact H| exact ir_cursor].
+ intros rid Ho. unfold X' in Ho. cbn in Ho. unfold nested in Ho. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [E|NE]; [discriminate|].
inversion Ho. subst rid. destruct (g_top _ _ _ _ _ _ GOg NE) as (H0 & r & Hr & Hk & _). exists r. split; [exact Hr|]. split; [exact Hk|].
intros b Hb. rewrite K_groups. destruct (aptr_eq_dec b p) as [->|NEb]; [apply lookup_delete_eq|]. rewrite lookup_delete_ne by congruence.
destruct (s_groups st !! b) eqn:Eb; [| reflexivity]. exfalso. exact (NEb (top_region_empty b _ NE Eb Hb)).
-  destruct K_cf as (cf1 & cf2 & cf3 & cf4 & cf5 & cf6 & cf7 & cf8 & cf9 & cf10 & cf11 & cf12 & cf13 & cf14 & cf15 & cf16 & cf17).
destruct IA; constructor; rewrite ?K_regions, ?K_areas, ?K_secret, ?K_metas, ?cf1, ?cf2, ?cf3, ?cf4, ?cf5, ?cf6, ?cf7, ?cf8, ?cf9, ?cf10, ?cf11, ?cf12, ?cf13, ?cf14, ?cf15, ?cf16, ?cf17; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite K_frontier. auto.
+ intros sc' Hsc'. rewrite K_usage, (U1 sc' Hsc').
pose proof (gcnt_K sc') as GK. rewrite <- (ia_usage sc' Hsc') in GK. rewrite Z.eqb_sym in GK.
destruct (Z.eqb_spec sc' sc) as [E|NE]; [rewrite <- E; lia| lia].
-  destruct IM as [M1 M2 M3 M4 M5] eqn:EIM; constructor; rewrite ?K_MR.
+ intros m Hm. rewrite !K_MR. apply M1. rewrite <- (K_MR m). exact Hm.
+ intros m b Hm. rewrite K_MR in Hm. destruct (aptr_eq_dec m g) as [->|NE]; [right; left; reflexivity|].
destruct (M2 m b Hm) as [H|H]; [left| right; right; exact H]. apply hosts_K. split; [exact H|]. exact (NGm b m H NE).
+ intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NE Hb]. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !K_MR. auto.
+ intros m Hm. rewrite K_metas. exact (M4 m Hm).
+ intros z Hz. rewrite !K_MR, K_groups. cbn in Hz. destruct Hz as [<-|Hz].
* split; [intros [h Hh]; exact (g_unlisted_K h Hh)|]. split; [exact NL|].
split; [exact (proj2 (il_link _ _ IL g) NL)|].
exists p. split; [exact (hosts_mem _ _ _ IM _ _ g_hosts)| apply lookup_delete_eq].
* destruct (M5 z Hz) as (A1 & A2 & A3 & b & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
exists b. split; [exact A4|]. destruct (aptr_eq_dec b p) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; exact A5].
-  destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9] eqn:EIL; constructor; try assumption.
+ intros h. rewrite K_get_head. apply L1.
+ intros h. apply (dll_ext_metas st st' K_metas). apply L2.
+ intros m. rewrite !K_MR. apply L5.
+ intros m Hm. rewrite !K_MR. apply L6. exact Hm.
+ intros sc0 m Hm. destruct (L7 sc0 m Hm) as (A1 & A2 & A3). rewrite K_MR. split; [exact A1|]. split; [| exact A3].
apply live_K; [exact A2|]. intros ->. exact (g_unlisted_K _ Hm).
-  destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
+ intros m b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. pose proof (G1 m b aim Hb) as GOm.
assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hb) g_hosts)).
assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
destruct GOm; constructor; rewrite ?K_MR, ?K_metas, ?K_regions; try assumption.
* intros _. exact (g_partial NF).
* intros _. exact (g_unlisted NF).
* intros _. exact (g_rest NF).
* intros _. exact (g_under NF).
* intros Hml. destruct (g_nest Hml) as (pm & i' & Hs & REST). exists pm, i'. rewrite !K_MR. split; [| exact REST].
rewrite K_slots_other; [exact Hs|]. apply (entry_not_g _ _ _ Hs). intros ->.
destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi' & Eb).
destruct (g_slot_free' i' Hi') as [_ N]. rewrite <- Eb, Hb in N. discriminate.
+ intros b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. exact (G2 b aim Hb).
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite K_groups in H1, H2. apply lookup_delete_Some in H1 as [_ H1]. apply lookup_delete_Some in H2 as [_ H2].
rewrite !K_MR. eapply G3; eassumption.
+ intros rid r Hr Hk Ho. rewrite K_regions in Hr. destruct (G4 rid r Hr Hk ltac:(rewrite HO; discriminate)) as (m & Hm & Hml). exists m. rewrite K_MR. split; [| exact Hml].
apply hosts_K. split; [exact Hm|]. intros E.
assert (Em : m = g) by (apply (hosts_fun st p); [rewrite <- E; exact Hm| exact g_hosts]). subst m.
unfold X' in Ho. cbn in Ho. unfold nested in Ho. rewrite (proj2 (Z.eqb_neq _ _) Hml) in Ho. apply Ho. rewrite <- E. reflexivity.
+ intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. rewrite K_regions. exact (G5 b h Hb).
-  destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
+ intros s m j Hs. destruct (K_slots_some _ _ Hs) as [Hs0 NG]. destruct (S1' s m j Hs0) as (Hl & Hj & Es). rewrite !K_MR.
assert (NEm : m <> g) by (intros ->; exact (NG (entry_g_gslot _ _ Hs0))).
split; [exact (live_K m Hl NEm)|]. auto.
+ intros b m j Hb Hj. rewrite K_MR in Hj |- *. apply hosts_K in Hb as [Hb NEb].
assert (NEm : m <> g) by (intros ->; exact (NEb (hosts_inj _ _ _ IM _ _ _ Hb g_hosts))).
rewrite K_slots_other; [exact (S2 b m j Hb Hj)|]. exact (other_slot_not_g m b j Hb NEm Hj).
+ intros b m aim j Hb Hj. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. rewrite K_MR in Hj. rewrite !K_MR, K_groups. unfold X'. cbn [x_pend].
assert (Hbm : hosts st b m) by (exists aim; exact Hb).
assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ Hbm g_hosts)).
pose proof (S3 b m aim j Hb Hj) as P. cbn zeta in P |- *.
set (s := slot_start' (MR st m) j) in *.
assert (OP : ~ (x_pend X = Some s)).
{ rewrite HP. intros E. apply (other_slot_not_g m b j Hbm NEm Hj). exists i. split; [unfold cnt; lia|].
rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). apply (inj Some) in E. rewrite E. reflexivity. }
unfold one5 in P |- *.
destruct P as (P0 & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
destruct (aptr_eq_dec s p) as [Esp|NEsp].
* assert (Hn : nested = true).
{ unfold nested. apply Z.eqb_eq. destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [E|NE]; [exact E|]. exfalso.
destruct (g_top _ _ _ _ _ _ GOg NE) as [H0 _]. pose proof (slots_pos s m j (S2 b m j Hbm Hj)) as SP. rewrite Esp in SP. lia. }
rewrite Hn. rewrite Esp in *. rewrite lookup_delete_eq.
assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
assert (nA : ~ tbit (m_avail (MR st m)) j = true) by (intros A; exact (nAD (conj A D))).
assert (nB : ~ tbit (m_freed (MR st m)) j = true) by (intros B; exact (nBD (conj B D))).
assert (nC : ~ In p (map bslot BL)) by (intros C; exact (nCD (conj C D))).
clear - nA nB nC. assert (NN : ~ (@None ghdr <> None)) by (intros H; apply H; reflexivity). tauto.
* rewrite lookup_delete_ne by congruence.
assert (NP' : ~ ((if nested then Some p else None) = Some s)) by (destruct nested; [intros E; inversion E; congruence| discriminate]).
revert P0 nAB nAC nAD nAE nBC nBD nBE nCD nCE nDE OP NP'. clear.
generalize (tbit (m_avail (MR st m)) j = true) (tbit (m_freed (MR st m)) j = true) (In s (map bslot BL)) (s_groups st !! s <> None).
generalize ((if nested then Some p else None) = Some s) (x_pend X = Some s). intros. tauto.
+ intros s Hs. unfold X' in Hs. cbn [x_pend] in Hs. unfold nested in Hs. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; [| discriminate]. inversion Hs. subst s.
destruct (g_nest _ _ _ _ _ _ GOg Hml) as (pm & ip & Hs0 & _). rewrite K_slots_other; [rewrite Hs0; discriminate| exact p_not_gslot].
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (m & j & Hs & REST). exists m, j. rewrite K_MR. split; [| exact REST].
rewrite K_slots_other; [exact Hs|]. intros G. destruct (gslot_range _ G) as (j' & Hj' & E).
destruct (g_slot_free' j' Hj') as [NB _]. apply NB. rewrite <- E. apply in_map_iff. exists k. auto.
-  destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
assert (KN : forall q v, known st q v -> known st' q v).
{ intros q v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
assert (UN : forall q, unknown st q -> unknown st' q).
{ intros q. unfold unknown, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
constructor.
+ intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_regions. exact (D1 rid sh Hsh).
+ intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_tick. exact (D2 rid sh Hsh).
+ intros b m j Hb Hj. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hj |- *. apply KN. exact (D3 b m j Hb Hj).
+ intros b m o Hb Ho. apply hosts_K in Hb as [Hb _]. apply UN. exact (D4 b m o Hb Ho).
+ intros b m pm j Hb Hml Hs. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hml. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR.
destruct (D5 b m pm j Hb Hml Hs0) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
split; [exists v3; auto|]. auto.
+ intros k m j Hk Hs. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR. pose proof (D6 k m j Hk Hs0) as B. cbn zeta in B |- *.
destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [exact A5|]. split.
* intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; auto.
* split; [intros Hres; apply KN; apply A7; exact Hres|]. intros a Ha. apply UN. apply A8. exact Ha.
Qed.

#[using="RC__ X L BL LS ai INV Hg sc S1 U1 U2 IR IG"] Lemma kill_top : m_maplen (MR st g) <> 0 ->
exists r, snd p = 0 /\ s_regions st' !! (fst p) = Some r /\ r_kind r = RKGroup
/\ m_maplen (MR st g) * 4096 = round_up_pg (r_len r) /\ 0 < m_maplen (MR st g) * 4096.
Proof.
intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r & Hr & Hk & E & _). exists r. rewrite K_regions.
pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _). pose proof (round_up_ge_k (r_len r)). repeat split; auto. lia.
Qed.

#[using="RC__ X L BL LS ai i INV Hg Hi sc S1 U1 U2 IM IG IS"] Lemma kill_nested : m_maplen (MR st g) = 0 ->
exists pm ip bpm, s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
/\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
/\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48
/\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
/\ gend (MR st g) <= sstart (MR st pm) ip + get_stride (MR st pm).
Proof.
intros Hml. destruct (g_nest _ _ _ _ _ _ GO Hml) as (pm & ip & Hs & Hf & He & Hsc & Hstr).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpm Hpm] & Hip & Ep).
exists pm, ip, bpm.
assert (NE : pm <> g) by (intros ->; lia).
split; [rewrite K_slots_other; [exact Hs| exact p_not_gslot]|].
split; [apply hosts_K; split; [exact Hpm|]; intros ->; exact (NE (hosts_fun _ _ _ _ Hpm g_hosts))|].
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm) in Ep.
split; [rewrite Ep; reflexivity|]. repeat split; auto; lia.
Qed.

#[using="RC__ X L BL LS ai i INV Hg Hi sc S1 U1 U2 IA IM IG IS ISH"] Lemma dec_hdr_eq {T} (k : aptr -> Z -> M T) bail :
m_maplen (MR st g) = 0 ->
exists pm ip bpm, dec_hdr st' p k bail = k pm ip
/\ s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
/\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
/\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48.
Proof.
intros Hml. destruct (kill_nested Hml) as (pm & ip & bpm & Hs' & Hpm' & Hf & Hip & Ep & Hsc & Hstr & Hend).
exists pm, ip, bpm. split; [| repeat split; auto; lia].
pose proof Hpm' as Hpm. apply hosts_K in Hpm as [Hpm NEb].
destruct (hosts_ok _ _ _ IG _ _ Hpm) as (aipm & Hgpm & GOpm).
assert (Hs : s_slots st !! p = Some (pm, ip)) by (destruct (K_slots_some _ _ Hs') as [H _]; exact H).

pose proof (ish_nest _ _ ISH p g pm ip g_hosts Hml Hs) as NS. cbn zeta in NS. rewrite (hosts_gbase _ _ _ IM _ _ Hpm) in NS.
set (q := (snd p - snd bpm - UNIT) / UNIT) in NS.
destruct NS as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
pose proof (ish_hdr0 _ _ ISH bpm pm ip Hpm ltac:(unfold cnt_of; lia)) as K4.
assert (KN : forall a v, known st a v -> known st' a v).
{ intros a v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
assert (Hq : UNIT * q = get_stride (MR st pm) * ip).
{ subst q. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm).
replace (snd bpm + UNIT + get_stride (MR st pm) * ip - snd bpm - UNIT) with (size_class (m_sizeclass (MR st pm)) * ip * UNIT) by (rewrite Hstr; lia).
rewrite Hstr. unfold UNIT. rewrite Z.div_mul by lia. lia. }
clearbody q.
pose proof (g_align _ _ _ _ _ _ GOpm) as [A0 A16].
unfold dec_hdr, get_meta.
rewrite (guard_true 10).
2:{ apply Z.eqb_eq. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), Hstr. unfold UNIT in *.
replace (snd bpm + 16 + 16 * size_class (m_sizeclass (MR st pm)) * ip) with (snd bpm + (1 + size_class (m_sizeclass (MR st pm)) * ip) * 16) by lia.
rewrite Z_mod_plus_full. exact A16. }
unfold rd16.
rewrite (rd8_known st' (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [apply KN; exact K2| cbn; lia| reflexivity]).
rewrite (rd8_known st' (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [apply KN; exact K1| cbn; lia| reflexivity]).
rewrite (rd8_known st' (aadd p (-3)) v3) by (eapply known_at; [apply KN; exact K3| cbn; lia| reflexivity]).
rewrite (rd8_known st' (aadd p (-4)) 0).
2:{ eapply known_at; [apply KN; exact K4| rewrite Ep; cbn; unfold IB; lia| rewrite Ep; reflexivity]. }
cbn [Z.eqb negb].
rewrite (u16_bytes q Q).
assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bpm).
{ rewrite Ep. unfold aadd, sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm). destruct bpm as [br bo]. cbn [fst snd] in *. f_equal. lia. }
rewrite Ebase. unfold get_group. destruct Hpm' as [ai' Hg']. rewrite Hg'. cbn [g_meta]. rewrite E3. fold (MR st' pm). rewrite !K_MR.
rewrite (guard_true 11) by (rewrite (hosts_mem _ _ _ IM _ _ Hpm); apply optr_eqb_refl).
rewrite (guard_true 12) by (apply Z.leb_le; lia).
pose proof (is_part _ _ _ IS _ _ _ ip Hgpm Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm), <- Ep in P. unfold one5 in P.
assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
rewrite (guard_true 13) by (unfold testbit; destruct (Z.testbit (m_avail (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
rewrite (guard_true 14) by (unfold testbit; destruct (Z.testbit (m_freed (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
pose proof (g_present _ _ _ _ _ _ GOpm) as Pr. destruct (s_metas st !! pm) as [mr|] eqn:Em; [| congruence].
destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
destruct K_cf as (cf1 & _).
rewrite (guard_true 15) by (rewrite K_areas, Emk, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; unfold ctx; rewrite cf1; exact Hck).
pose proof (size_class_bound (m_sizeclass (MR st pm))) as SB.
rewrite (guard_true 16).
2:{ clear KN K2 K1 K3 K4 P D Ebase. destruct (Z.ltb_spec (m_sizeclass (MR st pm)) 48); [| lia]. rewrite Hstr in Hq.
assert (Eq : q = size_class (m_sizeclass (MR st pm)) * ip) by (unfold UNIT in Hq; lia).
assert (G0 : 0 <= m_sizeclass (MR st g)) by (destruct (g_sc _ _ _ _ _ _ GO) as [[[G0 _] _]|(G63 & _)]; lia).
rewrite Eq. specialize (SB ltac:(lia)). apply Bool.andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt]. rewrite Z.mul_add_distr_l. lia. }
rewrite (guard_true 17).
2:{ destruct (Z.eqb_spec (m_maplen (MR st pm)) 0) as [|NM]; cbn [negb]; [reflexivity|].
destruct (g_top _ _ _ _ _ _ GOpm NM) as (B0 & _ & _ & _ & _ & GE). apply Z.leb_le.
unfold gend, cnt_of, sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), B0 in GE.
pose proof (stride_ge _ _ _ IG _ _ Hpm) as [S16 _]. unfold UNIT in S16, Hq, GE.
clear KN K2 K1 K3 K4 P D Ebase SB.
eapply (guard17_arith (get_stride (MR st pm)) ip 0 0 q (m_last_idx (MR st pm)) (m_maplen (MR st pm))); try lia. }
reflexivity.
Qed.
End KILL.

#[using="Type"] Lemma fg_st1 X st L BL LS g p ai (INV : INVL X st L BL LS) (Hg : s_groups st !! p = Some (mkGhdr (Some g) ai)) :
let sc := m_sizeclass (MR st g) in
let cnt := m_last_idx (MR st g) + 1 in
let st1 := if sc <? 48 then set_usage sc (usage st sc - cnt) st else st in
(exists U, st1 = upd_ctx (fun c => set_usage_map U c) st)
/\ (forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc')
/\ (forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48).
Proof.
cbn zeta. pose proof (ia_usage_keys _ (proj1 (proj2 INV))) as UK.
pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as SC.
destruct (Z.ltb_spec (m_sizeclass (MR st g)) 48) as [LT|GE].
- split; [eexists; reflexivity|]. split.
+ intros sc' Hsc'. apply usage_set_usage.
+ intros sc0 v. cbn. destruct (Z.eq_dec sc0 (m_sizeclass (MR st g))) as [->|NE].
* intros _. destruct SC as [[A _]|(A & _)]; lia.
* rewrite lookup_insert_ne by congruence. apply UK.
- split; [| split; [| exact UK]].
+ exists (c_usage (s_ctx st)). destruct st as [c ? ? ? ? ? ? ? ? ? ?]; destruct c; reflexivity.
+ intros sc' Hsc'. destruct (Z.eqb_spec sc' (m_sizeclass (MR st g))); [lia| reflexivity].
Qed.

End RC__1.
