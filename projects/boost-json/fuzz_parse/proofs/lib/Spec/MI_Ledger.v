(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06region37Corelib7Numbers7BinNumsk61N25stdpp9countablem3bN_countable35stdpp7numbers1No26eq_dec09s_regions25stdpp4gmapq74gmap37Corelib4Init9Datatypesra4Somera6optionra4pairra4prod37Corelib4Init5Logicv02eqv03iff06mstate36Stdlib5Lists4Listhh72In25stdpp4basehj06lookup25stdpp8fin_mapshk6bmap_to_listq79gmap_foldq7bgmap_lookupk61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~ho37lranges0blive_ranges0branges_freera4bool0emmap_answer_okho3dlbrk_pages_ok0cbrk_pages_okv03andra4true0bround_up_pgra5falsera4list04PGSZ0dalloc_ceiling06is_err46Stdlib6ZArith6BinInt1Zim03addim02leim02ltim06modulohh76filterra4Nonera4cons36Stdlib7SortingbPermutationiqdbPermutationhj06inserthk6amap_insertq7h2gmap_partial_alter79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~jg65inv_Rjg64INVLjg66x_orphho37LEN_MAX" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_map_to_list_regions : ltac2:(zQ "h20!je!lf!n4!p3!pc!r3!t2!t9!u2!u9!hg4!hg9!hgf!hia!hjc!hl6!hm5!hn1>2st$c>3rid$1>1r$0@2$b@3$d@2$9$1$0@4$8$1$0^2^1@5$f$1$0@4$5$1$3$2$0@4$h0$1$3$2$0@1$4^3@3$a@1$7$0@6$e$1$0@4$5$1$3$2$0@4$h1$1$3$2$0^2@1$4^3@2$6$0^1").
Proof. intros st rid r.
  split.
  - intros H. apply elem_of_map_to_list. apply list_elem_of_In. exact H.
  - intros H. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact H.
Qed.

Section RANGES.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : ltac2:(zQ "10!jk4@3$0?1X?2st?1L").

Lemma lranges_iff : ltac2:(zQ "60!hnf!u9!hia!hg9!hrf!hsa>1x@2$1$0$0@2$3@3$2@2$1$0$0^1@1$4?1L@3$2@2$1$0$0^1@1$5?2st").
Proof. intros x.
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

Lemma forallb_ext {A} (f : A -> bool) l1 l2 : (forall x, In x l1 <-> In x l2) -> forallb f l1 = forallb f l2.
Proof.
  intros H. destruct (forallb f l1) eqn:E1; destruct (forallb f l2) eqn:E2; try reflexivity.
  - rewrite forallb_forall in E1. assert (E2' : forallb f l2 = true) by (apply forallb_forall; intros x Hx; apply E1; apply H; exact Hx). congruence.
  - rewrite forallb_forall in E2. assert (E1' : forallb f l1 = true) by (apply forallb_forall; intros x Hx; apply E2; apply H; exact Hx). congruence.
Qed.

Lemma ranges_free_eq : ltac2:(zQ "60!hnf!ht7!hu4!hg4!hrf!hsa>1a$0>1n$0@3$3$2@3$1@1$4?1L^2^1@3$1@1$5?2st^2^1").
Proof. intros a n. unfold ranges_free. apply forallb_ext. apply lranges_iff. Qed.

Lemma mmap_answer_ok_eq : ltac2:(zQ "60!hnf!hub!hu4!hg4!hrf!hsa>3len$0>1r$0@3$3$2@3$1@1$4?1L^2^1@3$1@1$5?2st^2^1").
Proof. intros len r. unfold mmap_answer_ok. rewrite ranges_free_eq. reflexivity. Qed.

Lemma brk_pages_ok_eq : ltac2:(zQ "50!hnf!hu4!hg4!hvb!igc>2lo$0>3len$0@3$2$1@3$3?1L^2^1@3$4?2st^2^1").
Proof. intros lo len. unfold lbrk_pages_ok, brk_pages_ok. rewrite ranges_free_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ranges_free_regions a n rid r : ranges_free (live_ranges st) a n = true -> s_regions st !! rid = Some r ->
  let '(b, l) := region_live_range r in a + n <= b \/ b + l <= a.
Proof.
  intros H Hr. unfold ranges_free in H. rewrite forallb_forall in H.
  specialize (H (region_live_range r)). destruct (region_live_range r) as [b l] eqn:E.
  assert (Hin : In (b, l) (live_ranges st)).
  { unfold live_ranges. apply in_app_iff. right. apply in_map_iff. exists (rid, r). rewrite <- E. split; [reflexivity| apply In_map_to_list_regions; exact Hr]. }
  specialize (H Hin). cbn in H. unfold iv_disjoint in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; [apply Z.leb_le in H| apply Z.leb_le in H]; lia.
Qed.
End RANGES.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_ok_facts : ltac2:(zQ "h20!hnf!hg4!hu4!iha!ii0!ii7!ij4!ijc!u9!ik3!ik9!il8!hub!ht7!in8!inf!io5!iob>4live@1$7@2$8$0$0>3len$0>1r$0>0@3$1$2@3$c^3^2^1$4>0@3$1$2@1$b^2$6@2$3@2$h0Z^3@2$3@3$1$0@2$h1^3$9Z@2$3@2$f@2$e^3@1$5^4$a@3$1$2@3$d^5^3@1$5^4$4").
Proof. intros live len r.
  unfold mmap_answer_ok, is_errno_form, is_err. intros H E.
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_ge in E. unfold TWO64 in *. lia.
  - apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma regions_insert_perm : ltac2:(zQ "h70!je!lf!n4!p3!u9!r3!pc!ip5!hl6!hm5!ipf!hu4!iq6!t9!u2!hg4!hgf!is9!it8!hjc!iu2!hn1!iv0>2st$h0>3rid$1>1r$0>1F>0@2$4$1$0$b>0@3$f@1$d$0@6$h3$1$0@4$5$1$3$2$0@4$h5$1$3$2$0^3@1$6^4@1$a$0@3$h1@2$4$1$0@3$7@2$4$1$0^2@5$8$1$0@4$5$1$3$2$0@4$9$1$3$2$0@7$h2$1$0@4$5$1$3$2$0@4$h4$1$0@4$5$1$3$2$0@4$h6$1$3$2$0^4^3@1$6^5@3$7@2$4$1$0^2@3$c@2$4$1$0@4$e$1$0^4^3@5$8$1$0@4$5$1$3$2$0@4$9$1$3$2$0@1$6^5").
Proof. intros st rid r F. intros H. apply perm_filter. apply map_to_list_insert. exact H. Qed.

Section NEW_GROUP_REGION.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r len : Z).
Hypothesis INV : ltac2:(zQ "10!jkd@5$0?1X?2st?1L?2BL?2LS").
Hypothesis HO : ltac2:(zQ "50!lf!ipf!t9!hg4!jl5@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis HOK : ltac2:(zQ "50!hu4!ii0!hg4!hsa!hub@3$2$0@3$4@1$3?2st?3len?1r$1").
Hypothesis NERR : ltac2:(zQ "40!hu4!ij4!hg4!il8@3$2$0@1$3?1r$1").
Hypothesis HLEN : ltac2:(zQ "30!io5!iha!jlf@2$1@2$0Z?3len@2$0?3len$2").
Let rid := s_next_rid st.
Let st' := fst (new_region RKGroup r len st).
Let L' := KInv.set_groups ((r, len) :: ld_groups L) L.
Let X' := xorph X (Some rid).

Lemma ng_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma ng_lookup q : s_regions st' !! q = if (q =? rid)%N then Some (mkRegion RKGroup r len) else s_regions st !! q.
Proof. unfold st'. apply lookup_new_region. Qed.
Lemma ng_keep q rq : s_regions st !! q = Some rq -> s_regions st' !! q = Some rq.
Proof. intros H. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite ng_fresh in H; discriminate| exact H]. Qed.
Lemma ng_some q rq : s_regions st' !! q = Some rq -> (q = rid /\ rq = mkRegion RKGroup r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma ng_frontier q rq : frontier st' q rq = frontier st q rq. Proof. reflexivity. Qed.

Theorem INVL_new_group_region : INVL X' st' L' BL LS.
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
    + intros q rq k Hq K H1 H2 H3. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [destruct K as [K|K]; discriminate|]. rewrite ng_frontier in H2. exact (ir_pages q rq k Hq K H1 H2 H3).
    + destruct ir_mshift as (Q1 & Q2 & Q3). split; [| split].
      * intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. exact (Q1 q rq Hq K).
      * intros q1 q2 r1 r2 H1 H2 K1 K2 E. apply ng_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply ng_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
        exact (Q2 q1 q2 r1 r2 H1 H2 K1 K2 E).
      * intros j Hj. destruct (Q3 j Hj) as (q & rq & Hq & K & E). exists q, rq. split; [apply ng_keep; exact Hq| auto].
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite ng_frontier. split; [apply ng_keep; exact Hq| auto].
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
  - apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5 GOE]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
      * intros q rq Hq K E. apply ng_keep. exact Hq.
      * apply (group_ok_X X); [reflexivity|]. exact (G1 m b ai Hb).
    + exact G2.
    + exact G3.
    + intros q rq Hq K Ho. apply ng_some in Hq as [[-> ->]|[NE Hq]].
      * exfalso. apply Ho. reflexivity.
      * apply (G4 q rq Hq K). rewrite HO. discriminate.
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply ng_keep; exact Hq| exact K].
    + exact GOE.
  - apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity| intros q rq Hq _ _; apply ng_keep; exact Hq|]. apply (inv_S_X X); [reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
Qed.
End NEW_GROUP_REGION.
