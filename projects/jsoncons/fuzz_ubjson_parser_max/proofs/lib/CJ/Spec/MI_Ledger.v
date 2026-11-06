(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Ledger () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."], [["0BL"; "1None"; "1Some"; "1bool"; "1cons"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "2or"]; ["3N"; "3Z"; "0F"; "0L"; "0L'"; "0LS"; "0RUNp"; "4alloc_ceiling"; "5lbrk_pages_ok"; "5lranges"; "6INVL"; "6frontier"; "7PGSZ"; "7RKGroup"; "7brk_pages_ok"; "7is_err"]; ["7live_ranges"; "7mkRegion"; "7mmap_answer_ok"; "7mstate"; "7ranges_free"; "7region"; "7round_up_pg"; "7s_regions"; "8In"; "8filter"; "9Permutation"; ":add"; ":le"; ":lt"; ":modulo"; "0X'"]; ["0a"; "0len"; "0live"; "0lo"; "0n"; "0q"; "0r"; "0rid"; "0rq"; "0st"; "0st'"; ";insert"; ";lookup"; "<N_countable"; "=map_insert"; "=map_to_list"]; [">gmap"; ">gmap_fold"; ">gmap_lookup"; ">gmap_partial_alter"; "?eq_dec"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma In_map_to_list_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "Q5'Q3'@'Q5&=&Q8'9%1254(8r2r1%349821&QO'R0&R4&QM%34>21=&R1%14@43?&Q7r3%211%:5DC641%B3@<1'<'7%11G&QL&R2%14K?>J%36LK>1E9(2%12MF%93731%N2;1pS>Q01pS@Q21pSDQ41").
Proof. intros st rid r.
split.
- intros H. apply elem_of_map_to_list. apply list_elem_of_In. exact H.
- intros H. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact H.
Qed.
Section RANGES.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : inv_R X st L.
Section SE.
Local Abbreviation SEC_T_lranges_iff := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "@'9'A%2211&=&Q8r1&IvC%211%53741&Q0vQI%211%93;81%;251pT<=1")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_lranges_iff) 0%nat 0%nat).
Lemma lranges_iff : ltac:(sec_stmt2 constr:(SEC_T_lranges_iff) 1%nat 0%nat).
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
End SE.
Lemma forallb_ext {A} (f : A -> bool) l1 l2 : (forall x, In x l1 <-> In x l2) -> forallb f l1 = forallb f l2.
Proof.
intros H. destruct (forallb f l1) eqn:E1; destruct (forallb f l2) eqn:E2; try reflexivity.
- rewrite forallb_forall in E1. assert (E2' : forallb f l2 = true) by (apply forallb_forall; intros x Hx; apply E1; apply H; exact Hx). congruence.
- rewrite forallb_forall in E2. assert (E1' : forallb f l1 = true) by (apply forallb_forall; intros x Hx; apply E2; apply H; exact Hx). congruence.
Qed.
Lemma ranges_free_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "A'A'<'3&Q4&IvC%211r2r1%63321&Q0vQI%211%:3165%=3<51pS:?1pS2@1").
Proof. intros a n. unfold ranges_free. apply forallb_ext. apply lranges_iff. Qed.
Lemma mmap_answer_ok_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "B'A'<'3&Q2vF&IvC%211r2r1%746321&Q0vQI%211%;4:165%>3=51pS>@1pS4A1").
Proof. intros len r. unfold mmap_answer_ok. rewrite ranges_free_eq. reflexivity. Qed.
Lemma brk_pages_ok_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "?'A'<'3&HvFvCr2r1%544321&NvQI%247154%;3:41pS4=1pS8>1").
Proof. intros lo len. unfold lbrk_pages_ok, brk_pages_ok. rewrite ranges_free_eq. reflexivity. Qed.
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
Lemma mmap_ok_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "Q@'6'9'A%2211%411'<'3&Q2vFr3r2r1%544321(:%93821&O%116(5%=3<21';&Q=z%221=&Q>&L%22@1%E3H15&Q<&Q;&Q6r4%211%42G1&G%11J%8231&Q4r5%231M7%Q23Q11J%E251%F2?1%G2D1p0I1p0N1pS>Q;1pS4Q<1pS6Q;1").
Proof. intros live len r.
unfold mmap_answer_ok, is_errno_form, is_err. intros H E.
apply Bool.orb_true_iff in H. destruct H as [H|H].
- apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_ge in E. unfold TWO64 in *. lia.
- apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.
Lemma regions_insert_perm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "QE'Q3'@'Q5'9%1232'3p021'<'7%117&QL'R0&R4&QM%34=21<&R2%14?43>r3&Q7r4%211%;6DC7541(1%11E%A3?31'Q:&Q9r2&QO&R1%14MBAL&QK&QN&R3%14Q1FEQ0%34Q2Q1E1r5%C11%77Q5Q4H3CE1%;5Q6Q5I91%>3Q4=1(4(8%14Q:Q9HJ%@5Q;Q:N>7%43Q921%D3Q:C1%F3Q;71p0H1pQ6Q;1pS>Q@1pS@QB1pSDQD1").
Proof. intros st rid r F. intros H. apply perm_filter. apply map_to_list_insert. exact H. Qed.
Section NEW_GROUP_REGION.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r len : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = None.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Hypothesis HLEN : 0 < len < LEN_MAX.
Let rid := s_next_rid st.
Let st' := fst (new_region RKGroup r len st).
Let L' := KInv.set_groups ((r, len) :: ld_groups L) L.
Let X' := xorph X (Some rid).
Lemma ng_fresh : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "D'<'7'Q5%211&QL'@'R0&R4&QM%344217&R2%146439vQG&Q7vQI%211%<6;>7541(1%11@%C3@31").
Proof.
destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma ng_lookup q : s_regions st' !! q = if (q =? rid)%N then Some (mkRegion RKGroup r len) else s_regions st !! q.
Proof. unfold st'. apply lookup_new_region. Qed.
Lemma ng_keep : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "N'@'Q5'<'7%113&QL'R0&R4&QM%349218&R2%14;43:r2&Q7vQI%211%;6@?7541(2r1%22B1%B3@41r3vQJ%:11%C6HG?=31%82H=%H3F21p071pSBK1pS<M1").
Proof. intros q rq. intros H. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite ng_fresh in H; discriminate| exact H]. Qed.
Lemma ng_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "Q='@'Q5'<'7%113&QL'R0&R4&QM%349218&R2%14;43:r2&Q7vQJ%211%;6@?7541(2r1%22B1%B3@41'?';r3vQG%G3I21(Q1(MvQFvQA%43321%M3NC1%:271&>%119vQI%G11%Q06Q5Q4LJ>1%E2Q5J%Q53Q321%B261%D291p0F1pSBQ:1pS<Q<1").
Proof. intros q rq. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma ng_frontier : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger ">'@'Q5'<'A&KvQJr2r1%43321vQI%63143%93831pSB;1pS<=1"). Proof. intros q rq. reflexivity. Qed.
Theorem INVL_new_group_region : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Ledger "8&JvFvQ?vQJvDv0vE%76654321").
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
End CEIL_WRAP_1.
