(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_WFree.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WFree2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Tree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1option"; "1orb"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"]; ["3N"; "3Z"; "0F"; "0L"; "0L'"; "0LS"; "0LS'"; "0P"; "0RUNp"; "4brk_quiet"; "4g_remove"; "4ld_groups"; "4mled"; "5INVL"; "5bl_remove"; "5blk"]; ["5extras"; "5inv_R"; "5inv_S"; "5x0"; "5x_pend"; "6ftree"; "7RKGroup"; "7UNIT"; "7aadd"; "7aptr"; "7bit"; "7cptr"; "7free"; "7lhead"; "7mstate"; "7r_base"]; ["7r_cells"; "7r_hav"; "7r_havp"; "7r_kind"; "7r_len"; "7region"; "7rkind"; "7round_up_pg"; "7s_regions"; "7s_shadow"; "7s_tick"; "7shadow"; "8In"; "8filter"; "9le"; ":Permutation"]; [";add"; ";eqb"; ";le"; ";lor"; ";lt"; ";mul"; ";pow"; ";testbit"; "0T"; "0X"; "0X'"; "0b"; "0c"; "0ch"; "0f"; "0hl"]; ["0i"; "0j"; "0l"; "0lG"; "0n"; "0o"; "0off"; "0pg"; "0q"; "0r"; "0rest"; "0rid"; "0rq"; "0sh"; "0st"; "0st'"]; ["<delete"; "<lookup"; "=N_countable"; "=Z_countable"; ">map_delete"; ">map_to_list"; "?gmap"; "?gmap_fold"; "?gmap_lookup"; "?gmap_partial_alter"; "@eq_dec"; "Aeq_dec"; "0t"; "0u"; "0w"; "0x"]; ["0y"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma add_bit_lor : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "K'A&R2zr2%3221'='2&R7r4r3%3221(4%73621&R0r5&R6+2%2219%5241&R3%1263%@3E31p0:1p0C1p0D1pU2I1pTNJ1").
Proof. intros f i.
intros Hf Hi Hb. rewrite <- Z.lxor_lor.
- apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros j Hj.
rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
+ rewrite Hb. reflexivity.
+ rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
- apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
+ rewrite Hb. reflexivity.
+ rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.
Lemma testbit_add_bit : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "Q1'A&R2zr3%3221'='2&R7r6r5%3221(4%73621&R0r7&R6+2%2219%5241%<21:&8%>27<&R1%12?>%4231%D3C61p0>1p0G1p0H1p0I1pU4N1pU2O1pTNQ01").
Proof. intros f i j.
intros Hf Hi Hj Hb. rewrite (add_bit_lor f i Hf Hi Hb). rewrite Z.lor_spec. f_equal.
destruct (Z.eqb_spec i j) as [<-|NE]; [apply Z.pow2_bits_true; lia| apply Z.pow2_bits_false; lia].
Qed.
Lemma bit_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 ":'A'=&Q:r1%211&R6+2%2214%73841pU291"). Proof. intros i. reflexivity. Qed.
Section WR.
Variables (st : mstate) (q : aptr) (v : Z).
Let st' := wr8 q v st.
Lemma wr8_shadow_lookup rid :
s_shadow st' !! rid = if (rid =? fst q)%N then Some (mkShadow (<[snd q := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst q)))) (r_hav (get_shadow st (fst q))) (r_havp (get_shadow st (fst q)))) else s_shadow st !! rid.
Proof.
unfold st', wr8, upd_shadow. cbn. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma wr8_dom : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "Q>'@!p021'QK'='7%113&S1'S6&S:&S2%34;218&S8%14=43:r2&QIvRN%211%;6B?7541(1r1%22B1%B3@41r4r3%211p041pULH1pUHL1&5'AvRH%33Q021%C11vRO%D11%M6Q4Q1IGF1%Q13O1@r6%11?p031pULQ61pUHQ:1p0:1p0@1pQ@Q;1").
Proof. intros P.
intros H Hq rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [auto|]. apply H.
Qed.
Lemma wr8_tks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "SM'@&QN&QJvRN%211r1%5221'QK'='7%113&S1'S6&S:&S2%34?218&S8%14A43:r2&QI%11A%:6E>6431(1%12@B%@3>31'<'A':%122L%D11&S;&S3%D46214%A47325r3&Q@r5%211%K6<:6541(9%14>Q8FQ3%C2=1%Q23=41&R2z%221;&R4+X0%22>1%H241r9%QB2Q11%K231p0;1pVJQF1pVNM1pU<N1'6%11N%QB11%Q@4Q2NM2%Q=4Q3ON3&QA%11K%QE6Q6643N1%Q;27Q?%QJ3721&QL%13Q8QBQ2&;%13Q<R6Q4r:%R7221p051p081pTLQ?1pU0B1pVLQC1%R51R>%R34QEQAQ@R?%R04QFQBQAR@&QBr4%211%R96QJRD54R21%QO2RER@%R>3821r8%RG2R61p031pVJRJ1pU@R11%R32?1%R42Q51p0R61pULRH1pUHS01vRO%R?11%RH6S3RLRDRBRA1%RL3RJ1R=%S42RCN%R=2QE1p0QM1pVJS81pVNR?1pU<R@1r;%S;2Q61p0Q91p0Q<1pTLRC1pU0QF1pVLRG1p0LQOpVJSC1pU@RJ1%RL241%RM2<1p0C1pULSA1pUHSI1p0J1p0SE1pTBSL1").
Proof. intros T.
intros HT H rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
intros E. inversion E. subst sh. cbn.
assert (G : forall o w t, r_cells (get_shadow st (fst q)) !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N).
{ intros o w t Ho. unfold get_shadow in Ho. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Ho.
- exact (proj1 (H _ _ E0) o w t Ho).
- rewrite lookup_empty in Ho. discriminate. }
assert (G2 : forall u hl ch, r_hav (get_shadow st (fst q)) !! u = Some hl -> In ch hl -> (snd ch <= T)%N).
{ intros u hl ch Hu Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hu.
- exact (proj1 (proj2 (H _ _ E0)) u hl ch Hu Hin).
- rewrite lookup_empty in Hu. discriminate. }
assert (G3 : forall pg t, r_havp (get_shadow st (fst q)) !! pg = Some t -> (t <= T)%N).
{ intros pg t Hp. unfold get_shadow in Hp. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hp.
- exact (proj2 (proj2 (H _ _ E0)) pg t Hp).
- rewrite lookup_empty in Hp. discriminate. }
split; [| split; [exact G2| exact G3]].
intros o w t. destruct (Z.eq_dec o (snd q)) as [->|NEo].
- rewrite lookup_insert_eq. intros X. inversion X. subst. split; [| exact HT].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- rewrite lookup_insert_ne by congruence. apply G.
Qed.
End WR.
Definition xpend (X : extras) (p : option aptr) : extras := mkX (x_idle X) (x_zomb X) p (x_orph X) (x_fresh X).
Definition xorph (X : extras) (o : option N) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) o (x_fresh X).
Definition NTF_SPEC : Prop :=
forall (T : Type) (f : nat) X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
(1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
exists st' mi LS',
nontrivial_free dec_hdr f st g i k bail = k st' mi /\
match mi with
| None => INVL (xpend X None) st' L BL LS'
| Some (base, len) =>
exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
/\ len = round_up_pg (r_len r) /\ 0 < len
/\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
end.
Lemma g_remove_perm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "Q4'6':'A%2211%411'QOr4(3(9r2r1%349921r3%63:21%93;81&QLr5%23>71&?'=&5%13CC<%33D16%511p071pW2F1&Jr6%22F1%H3J1=p051p0A1pU6N1pTHO1pUFN1pU8O1").
Proof. intros lG.
induction lG as [|y lG IH]; intros rest b l P Hr.
- apply Permutation_nil_cons in P. destruct P.
- cbn. assert (Hy : In y ((b, l) :: rest)) by (eapply Permutation_in; [exact P| left; reflexivity]).
destruct (Z.eqb_spec (fst y) b) as [E|NE].
+ destruct Hy as [<-|Hy]; [| exfalso; exact (Hr _ Hy E)].
apply Permutation_cons_inv with (a := (b, l)). exact P.
+ destruct Hy as [<-|Hy]; [cbn in NE; congruence|].
destruct (in_split _ _ Hy) as (r1 & r2 & ->).
assert (P' : Permutation lG ((b, l) :: r1 ++ r2)).
{ apply Permutation_cons_inv with (a := y). eapply Permutation_trans; [exact P|].
change ((b, l) :: r1 ++ y :: r2) with (((b, l) :: r1) ++ y :: r2). change (y :: (b, l) :: r1 ++ r2) with (y :: ((b, l) :: r1) ++ r2).
apply Permutation_sym. apply Permutation_middle. }
eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip. apply (IH _ _ l P').
intros z Hz. apply Hr. apply in_app_iff in Hz. apply in_app_iff. cbn. tauto.
Qed.
Lemma round_up_ge : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "7'A&R2r1&QG%112%4231pW061").
Proof. intros x. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.
Lemma perm_filter {A} (f : A -> bool) l l' : Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
induction 1; cbn.
- constructor.
- destruct (f x); [apply perm_skip|]; assumption.
- destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
- eapply Permutation_trans; eauto.
Qed.
Lemma regions_delete_perm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "QE'Q>'@'QE':%1232'2p021'='7%117&S1'S6&S:&S2%34=21<&S8%14?43>r3&QHr4%211%;6DC7541(1r2%22F1%B3@41'QO&QM&S5&S7%14MBALr5%>11%55Q0OC31%73N;1(3(9%14Q4Q3BD&S0&S4&S9%14Q8MLQ7%34Q9Q8L1%55Q:M1H;%@5Q;Q:N>1%:3Q981%C3Q:G1%E3Q;=1p0G1pQ6Q;1pUDQ@1pUHQB1pUNQD1").
Proof. intros st rid r F. intros H. apply perm_filter. apply Permutation_sym. apply map_to_list_delete. exact H. Qed.
Lemma inv_S_X : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "J'Q0'Q>'6&O%211'='7&Q9%211&Q4r3%211r4%411%93631'Q2r5r2%33281%43379p021p071p2B1pUNF1pTFH1pTDI1").
Proof. intros X X' st BL. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
Section DROP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (r : region).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = Some rid.
Hypothesis Hr : s_regions st !! rid = Some r.
Let st' := drop_region rid st.
Let L' := KInv.set_groups (g_remove (r_base r) (ld_groups L)) L.
Let X' := xorph X None.
Lemma drop_lookup q : s_regions st' !! q = if (q =? rid)%N then None else s_regions st !! q.
Proof. apply lookup_drop_region. Qed.
Lemma drop_keep : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "Q4'@'QE'='7%113&S1'S6&S:&S2%349218&S8%14;43:r2&QHvRN%211%;6@?7541(1r1%22B1%B3@41&?r3vRK%F3H21%411r4vRO%?11%H6MLDB31%=2M8%M3K21p071p0=1pUJQ11pUBQ31").
Proof. intros q rq. intros H NE. rewrite drop_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.
Lemma drop_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "Q4'@'QE'='7%113&S1'S6&S:&S2%349218&S8%14;43:r2&QHvRO%211%;6@?7541(1r1%22B1%B3@41'<r3vRN%;11%D6IH@>31%92I>%I3G21&?vRK%L3N81%311%;251p0=1pUJQ11pUBQ31").
Proof. intros q rq. rewrite drop_lookup. destruct (N.eqb_spec q rid); [discriminate| auto]. Qed.
Theorem INVL_drop_orph : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "8&MvHvR:vROvDv0vE%76654321").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ir_orph _ _ _ IR rid HO) as (r0 & Hr0 & Hk & NOG). rewrite Hr in Hr0. symmetry in Hr0. inversion Hr0. subst r0. clear Hr0.
assert (KEEP : forall q rq, s_regions st !! q = Some rq -> r_kind rq <> RKGroup \/ q <> rid -> s_regions st' !! q = Some rq).
{ intros q rq Hq [K|NE]; apply drop_keep; auto. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by (intros; reflexivity).
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; cbn -[drop_region g_remove frontier region_live_range round_up_pg Z.mul Z.pow Z.add].
+ intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_ids q rq Hq).
+ intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_shape q rq Hq).
+ intros q1 q2 r1 r2 H1 H2 NE. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_disj q1 q2 r1 r2 H1 H2 NE).
+ exact ir_resv.
+
apply g_remove_perm with (l := r_len r).
* eapply Permutation_trans; [exact ir_groups|].
eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
cbn. rewrite Hk. cbn. apply perm_skip. unfold st', drop_region. cbn. apply Permutation_refl.
* intros y Hy. apply in_map_iff in Hy as ([q rq] & <- & Hq). apply filter_In in Hq as [Hq Hkq]. cbn in Hkq |- *.
apply elem_of_list_In in Hq || apply list_elem_of_In in Hq. apply elem_of_map_to_list in Hq.
unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
destruct (r_kind rq) eqn:Ek; try discriminate.
intros E. pose proof (ir_disj q rid rq r Hq Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ek, Hk in D.
pose proof (ir_shape _ _ Hq) as (S1 & _ & S3 & _). pose proof (ir_shape _ _ Hr) as (T1 & _ & T3 & _).
pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). lia.
+ eapply Permutation_trans; [exact ir_metas|].
eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
cbn. rewrite Hk. cbn. unfold st', drop_region. cbn. apply Permutation_refl.
+ intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_metalen q rq Hq K).
+ intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_brkfront q rq Hq K).
+ destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
right. exists q, rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
+ intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
* split; [apply KEEP; [exact Hq| left; congruence]| auto].
* apply drop_some in Hq as [Hq _]. auto.
+ intros q1 q2 r1 r2 H1 H2. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_brk1 q1 q2 r1 r2 H1 H2).
+ revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
* destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (NB q rq Hq).
* exact IBK.
* destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
+ destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
+ intros q Hq. cbn in Hq. discriminate.
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite FR. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply KEEP; [exact Hrq| left; destruct K; congruence]| exact K].
- apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
* intros q rq Hq K E. apply KEEP; [exact Hq|]. right. intros ->. specialize (NOG b E). rewrite NOG in Hb. discriminate.
* apply (group_ok_X X); [reflexivity|]. eapply G1. exact Hb.
+ exact G2.
+ exact G3.
+ intros q rq Hq K _. apply drop_some in Hq as [Hq NE]. apply (G4 q rq Hq K). rewrite HO. congruence.
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [| exact K]. apply KEEP; [exact Hq|]. right. intros E. specialize (NOG b E). rewrite NOG in Hb. discriminate.
- apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
- assert (GS : forall q, q <> rid -> get_shadow st' q = get_shadow st q).
{ intros q NE. unfold get_shadow, st', drop_region. cbn. rewrite lookup_delete_ne by congruence. reflexivity. }
assert (KN : forall q o v, q <> rid -> known st (q, o) v -> known st' (q, o) v).
{ intros q o v NE K. unfold known, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
assert (UN : forall q o, q <> rid -> unknown st (q, o) -> unknown st' (q, o)).
{ intros q o NE K. unfold unknown, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
assert (HNE : forall b m, hosts st b m -> fst b <> rid).
{ intros b m [ai Hb] E. specialize (NOG b E). rewrite NOG in Hb. discriminate. }
destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor.
+ intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply drop_keep; auto| exact K].
+ intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq]. eapply D2. exact Hq.
+ intros b m i Hb Hi. apply KN; [exact (HNE b m Hb)|]. apply (D3 b m i Hb Hi).
+ intros b m o Hb Ho. apply UN; [exact (HNE b m Hb)|]. apply (D4 b m o Hb Ho).
+ intros b m p i Hb Hml Hs. destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
pose proof (HNE b m Hb) as NE.
split; [exists v3; split; [apply KN; [exact NE| exact K3]| auto]|]. split; [apply KN; [exact NE| exact K2]|]. split; [apply KN; [exact NE| exact K1]| exact Q].
+ intros k m i Hkk Hs. destruct (D6 k m i Hkk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (NE : fst (bslot k) <> rid).
{ destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Ek). rewrite Ek. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). exact (HNE b m Hb). }
split; [apply KN; [exact NE| exact A1]|]. split; [apply KN; [exact NE| exact A2]|]. split; [apply KN; [exact NE| exact A3]|]. split; [apply KN; [exact NE| exact A4]|].
split; [exact A5|]. split.
* intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try (apply KN; [exact NE| assumption]). exact B6.
* split; [intros Hres; apply KN; [exact NE| apply A7; exact Hres]|]. intros a Ha. apply UN; [exact NE| apply A8; exact Ha].
Qed.
End DROP.
Lemma In_perm_map {A B} (f : A -> B) l l' x : Permutation l (map f l') -> In x l' -> In (f x) l.
Proof. intros P Hx. eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_map. exact Hx. Qed.
Lemma group_region_in_ledger : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "QG'Q0'Q>'L'@'QE'Q1vHr5r4r3%544321'='7%119&S1'S6&S:&S2%34?21>&S8%14A43@&QH%11?%96DC53>1(1r2%22F1%@3>41'QF&QC%11E(Q6%E3421&QL':'A%2211(9&Q?%11O&QD%11Q1%547731&Kr6%211%=3:41p0?1p0E1p0Q71pUDQ>1pUHQ@1pQ8QB1pUNQD1pTDQF1").
Proof. intros X st L rid r.
intros IR Hr Hk. pose proof (ir_groups _ _ _ IR) as P.
apply (In_perm_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ (rid, r) P).
apply filter_In. split; [| rewrite Hk; reflexivity]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hr.
Qed.
Lemma brk_quiet_of : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "?'Q0'Q>'L'Q1vHr3r2r1%544321&I%114p031pQ8:1pUN<1pTD>1").
Proof. intros X st L.
intros IR. pose proof (ir_brk _ _ _ IR) as B. unfold brk_quiet.
destruct (c_brk (s_ctx st)); [destruct B as [-> _]| rewrite B| destruct B as [-> _]]; exact I.
Qed.
Section FREE.
Hypothesis NTF : NTF_SPEC.
Section SE.
Local Abbreviation SEC_T_free_INVL := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WFree2 "QM'Q>'L'6&O%211'Q=&Q9%511p031&Q;'A&MvH&Q3r7r6r5r4%76654321&QL':%12<;%221<(9r3%24@?81r2%446A21%9361=&Q5r8&Q<r9(1&Q8&R5&Q7%221D%42F1%62Q11%9281'>&Nr:%22>1r1%Q36Q2Q1DF21qQ>Q71%72Q81qV0QA1qQ:QA1%F5Q7QCE;1p0H1p0Q31pU:Q<1pU>Q=1pTJQ?1pQ<QA1p2QF1pQ8QJ1pUNQL1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 0%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 1%nat 0%nat).
Variable BL : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 2%nat 0%nat).
Variable LS : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 3%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 4%nat 0%nat).
Variable off : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_free_INVL) 6%nat 0%nat).
Theorem free_INVL : ltac:(sec_stmt2 constr:(SEC_T_free_INVL) 7%nat 0%nat).
Proof.
intros INV Hk.
destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
unfold free. rewrite (free_hdr_eq st c off n m bm i ai a ar ka BF). cbn [sbind].
set (p := aadd c (UNIT * off)).
set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _].
assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
{ change c with (bslot ((c, off), n)) at 1 2.
apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
- intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ; unfold UNIT, IB in *; lia.
- subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Hkr); exists r; auto).
assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
- subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
unfold free_tail.
assert (MR1' : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; reflexivity).
assert (MR1 : forall x, get_meta_rec st1 x = get_meta_rec st x) by exact MR1'.
rewrite !MR1.
pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st m); rewrite NA, NF; reflexivity).
fold (MR st m).
destruct (negb ((m_freed (MR st m) =? 0) || (Z.lor (m_freed (MR st m)) (m_avail (MR st m)) + bit i =? mask_upto (m_last_idx (MR st m))))) eqn:BR.
-
cbn [ftree ret]. exists LS.
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
assert (Efun : upd_meta m (m_set_freed (m_freed (MR st m) + bit i)) st1
= upd_meta m (fun r => m_set_avail (m_avail (MR st m)) (m_set_freed (m_freed (MR st m) + bit i) r)) st1).
{ unfold upd_meta. f_equal. all: rewrite <- (MR1 m); fold (MR st1 m); destruct (MR st1 m); reflexivity. }
rewrite Efun.
assert (Hfr : m_freed (MR st m) <> 0).
{ intros E. rewrite E in BR. cbn in BR. discriminate. }
apply (INVL_mask_change (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm ai (m_avail (MR st m)) (m_freed (MR st m) + bit i) None INV1).
+ exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
+ rewrite !MR1'. rewrite bit_eq. unfold tbit.
split; [exact M1|]. split; [pose proof (Z.pow_nonneg 2 i); lia|]. split; [exact M3|]. split; [| split].
* intros j Hj. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [apply M4; auto| apply Z.eqb_eq in H; lia].
* intros j Hj Ha. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
* pose proof (bf_ai _ _ _ _ _ _ _ _ _ _ _ BF) as AI. intros j Hj. rewrite testbit_add_bit by (auto; lia). unfold tbit in M6. rewrite (M6 j Hj). reflexivity.
+
intros j Hj. rewrite !MR1'. cbn zeta.
destruct INV1 as (_ & _ & _ & _ & _ & IS1 & _).
pose proof (is_part _ _ _ IS1 bm m ai j (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) ltac:(rewrite MR1'; exact Hj)) as P1.
rewrite !MR1' in P1. cbn zeta in P1. cbn [x_pend xpend] in P1.
unfold tbit in *. rewrite bit_eq. rewrite testbit_add_bit by (auto; lia).
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) in P1 |- *.
assert (N5 : ~ (@None aptr = Some (fst bm, sstart (MR st m) j))) by discriminate.
destruct (Z.eqb_spec i j) as [<-|NE].
* rewrite <- Ec in P1 |- *. rewrite NF, Bool.orb_false_l || rewrite Bool.orb_true_r.
unfold one5 in P1 |- *. rewrite NF in P1.
clear - P1. revert P1.
generalize (Z.testbit (m_avail (MR st m)) i = true) as A.
generalize (In c (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! c <> None) as Hh.
generalize (@eq (option aptr) (Some c) (Some c)) as P5 || idtac.
intros. assert (FF : ~ (false = true)) by discriminate. assert (N5 : forall x : aptr, ~ (@None aptr = Some x)) by discriminate.
pose proof (N5 c). pose proof (@eq_refl (option aptr) (Some c)). tauto.
* rewrite Bool.orb_false_r.
assert (NS : ~ (Some c = Some (fst bm, sstart (MR st m) j))).
{ intros E. apply NE. assert (E2 : slot_start' (MR st m) i = slot_start' (MR st m) j).
{ rewrite !(slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). rewrite <- Ec. congruence. }
exact (proj2 (slot_key_inj _ _ _ IS _ _ _ _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) Hi Hj E2)). }
unfold one5 in P1 |- *.
clear - P1 NS N5. revert P1 NS N5.
generalize (Z.testbit (m_avail (MR st m)) j = true) as A. generalize (Z.testbit (m_freed (MR st m)) j = true) as F.
generalize (In (fst bm, sstart (MR st m) j) (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! (fst bm, sstart (MR st m) j) <> None) as Hh.
intros. tauto.
+ right. split.
* intros s Hs'. cbn in Hs'. inversion Hs'. subst s. exists i. rewrite !MR1'. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). exact Ec.
* intros s Hs'. discriminate.
+ intros _ sc Hin Hnh. split; [| pose proof (Z.pow_nonneg 2 i); rewrite bit_eq; lia]. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
+ intros _ Hsc NI. exfalso. apply Hfr. rewrite MR1' in Hsc. exact (proj2 (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NI)).
+ intros _ Hsc Hst. exfalso. apply Hfr. rewrite MR1' in Hsc, Hst. exact (proj2 (g_under _ _ _ _ _ _ GO ltac:(discriminate) Hsc Hst)).
-
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
assert (Hsc0 : 0 <= m_sizeclass (MR st m)).
{ pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as [[? _]|(E63 & _)]; lia. }
destruct (NTF mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
(fun st2 mi => match mi with
| Some (base, len) => if negb (len =? 0)
then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
else ret st2
| None => ret st2 end) (ret st1) INV1)
as (st' & mi & LS' & EQ & POST).
+ apply (hosts_ext st st1); [reflexivity|]. exists ai. exact Hb.
+ rewrite MR1'. exact Hi.
+ cbn [x_pend xpend]. rewrite MR1', Ec. reflexivity.
+ reflexivity.
+ reflexivity.
+ unfold FUEL. lia.
+ rewrite MR1'. unfold FUEL. lia.
+ rewrite EQ. destruct mi as [[base len]|].
* destruct POST as (r & Hb0 & Hr & Hkr & Hlen & Hpos & INV').
destruct (Z.eqb_spec len 0) as [|NZ]; [lia|]. cbn [negb].
pose proof INV' as (IR' & _).
cbn [ftree]. split.
-- split; [exact (brk_quiet_of _ _ _ IR')|]. exists (r_len r). split; [| right; exact Hlen].
rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r. exact (group_region_in_ledger _ _ _ _ _ IR' Hr Hkr).
-- intros z. cbn [answer_ok]. destruct (munmap_answer_ok z); [| exact I].
cbn [ftree ret]. exists LS'. rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r.
apply (INVL_drop_orph (xorph (xpend (xpend x0 (Some c)) None) (Some (fst base))) st' L (bl_remove c BL) LS' (fst base) r INV' eq_refl Hr).
* cbn [ftree ret]. exists LS'. exact POST.
Qed.
End SE.
End FREE.
End CEIL_WRAP_1.
