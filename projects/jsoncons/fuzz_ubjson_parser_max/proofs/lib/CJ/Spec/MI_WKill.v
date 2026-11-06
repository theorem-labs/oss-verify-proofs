(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WKill () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WKill.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WKill.CEIL_WRAP_1.KILL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1Some"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3map"]; ["4N"; "4Z"; "0L"; "0LS"; "0P"; "0RUNp"; "5INVL"; "5MR"; "5blk"; "5bslot"; "5frontier"; "5gbase"; "5gcnt"; "5gend"; "5group_ok"; "5hosts"]; ["5live_group"; "5sstart"; "5x_pend"; "5zsum"; "7gslot"; "6gterm"; "8RKGroup"; "8UNIT"; "8aptr"; "8area"; "8brkstate"; "8c_active"; "8c_avail_meta"; "8c_avail_meta_area_count"; "8c_avail_meta_areas"; "8c_avail_meta_count"]; ["8c_bounces"; "8c_brk"; "8c_free_meta_head"; "8c_init_done"; "8c_meta_alloc_shift"; "8c_meta_area_head"; "8c_meta_area_tail"; "8c_mmap_counter"; "8c_secret"; "8c_seq"; "8c_unmap_seq"; "8c_usage"; "8cptr"; "8get_head"; "8get_stride"; "8ghdr"]; ["8lhead"; "8m_last_idx"; "8m_maplen"; "8m_sizeclass"; "8mctx"; "8meta"; "8mstate"; "8optr"; "8r_kind"; "8r_len"; "8region"; "8rkind"; "8round_up_pg"; "8s_areas"; "8s_ctx"; "8s_groups"]; ["8s_metas"; "8s_next_rid"; "8s_regions"; "8s_reserved"; "8s_secret"; "8s_shadow"; "8s_slots"; "8s_tick"; "8set_usage_map"; "8shadow"; "8size_class"; "8slot_start'"; "8usage"; "9In"; ":Permutation"; ";add"]; [";le"; ";lt"; ";mul"; "0U"; "0X"; "0X'"; "0ai"; "0b"; "0bpm"; "0c"; "0g"; "0h"; "0i"; "0ip"; "0j"; "0l"]; ["0l'"; "0m"; "0p"; "0pm"; "0r"; "0rid"; "0s"; "0sc"; "0sc'"; "0st"; "0st'"; "0st1"; "<delete"; "<lookup"; "=N_countable"; "=Z_countable"]; ["=prod_countable"; ">prod_eq_dec"; "?map_delete"; "?map_to_list"; "@gmap"; "@gmap_fold"; "@gmap_lookup"; "@gmap_partial_alter"; "Aeq_dec"; "Beq_dec"; "0v"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma zsum_perm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "@'4'A%211'RNr2r1%33521':&Q3r3%211%317%53;21p071pW2<1pW0=1").
Proof. intros l l'. induction 1; unfold zsum in *; cbn in *; lia. Qed.
Lemma round_up_ge_k : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "7'A&S0r1&R<%112%4231pXH61").
Proof. intros x. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.
Definition gterm (st : mstate) (sc : Z) (bh : aptr * ghdr) : Z :=
match g_meta (snd bh) with
| Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0
| None => 0
end.
Lemma gcnt_unfold : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q5'R6'A':&Lr2r1%3221&Q3&?'7&Q8'QO%3221&Q5%12:9&T3'T4&T1'@&T8&T9%4432D1&T0&SN&SO%36762H51%:4@51?&T5%14B73A&R?%11J%@5ED531%H4DOB1%J11%Q03Q1L1pW@Q21pWDQ41").
Proof. intros st sc. reflexivity. Qed.
Lemma gcnt_delete : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "R2'R6&Q8'QO'A':'5%114&SM'T4&T1'@&T8&T9%4432:1&T0&SN&SO%36762>51%:4A51@&T6%14C73Br3&R?r5%211%B6HG7541(2r2%22J1%I3G41&SL&T2&T7%14Q0D@O%34Q1Q0@1r4r6%?11%85Q5D431%Q33E?1'R5%Q14Q8LH1&R@%117r7%311%Q:3531&Lr8%221>&RO&Q5(6%14QDQCAN%336C1%82;D%6221%QE3QF81p0<1p0D1p0O1pW@QJ1pVHQL1pW6QN1pWFR01pWDR11").
Proof. intros st st' p h sc.
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
Lemma g_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "5&OvSIvSBvS:%43321"). Proof. exists ai. exact Hg. Qed.
Lemma GO : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "8'NvS4vSIvCvS:vSBvS6%76654321"). Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
Lemma stride_pos : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "9&S1z&QN&GvSIvS:%3221%511%8271").
Proof. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [H _]. unfold UNIT in H. lia. Qed.
Lemma gbase_p : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ":':&Q8&K&GvSIvS:%3221%511vSB%93821"). Proof. exact (hosts_gbase _ _ _ IM _ _ g_hosts). Qed.
Lemma slot_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "L'A':&Q8&RK&GvSIvS:%3221r1%6221(6'@&3vSB%233>1&RO&8%136A4&Q7%4221&S2&QN%11?%321?%9251%?4>I;1%I3HA1pVNK1").
Proof. intros j. rewrite slot_start'_sstart. unfold sstart. rewrite gbase_p. reflexivity. Qed.
Lemma sstart_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "G'A':&Q1&GvSIvS:%3221r1%6221&RO&8'@vSB%332=1&Q7%6221&S2&QN%11<%321<%;251%D3E=1pVNF1").
Proof. intros j. unfold sstart. rewrite gbase_p. reflexivity. Qed.
Lemma K_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "E':'T4&Q8&T1'@&T8'A&T9%544321&T0&SN&SO%36872651'R5%=4<621&R@vSJ%211vSI%411%D3631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_MR : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ";&Q8':'R5&GvSJr1%3221vSI%5213%83731pXH:1"). Proof. intros x. unfold MR, get_meta_rec. rewrite K_metas. reflexivity. Qed.
Lemma K_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "=':'T4'@&T8&SN'R:%544321&RBvSJ%211vSI%411%<3631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "=':'T4'@&T8&SN'RI%544321&REvSJ%211vSI%411%<3631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "E':'T4&Q8&T1'@&T8'A&T9%544321&T0&SN&SO%36872651'Q9%=4<621&R=vSJ%211vSI%411%D3631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "8':'@&RGvSJ%211vSI%411%73631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "8':'@&RAvSJ%211vSI%411%73631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "8':'A&RDvSJ%211vSI%411%73631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_reserved : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "<':'4'7'A%2211%411&RCvSJ%211vSI%411%;3631"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "L':'T4&Q8&T1'@&T8'A&T9%544321&T0&SN&SO%36872651'QO%=4<621&R?vSJ%211&SL&T2&T7%14C=98%34D981vSBvSI%:11%85H<431%K3=:1"). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "8':'R4&R>vSJ%211vSK%411%73631"). Proof. reflexivity. Qed.
Lemma K_c : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "L'R4!p021'T4'A&T9&SO%443213r3r2%211r4&RH%1245%311p051pV891pVDA1&R>vSI%211%<11vSJ%511%@11p041p091pQ:I1").
Proof. intros P. intros HPU H0. rewrite K_ctx. destruct S1 as [U ->]. cbn. apply HPU. exact H0. Qed.
Lemma K_cf : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "S6'9':'A&QH&R>vSJ%211%411vSI%511%711%:3941&QC%117%215%>3=21&QG%11;%219%B3A21&R7&QB%11@%21>%G3421&Q<%11D%21B%K3821&Q?%11H%21F%O3N21&Q=%11L%21J%Q33Q221&QD%11Q0%21N%Q73Q621&QE%11Q4%21Q2%Q;3H21&QF%11Q8%21Q6%Q?3L21&Q>%11Q<%21Q:%QC3Q021'T4&T9&SO&Q8%44QG321&Q;%11QE%21QC%QL3421%94QL87QL&QJ%11QJ%21QH%R13421&Q@%11QN%21QL%R53821&QI%11R2%21R0%R93R821'Q:&QA%11R7%21R5%R>3421&QK%11R;vSK%R?11%411%RD3G41%RF271%RG2=1%RH2B1%RI2G1%RJ2M1%RK2Q71%RL2Q<1%RM2QA1%RN2QF1%RO2QK1%S02R01%S12R51%S22R:1%S32R@1%S42RE1%S52RJ1").
Proof. destruct S1 as [U E]. rewrite K_ctx, E. cbn. repeat split; reflexivity. Qed.
Lemma K_usage : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ":'A':&RLvSJr1%3221vSK%5213%73831pWB91").
Proof. intros sc'. reflexivity. Qed.
Lemma K_get_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ";'R0':&R7&QMvSJr1%3221vSI%5213%83731pVH:1").
Proof. intros h. destruct S1 as [U ->]. destruct h; reflexivity. Qed.
Lemma K_frontier : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ">'@'R:':'A&JvSJr2r1%43321vSI%63143%93831pW:;1pW<=1").
Proof. intros rid r. unfold frontier. rewrite K_ctx. destruct S1 as [U ->]. reflexivity. Qed.
Definition gslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = slot_start' (MR st g) j.
Lemma K_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q;&Q8'>'9':'5'7'A%2271%411&SM'T4&T1'@&T8&T9%443291&T0&SN&SO%36762=51%:4D51=&T6%14F73?r1&RFvSJ%211%B6KD7541vSI%511%E6NG:871%L3G41&=&Q4%11;%311%Q2251(1%11O%Q43O<1%Q6216%Q8251pW>Q:1").
Proof. intros s.
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
Lemma K_slots_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q5&Q8&=&Q4r1%211%411':'5'7'A%22:1%411&SM'T4&T1'@&T8&T9%443291&T0&SN&SO%36762=51%:4G51=&T6%14I73?r2&RFvSJ%211%B6ND7541vSI%511%E6Q1G:871%L3G41p0N1pW>Q41").
Proof. intros s. intros NG. destruct (K_slots s) as [[E _]|[_ G]]; [exact E| tauto]. Qed.
Lemma K_slots_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q2&Q8&Q4r1%211':'5'7'A%2281%411&SM'T4&T1'@&T8&T9%443291&T0&SN&SO%36762=51%:4E51=&T6%14G73?r2&RFvSJ%211%B6LD7541(1%11F%K3F31p0M1pW>Q11").
Proof. intros s. intros G. destruct (K_slots s) as [[_ NG]|[E _]]; [tauto| exact E]. Qed.
Lemma K_slots_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q=&Q8'7'A%2231':'5%113&SM'T4&T1'@&T8&T9%4432;1&T0&SN&SO%36762?51%:4B51?&T6%14D73Ar2&RFvSJ%211%B6IF7541(2r1%22I1%I3G41'9r3vSI%;11%K6Q2O@>31%92Q0>%Q03N21&=&Q4%118%311%;251p0=1pXFQ81pW>Q<1").
Proof. intros s v. intros H. destruct (K_slots s) as [[E NG]|[E G]]; [rewrite <- E; auto| congruence]. Qed.
Lemma none_of {A} (o : option A) : (o <> None -> False) -> o = None.
Proof. destruct o; [intros H; exfalso; apply H; discriminate| reflexivity]. Qed.
Section SE.
Local Abbreviation SEC_T_g_slot_free := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "R:'A'9&S0zr1%3221&R1&GvSIvS:%3221%511%:281%<281&=&RM'7'@%221B(6&3vSB%235F1&Q1r2%22?1%749J41&?&H&QL&Iv0%544321%B3?71%D11':'5'QO%211&SM'T4&Q8&T1&T8&T9%34L2Q=1&T0&SN&SO%36Q062QA51%:4951=&T6%14;73?&R?%11Q>%@6Q5B53M1(1%11D%G3D31%G1B&Q2vS4%211(2%12Q>Q6%N3631r3vS<%Q13R421p041%R52<1%R62Q51p0QK1pVNR91")) (only parsing).
Variable j : ltac:(sec_ty2 constr:(SEC_T_g_slot_free) 0%nat 0%nat).
Lemma g_slot_free : ltac:(sec_stmt2 constr:(SEC_T_g_slot_free) 1%nat 0%nat).
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
End SE.
Lemma g_slot_free' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "QG'A'9&S0zr1%3221&R1&GvSIvS:%3221%511%:281%<281&=&RM&Q8&RKr2%2291&?&H&QL&Iv0%544321%;3:71%=11':'5'QO%211&SM'T4&T1'@&T8&T9%4432Q61&T0&SN&SO%36762Q:51%:4K51=&T6%14M73?&R?%11Q7%@6Q0B53M1(1%11D%G3D31%QC2I1p0Q81pVNQF1").
Proof. intros j. intros Hj. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). destruct (g_slot_free j Hj) as (A & B & _). auto. Qed.
Lemma gslot_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "L&Q8&Q4r1%211';'A'9&S0z%2217&R1&GvSIvS:%3221%511%92>1%;281':r3&RK%127C%43F31%A261qVNC1%E2D1p0G1pW>K1").
Proof. intros s. intros (j & Hj & E). exists j. unfold cnt in Hj. split; [lia| exact E]. Qed.
Lemma other_slot_not_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q5&Q8'A&OvSIr2r3%43321&=':r4vS:%33;21%511'9&S0z%221;&R1&Gr5%22A1%411%82A1%:271&Q4&RKr6%92H1%321C%511%G11p081p0D1p0K1pVNQ11pV@Q31pW4Q41").
Proof. intros m b j.
intros Hm NE Hj G. destruct (gslot_range _ G) as (j' & Hj' & E).
destruct (slot_key_inj _ _ _ IS _ _ _ _ _ _ Hm g_hosts Hj Hj' E) as [Em _]. exact (NE Em).
Qed.
Lemma entry_not_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q>&Q8'A':'5'7%1254%311&SM'T4&T1'@&T8&T9%4432<1&T0&SN&SO%36762@51%:4B51=&T6%14D73?r3&RFvSI%211%B6ID7541(2(6r2r1%34NM21%52J1%N3J71&=vS:%Q13Q3>1%311&Q4r5%211%711p051p0:1pVNQ:1pW4Q<1pW>Q=1").
Proof. intros s m j.
intros Hs NE. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). exact (other_slot_not_g m b j Hb NE Hj).
Qed.
Lemma entry_g_gslot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q7&Q8'A':'5'7%1254%311&SM'T4&T1'@&T8&T9%4432<1&T0&SN&SO%36762@51%:4B51=&T6%14D73?r2&RFvSI%211%B6ID7541(2(6vS:r1%34NM21%52J1%N3J71&Q4r3%211p041pVNQ41pW>Q61").
Proof. intros s j.
intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hj & ->). exists j. unfold cnt. split; [lia| reflexivity].
Qed.
Lemma hosts_K : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "C&Q8&<&OvSJr2r1%43321'9vSI%73154&=':vSB%23=91%411%8261%?2:1pW4A1pV@B1").
Proof. intros b m.
unfold hosts. rewrite K_groups. split.
- intros [a H]. apply lookup_delete_Some in H as [NE H]. split; [exists a; exact H| congruence].
- intros [[a H] NE]. exists a. rewrite lookup_delete_ne by congruence. exact H.
Qed.
Lemma hosts_K_neq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ">&Q8&OvSJr2r1%43321&=':vS:%23961%411p061pW4<1pV@=1").
Proof. intros b m. intros H. apply hosts_K in H as [H NE]. intros ->. exact (NE (hosts_inj _ _ _ IM _ _ _ H g_hosts)). Qed.
Lemma live_K : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "A&Q8&Q0vSIr1%3221&=':r2vS:%33921%511vSJr3%<221p041p0;1pW4@1").
Proof. intros m.
intros [b Hb] NE. exists b. apply hosts_K. split; [exact Hb|]. intros ->. exact (NE (hosts_fun _ _ _ _ Hb g_hosts)).
Qed.
Lemma g_unlisted_K : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill ";'R0&=&RM&Q8vS:vCr1%211%63541%811pVH:1").
Proof. intros h. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h). Qed.
Lemma p_not_gslot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "5&=&Q4vSB%211%411").
Proof.
intros (j & Hj & E). rewrite slot_g in E. pose proof stride_pos.
assert (snd p = snd p + UNIT + get_stride (MR st g) * j) by (rewrite E at 1; reflexivity). unfold UNIT in *. nia.
Qed.
Lemma slots_pos : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "Q<'7'@'A%3221&Q8':'5%7235%211&SM'T4&T1&T8&T9%34=2<1&T0&SN&SO%36A62@51%94?51<&T6%14A73>r3&RFvSI%211%A6GC7541(2(6r2r1%34KM21%52I1%L3I71&S1z&8r4%23Q5Q41%5241p071pVNQ71pW4Q61pW>Q81").
Proof. intros s m j.
intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn.
pose proof (sstart0 _ _ _ IM _ _ Hb). pose proof (sstart_mono _ _ _ IG _ _ 0 j Hb ltac:(lia)).
destruct (hosts_ok _ _ _ IG _ _ Hb) as (a & _ & GOm). pose proof (g_align _ _ _ _ _ _ GOm) as [A _]. unfold UNIT in *. lia.
Qed.
Lemma top_region_empty : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "QE'7'@'A%3221'QO&=':&R2&GvSIvS:%3221%511z%83<21%:11'5%11=&SM'T4&Q8&T1&T8&T9%34G2F1&T0&SN&SO%36K62J51%:4951I&T6%14;73Kr3&R?%11I%A6Q0O6431(2r2%22Q21%Q13F41&3r4%23Q9Q81vSB%43Q;Q:1%Q73Q<31r5%Q93Q<14p031p0:1p0Q31pVHQ?1pV@QA1").
Proof. intros b h.
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
Lemma gcnt_K sc' : gcnt st sc' = (if sc =? sc' then cnt else 0) + gcnt st' sc'.
Proof.
rewrite (gcnt_delete st st' p _ sc' Hg K_groups K_metas). unfold gterm. cbn. fold sc. fold cnt. reflexivity.
Qed.
Theorem INVL_kill : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "8&FvEvS5vSJvBv0vC%76654321").
Proof.
pose proof GO as GOg. pose proof g_hosts as Hgh.
assert (NGm : forall b m, hosts st b m -> m <> g -> b <> p).
{ intros b m Hm NE ->. exact (NE (hosts_fun _ _ _ _ Hm g_hosts)). }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; rewrite ?K_regions, ?K_next_rid, ?K_reserved; try assumption.
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
- destruct K_cf as (cf1 & cf2 & cf3 & cf4 & cf5 & cf6 & cf7 & cf8 & cf9 & cf10 & cf11 & cf12 & cf13 & cf14 & cf15 & cf16 & cf17).
destruct IA; constructor; rewrite ?K_regions, ?K_areas, ?K_secret, ?K_metas, ?cf1, ?cf2, ?cf3, ?cf4, ?cf5, ?cf6, ?cf7, ?cf8, ?cf9, ?cf10, ?cf11, ?cf12, ?cf13, ?cf14, ?cf15, ?cf16, ?cf17; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite K_frontier. auto.
+ intros sc' Hsc'. rewrite K_usage, (U1 sc' Hsc').
pose proof (gcnt_K sc') as GK. rewrite <- (ia_usage sc' Hsc') in GK. rewrite Z.eqb_sym in GK.
destruct (Z.eqb_spec sc' sc) as [E|NE]; [rewrite <- E; lia| lia].
- destruct IM as [M1 M2 M3 M4 M5] eqn:EIM; constructor; rewrite ?K_MR.
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
- destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9] eqn:EIL; constructor; try assumption.
+ intros h. rewrite K_get_head. apply L1.
+ intros h. apply (dll_ext_metas st st' K_metas). apply L2.
+ intros m. rewrite !K_MR. apply L5.
+ intros m Hm. rewrite !K_MR. apply L6. exact Hm.
+ intros sc0 m Hm. destruct (L7 sc0 m Hm) as (A1 & A2 & A3). rewrite K_MR. split; [exact A1|]. split; [| exact A3].
apply live_K; [exact A2|]. intros ->. exact (g_unlisted_K _ Hm).
- destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
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
- destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
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
- destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
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
Lemma kill_top : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "QM&=':'A&R2&GvSIvS:%3221%511z%93821%;11';'R:'9&8'@vSB%332@1%B3A1:'5%118&SM'T4&T8&SN%34:21=&T6%14<43?&3%13>L=&RBvSJ%211%<6BE8641(2r1%22H1%Q53A41'R;&R8%115(Q6%Q:3421&S2+TP0%22Q61&R<&R9%11=%311%QB3QA51&S1%12Q<7%Q8231%Q92<1%Q:2B1%Q;2Q61qW:Q=1%Q?2Q>1p0QA1").
Proof.
intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r & Hr & Hk & E & _). exists r. rewrite K_regions.
pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _). pose proof (round_up_ge_k (r_len r)). repeat split; auto. lia.
Qed.
Lemma kill_nested : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WKill "S0':'A&R2&GvSIvS:%3221%511z%93821';&Q8'9'5'7%124>%311&SM'T4&T1'@&T8&T9%4432F1&T0&SN&SO%36762J51%:4A51=&T6%14C73?vSB&RFvSJ%211%B6HD7541(2(6r3r2%34MQ721%52J1%Q:3J71&Or1%23<17&3%13KQ>3%23LQ?A%QA3M21&S0%12Q;<&R1%QB2QA?%211%52@1%Q<251&Q1%125C%F4Q7QJ<1%QL3QAM1&S1&R3%11QI%21;%4221+Q@%6231%QH231&QN%11A&S2&Q7&RJ%11:%4231%R<3R;61&M%11R8&RO%12F:%O231%R6261%R72?1%R82H1%R92M1%R:2Q51%R;2Q:1%R<2Q>1qVBR>1%R@2R?1qVLRJ1%RB2RK1qW8RB1%RD2RC1p0RF1").
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
Lemma dec_hdr_eq {T} (k : aptr -> Z -> M T) bail :
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
Lemma fg_st1 X st L BL LS g p ai (INV : INVL X st L BL LS) (Hg : s_groups st !! p = Some (mkGhdr (Some g) ai)) :
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
End CEIL_WRAP_1.
