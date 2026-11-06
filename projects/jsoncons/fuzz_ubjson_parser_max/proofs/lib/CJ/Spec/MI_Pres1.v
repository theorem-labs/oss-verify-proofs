(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Pres1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0A'"; "0B"; "0BL"; "0C"; "1None"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3N"; "3Z"]; ["0D"; "0E"; "0E'"; "0F'"; "0IS"; "0L"; "0LS"; "0RUNp"; "4INVL"; "4MR"; "4blk"; "4cnt_of"; "4extras"; "4gbase"; "4gend"; "4hosts"]; ["4inv_S"; "4live_group"; "4one5"; "4sstart"; "5aptr"; "5area"; "5get_stride"; "5ghdr"; "5m_avail"; "5m_freeable"; "5m_freed"; "5m_last_idx"; "5m_maplen"; "5m_mem"; "5m_next"; "5m_prev"]; ["5m_sizeclass"; "5mctx"; "5meta"; "5mstate"; "5optr"; "5region"; "5s_areas"; "5s_ctx"; "5s_groups"; "5s_metas"; "5s_regions"; "5s_shadow"; "5s_slots"; "5shadow"; "5slot_start'"; "6le"]; ["0X"; "0X'"; "0b"; "0b1"; "0b2"; "0bb"; "0f"; "0g"; "0i"; "0i1"; "0i2"; "0m"; "0m1"; "0m2"; "0st"; "0st'"]; ["7lookup"; "8N_countable"; "8Z_countable"; "8prod_countable"; "9prod_eq_dec"; ":gmap"; ":gmap_lookup"; ";eq_dec"; "<eq_dec"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma slot_key_inj : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "R0'L'QC'6&J%211'Q0r3r2r1%43321&Q4'?&Or9r6r5%43321r:r4%73241'9&QOz%2215&Q;&Ir;r7%3221%511%92<1%;281r<%821C%:11%>2A1%@2=1':&QNr=%?21K%321K%A23?%521L%73Q231r8%93Q4M1%:3Q4DQ1%L221p051p0>1p0D1p0Q11p0Q51pTFQ;1pTDQ<1pTLQ>1pT:Q?1pTJQ@1pT8QA1pQ:QC1p8QI1pTNQM1pT2QO1").
Proof. intros X st BL IS b1 m1 b2 m2 i1 i2.
intros H1 H2 R1 R2 E.
pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.
Lemma one5_E_irrel : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "G!&Q2r6r5r4r3r2%6554321&<%114r9r8r7%<5321;9p051p061p091pQ6A1pQ4B1pQ2C1p:D1p6E1p2F1").
Proof. intros A B C D E E'.
unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.
Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).
Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').
Hypothesis C_masks : 0 <= A' /\ 0 <= F'
/\ (forall i, 0 <= i -> tbit A' i = true -> i <= ai)
/\ (forall i, 0 <= i -> tbit F' i = true -> i <= m_last_idx (R g))
/\ (forall i, 0 <= i -> tbit A' i = true -> tbit F' i = true -> False)
/\ (forall i, ai < i <= m_last_idx (R g) -> tbit F' i = true).
Hypothesis C_part : forall i, 0 <= i <= m_last_idx (R g) ->
let s := slot_start' (R g) i in
one5 (tbit A' i = true) (tbit F' i = true) (In s (map bslot BL)) (s_groups st !! s <> None) (pend' = Some s).
Hypothesis C_pend : pend' = x_pend X \/
((forall s, x_pend X = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)
/\ (forall s, pend' = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)).
Hypothesis C_rest : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> A' = 0 /\ F' <> 0.
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> get_stride (R g) < UNIT * size_class (m_sizeclass (R g)) -> A' = 0 /\ F' = 0.
Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
Lemma R'_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "A&Q4&<':r1vR7%33521%511'QB&IvR?r2%3221vR>%5213%<3731p091pUD@1").
Proof. intros x. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma R'_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ";':'QB&IvR?vR7%3221vR6vR>%6214%311%:3951").
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
Lemma fR_mem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':&QD&Q=vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_prev : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':&QD&Q?vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':&QD&Q>vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_last : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q;vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_freeable : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q9vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_sc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q@vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_maplen : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q<vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_avail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q8vR6&IvR>vR7%3221%511%711v1%;3:21"). Proof. reflexivity. Qed.
Lemma fR_freed : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q:vR6&IvR>vR7%3221%511%711vC%;3:21"). Proof. reflexivity. Qed.
Lemma fR_stride : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&Q6vR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_gbase : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':&Q4&MvR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_sstart : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">'?':&Q3vR6&IvR>vR7%3221%511r1%8221%9242%;3<21pTB=1"). Proof. intros i. reflexivity. Qed.
Lemma fR_slot_start' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "?'?':&Q4&QNvR6&IvR>vR7%3221%511r1%8221%9242%<3;21pTB>1"). Proof. intros i. reflexivity. Qed.
Lemma fR_gend : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&NvR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma fR_cnt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<':'?&KvR6&IvR>vR7%3221%511%711%813%;3:21"). Proof. reflexivity. Qed.
Lemma R'_mem : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':&QD&Q=&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_prev : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':&QD&Q?&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':&QD&Q>&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_last : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&Q;&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_freeable : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&Q9&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&Q@&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_maplen : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&Q<&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_stride : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&Q6&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gbase : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "=&Q4':&M&IvR?r1%3221%511vR>%6214%811%:3;41pUD<1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_sstart : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "@&Q4'?':&Q3&IvR?r2%3221r1%6221vR>%7215%9214%;3<41pTB=1pUD?1"). Proof. intros x i. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_slot_start' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "@&Q4'?':&QN&IvR?r2%3221r1%6221vR>%7215%9214%;3=41pTB=1pUD?1"). Proof. intros x i. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_gend : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&N&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_cnt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ">&Q4':'?&K&IvR?r1%3221%511vR>%6214%811%;3:41pUD=1"). Proof. intros x. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
Lemma R'_avail_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "D&Q4&<':r1vR7%33521%511'?&Q8&IvR?r2%3221%511vR>%6214%811%?3:41p0<1pUDC1"). Proof. intros x. intros; rewrite R'_other; auto. Qed.
Lemma R'_freed_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "D&Q4&<':r1vR7%33521%511'?&Q:&IvR?r2%3221%511vR>%6214%811%?3:41p0<1pUDC1"). Proof. intros x. intros; rewrite R'_other; auto. Qed.
Lemma st'_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "E':'RE&Q4&RD'>&RG'?&RH%544321&RC&RA&RB%36872651'Q7%=4<621&QHvR?%211vR>%411%D3631"). Proof. reflexivity. Qed.
Lemma st'_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "F':'RE&Q4&RD'>&RG'?&RH%544321&RC&RA&RB%36872651'8%12<8%>4=731&QLvR?%211vR>%411%E3631"). Proof. reflexivity. Qed.
Lemma st'_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "=':'RE'>&RG&RA'QE%544321&QJvR?%211vR>%411%<3631"). Proof. reflexivity. Qed.
Lemma st'_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "8':'QA&QGvR?%211vR>%411%73631"). Proof. reflexivity. Qed.
Lemma st'_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "E':'RE&Q4&RD'>&RG'?&RH%544321&RC&RA&RB%36872651'Q5%=4<621&QFvR?%211vR>%411%D3631"). Proof. reflexivity. Qed.
Lemma st'_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "=':'RE'>&RG&RA'QM%544321&QKvR?%211vR>%411%<3631"). Proof. reflexivity. Qed.
Lemma hosts' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "<&Q4&;&OvR?r2r1%43321vR>%63143%8231pTH:1pT<;1"). Proof. intros bb m. apply hosts_ext. reflexivity. Qed.
Lemma live' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 ":&Q4&;&Q1vR?r1%3221vR>%5213%7231pTH91"). Proof. intros m. apply live_group_ext. reflexivity. Qed.
Lemma keys' : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "Q:&Q4&;&<':'7'QB%211&R@'RE&RD'>&RG'?&RH%544321&RC&RA&RB%36872651%;4C51>&RF%14E73@r1&QIvR?%211%C6JE7541(5%11G%J3G31%L11'=vR>%:11%K6Q2M?=<1%Q03M17%Q211vR7%Q33Q6@1%8231%Q72:1pUDQ91").
Proof. intros x.
unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
split; [auto| intros _; discriminate].
Qed.
Lemma g_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "5&OvR>vR2vR7%43321"). Proof. exists ai. exact Hg. Qed.
Theorem INVL_mask_change : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Pres1 "8&HvGvR1vR?vEv3vF%76654321").
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
assert (Gpres : s_metas st !! g <> None).
{ exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
- destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
+ intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
destruct K as [K| ->].
* destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
* destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
* apply K. apply Hk. exact Hk2.
* apply Gpres. rewrite <- K. apply Hk. exact Hk2.
+ intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
rewrite R'_sc, R'_cnt. reflexivity.
- destruct IM as [M1 M2 M3 M4 M5]; constructor.
+ intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
* exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
* apply M1. exact Hm.
+ intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
+ intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
+ intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
+ intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
- destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
+ intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
+ intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
+ exact L3.
+ exact L4.
+ intros m. rewrite R'_next, R'_prev. apply L5.
+ intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
+ intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
+ exact L9.
- destruct IG as [G1 G2 G3 G4 G5]; constructor.
+ intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
destruct (aptr_eqb_spec m g) as [->|NE].
*
pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
all: try (apply keys'; left; exact g_present).
all: try exact C_masks.
all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
all: try (intros NF Hsc NI; apply C_unlisted; assumption).
all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
all: try (intros NF Hsc Hs; apply C_under; assumption).
all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
all: match goal with |- ?g => idtac "REMAINS-G" g end.
* destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
all: try (apply keys'; left; assumption).
all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
all: match goal with |- ?g => idtac "REMAINS-O" g end.
+ intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
+ intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
+ intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
- destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
+ intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
+ intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
+ intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
* rewrite fR_avail, fR_freed. apply C_part. exact Hi.
*
pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
{ intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
{ intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
+ intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
* apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
* destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
- apply (inv_SH_view st st'); try reflexivity; try assumption.
+ apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.
End CEIL_WRAP_1.
