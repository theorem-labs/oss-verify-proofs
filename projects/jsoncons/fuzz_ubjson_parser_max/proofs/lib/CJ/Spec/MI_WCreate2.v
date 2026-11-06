(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_WGroup MI_WCreate MI_Cnt MI_TF2.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WCreate2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Cnt."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Ext."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_TF2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WCreate2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WGroup."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0A"; "0B"; "0BL"; "1None"; "1Some"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2False"; "2and"; "2eq"; "2not"]; ["2or"; "3N"; "3Z"; "0E"; "0L"; "0LS"; "0P"; "0RUNp"; "4zrange"; "5ctrl_eq"; "6INVL"; "6MR"; "6hosts"; "6known"; "6one5"; "7TF0"]; ["7TF2"; "7TW"; "8F63"; "8agG"; "8hdr3_f"; "9nl_list"; "9wrs"; ":Known"; ":UNIT"; ":aadd"; ":active"; ":aptr"; ":area"; ":c_usage"; ":cell_read"; ":cellval"]; [":get_head"; ":get_meta_rec"; ":get_stride"; ":ghdr"; ":hdr_havoc"; ":lhead"; ":m_set_maplen"; ":mask_upto"; ":mctx"; ":meta"; ":meta0"; ":mkGhdr"; ":mkMeta"; ":mstate"; ":optr"; ":put_group"]; [":region"; ":round_up_pg"; ":s_areas"; ":s_ctx"; ":s_groups"; ":s_metas"; ":s_next_rid"; ":s_regions"; ":s_reserved"; ":s_secret"; ":s_shadow"; ":s_tick"; ":set_metas"; ":set_usage"; ":set_usage_map"; ":shadow"]; [":shadow0"; ":size_class"; ":upd_meta"; ":usage"; ";forallb"; "<add"; "<div"; "<land"; "<le"; "<lor"; "<lt"; "<modulo"; "<mul"; "<pow"; "<shiftr"; "<sub"]; ["0X"; "0X'"; "0ai"; "0bg"; "0cnt"; "0g"; "0h"; "0i"; "0idx"; "0j"; "0k"; "0m"; "0ml"; "0mr'"; "0needed"; "0o"]; ["0p"; "0rid"; "0sc"; "0sc0"; "0size"; "0st"; "0st'"; "0st1"; "0st2"; "0st3"; "0st4"; "0st5"; "0st6"; "=insert"; "=lookup"; ">N_countable"]; [">Z_countable"; ">prod_countable"; "?prod_eq_dec"; "@map_insert"; "Agmap"; "Agmap_lookup"; "Agmap_partial_alter"; "Beq_dec"; "Ceq_dec"; "0stride"; "0v"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma land31_id : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "@'B'=&RHzr1%3221+O%5231%7231'>&RGr2%2216%43=12p061pXH?1").
Proof. intros x. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma land63_id : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "@'B'=&RHzr1%3221+QO%5231%7231'>&RGr2%2216%43=12p061pXH?1").
Proof. intros x. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma land52_id : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "G'B'=&RHzr1%3221&RJ&RM+2+QD%3221%5271%;271'>&RGr2&RO+1%2281%5241%73D15p091pXHF1").
Proof. intros x. intros. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma one5_A : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "@!r3&?%112&Nr6r5'<r4%5543221p071p081p0;1pQ8=1p4>1p2?1").
Proof. intros A B E. intros. unfold one5. tauto. Qed.
#[using="Type"] Lemma one5_B : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "@!&?r3%211&Nr6r5'<r4%5543221p071p091p091pQ8=1p4>1p2?1").
Proof. intros A B E. intros. unfold one5. tauto. Qed.
#[using="Type"] Lemma one5_E : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "@!&?r3%211&Nr6r5'<r4%5543221p081p081p091pQ8=1p4>1p2?1").
Proof. intros A B E. intros. unfold one5. tauto. Qed.
#[using="Type"] Lemma cell_read_shadow0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "<'B'>'Q?&Q>&R@r1%3221(Q7z%211%93841pW0;1").
Proof. intros o. unfold cell_read. cbn. rewrite !lookup_empty. reflexivity. Qed.
#[using="Type"] Lemma known_noshadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "Q0'QM'A'B'>'7'R?%211&SN'T4&T7&SO%34:216&T5%14<438r2&R:r3%211%;6A=7541(3%11?%B3?31&Mr4(8%14HG9;z%53421p071pW0K1pW4M1pW<O1").
Proof. intros st rid o. intros H. unfold known, SHd, get_shadow. cbn. rewrite H. cbn. apply cell_read_shadow0. Qed.
Definition agG (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
(m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).
Definition agt (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
let st0 := hdr_havoc p st in
let st1 := set_usage sc (usage st0 sc + cnt) st0 in
let st2 := upd_meta m (agG sc p cnt ai) st1 in
let st3 := put_group p (Some m) ai st2 in
add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.
#[using="Type"] Lemma ag_tail_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
ag_tail full_lay st sc m p cnt ai k = k (agt st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.
Section AGT.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
Let mr' := agG sc p cnt ai (MR st m).
#[using="Type"] Lemma agt_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "M'>'T4&Q;&T2'A&T7'B&T8%544321&T1&SO&T0%36872651'QI%=4<621&R5vSF%211&SM&T3&T6%14C=98%34D981vS;vS=vSE%;11%97I>=5431%L3>;1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_MR_m : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'QI&KvSFvS;%3221vS=%73621").
Proof. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_eq. reflexivity. Qed.
#[using="mr'"] Lemma agt_MR_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "A&Q;&?'>r1vS;%33521%511'QI&KvSFr2%3221vSE%5213%<3731p091pXH@1").
Proof. intros x. intros NE. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma agt_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "Q5'>'T4&Q;&T2'A&T7'B&T8%544321&T1&SO&T0%36872651'QC%=4<621&R4vSF%211&SM&T3&T6%14C=98%34D981vS@(QK(4vS;%22I1&RGvS2+O%3221%8251vSE%C11%A7Q1FE=<31%Q43FC1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_rec3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "M'>'QI&QA&QOvS@(4&Q;vS;%3221vS2&RB&Q3vSBvS4%342:15&R=&RE&RC&QDvSE%22@1%4219%6219%83;13%>3A:1%F4EA@1%H21CvS=%L3K21").
Proof. unfold get_meta_rec. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma agt_slots s : 0 <= cnt -> 0 < get_stride mr' ->
s_slots st' !! s =
if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod get_stride mr' =? 0) && ((snd s - snd p - UNIT) / get_stride mr' <? cnt)
then Some (m, (snd s - snd p - UNIT) / get_stride mr') else s_slots st !! s.
Proof. intros Hc Hs. unfold st', agt. cbn zeta. rewrite agt_rec3. rewrite lookup_add_slots by assumption. reflexivity. Qed.
#[using="Type"] Lemma agt_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "@'>'T4'A&T7&SO'R?%544321&R:vSF%211&QDvS@vSE%3221%711%?3961"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "='>'T4'A&T7&SO'R0%544321&R7vSF%211vSE%411%<3631"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "E'>'T4&Q;&T2'A&T7'B&T8%544321&T1&SO&T0%36872651'Q<%=4<621&R2vSF%211vSE%411%D3631"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'A&R6vSF%211vSE%411%73631"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'A&R;vSF%211vSE%411%73631"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'B&R9vSF%211vSE%411%73631"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_reserved : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "<'>'6'9'B%2211%411&R8vSF%211vSE%411%;3631"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "M'>'QH&R3vSF%211&R>&SM'B'T4&T8&T0%344214&T3&T6%147547%348841vSB&RE&RCvSE%2214vS4%5221&Q=%F15%211%D7CC?;:41%F213%L3KH1"). Proof. reflexivity. Qed.
#[using="Type"] Lemma agt_usage sc0 : usage st' sc0 = usage st sc0 + (if sc0 =? sc then cnt else 0).
Proof.
unfold usage at 1. unfold ctx. rewrite agt_ctx. cbn -[usage]. destruct (Z.eqb_spec sc0 sc) as [->|NE].
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. unfold usage, ctx. lia.
Qed.
#[using="Type"] Lemma agt_active : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 ";'B'>&QN&Q:vSFr1%3221vSE%5213%83731pW8:1"). Proof. intros sc0. reflexivity. Qed.
#[using="Type"] Lemma agt_get_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 ";'QE'>&QN&Q@vSFr1%3221vSE%5213%83731pV>:1"). Proof. intros h. destruct h; reflexivity. Qed.
#[using="Type"] Lemma agt_TF0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "6&OvSE%211vSF%411p031").
Proof. intros H. apply (TF0_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. exact H. Qed.
#[using="Type"] Lemma agt_TW : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "<&Q;!p021&Q1vSEr1%3221vSFr2%6221p041pQ>91").
Proof. intros P. intros H. apply (TW_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TW_hdr_havoc. exact H. Qed.
End AGT.
Section AG_TOP.
Variables (idle0 : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (r : region) (sc cnt needed ai : Z).
Let X := mkX (m :: idle0) [] None (Some rid) None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st2 L BL LS.
Hypothesis Hr : s_regions st2 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st2 !! rid = None.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hai : 0 <= ai <= cnt - 1.
Hypothesis Hai0 : sc = 0 -> ai = cnt - 1.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF0 st2.
Hypothesis NIm : ~ In m idle0.
Let p : aptr := (rid, 0).
Let ml := Z.shiftr needed 12.
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let st3 := upd_ctx MC st2.
Let st4 := upd_meta m (m_set_maplen ml) st3.
Let st' := agt st4 sc m p cnt ai.
Let mr' := agG sc p cnt ai (m_set_maplen ml meta0).
Let IM := proj1 (proj2 (proj2 INV)).
#[using="RUNp idle0 L BL LS rid X INV IM"] Lemma top_MRm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'QI&KvSHvS;%3221&QJ%73621").
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
#[using="INV"] Lemma top_INV3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8&JvGvS0vSIvDv2vE%76654321").
Proof. exact (INVL_mmap_counter X st2 L BL LS INV). Qed.
#[using="RUNp idle0 L BL LS rid X INV IM"] Lemma top_MR4 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 ";'>'QI&KvSJvS;%3221&QFvS<&QJ%3221%:3951").
Proof. unfold st4, MR. rewrite get_meta_rec_upd_same. f_equal. exact top_MRm. Qed.
#[using="GRP Hsc"] Lemma top_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "RK'B&RL&Q8&RAvSB%211%5241&QBvS=%211'=&RH+1vS4%3221+Q0%5231%7231'>vS<&RFvS>+TP0%3221%63H51%>2=6+X0%@281%B231&REr1%N21B%32N1%Q02>;%G221'@r2%J271+L%L21Q3%5231&RO%12MNz%J3Q<21+K%Q321Q:p031&RJ&RM+2+D%3221%52F1+@%Q<21I&RK%12K3%Q83QJ1?&R1%11Q7%Q;3QML1%>2CQ9'QI(QL(3&Q;%211(4vS@%2241&QGvS2%211%31Q0%Q2212%<999631Q2R0R8QI%QK3>R51%R42@1%R52B1%R62F1%R72J1%R82M1%R92Q41%R:2Q<1%R;2QC1%R<2QJ1%R=2QO1%R>2R71tXDRIR@1tW:RJRD1").
Proof.
unfold ml in *. pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
assert (Emr : mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml).
{ unfold mr', agG; cbv beta iota delta [m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_set_prev m_set_next m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]; cbn.
rewrite land31_id by lia. rewrite land63_id by lia. rewrite land52_id by lia. reflexivity. }
assert (Es : get_stride mr' = (if (cnt - 1 =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else UNIT * size_class sc)).
{ rewrite Emr. unfold get_stride. cbn. reflexivity. }
cbn zeta. unfold ml in *.
assert (RU : needed / 4096 * 4096 = round_up_pg needed).
{ destruct (round_up_pg_spec needed) as [A B]. pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite G2 in H.
pose proof (Z.div_mod (round_up_pg needed) 4096 ltac:(lia)). rewrite B in H0. nia. }
rewrite Es. repeat split; try assumption; try lia.
Qed.
#[using="r X INV Hr Kr Lr NS GRP Hsc Hai Hai0 EMP TF NIm IM"] Theorem ag_top_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "R8'=&JvGvS1vSFvDv2vE%76654321&O%116'>'QI&KvS;%22;1vS=%63521'7'QC%211&SN&Q;'T4&T2'A&T7'B&T8%544321&T1&SO&T0%36872651%;4<51?&T5%14>73AvS@&R4%11Q3%C6BE6431(4(QK%22EMvS2%3221%52K1%Q43K71&QN&Q:r1%22Q?1vSH%4213%Q;3631pW8L1'QE&Q@%12QF8%2279%QA3<21pV>51&R;%11QK%21<%QF3Q821%R2251%R32<1%R42E1%R52QD1%R62QL1%R72QO1").
Proof.
pose proof top_facts as TFX. cbn zeta in TFX. destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
pose proof top_INV3 as INV3. pose proof INV3 as (IR & IA & IM3 & IL & IG & IS & ISH).
assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite top_MR4; reflexivity).
pose proof (created_masks ai (cnt - 1) Hai ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
assert (Sp : get_stride mr' > 0) by lia.
assert (INV' : INVL X' st' L BL LS).
{ apply (INVL_create X X' st3 st' L BL LS m p ai mr' INV3 ltac:(left; reflexivity)).
all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- lia.
- lia.
- lia.
- exact Hai0.
- left. lia.
- unfold tbit. repeat split; try lia; assumption.
- intros _. rewrite <- Emr. repeat split; lia.
- rewrite <- Emr. lia.
- cbn. unfold UNIT. split; [lia| reflexivity].
- left. reflexivity.
- reflexivity.
- intros x Hx. cbn in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
- reflexivity.
- reflexivity.
- intros i Hi. unfold tbit. cbn [x_pend X'].
destruct (Z.le_gt_cases i ai).
+ apply one5_A; [apply M7; lia| intros Hf; exact (M5 i ltac:(lia) (M7 i ltac:(lia)) Hf)| discriminate].
+ apply one5_B; [intros Ha; pose proof (M3 i ltac:(lia) Ha); lia| apply M6; lia| discriminate].
- intros s Hs. discriminate.
- intros _. exact EMP.
- left. rewrite <- Emr. cbn [snd fst x_orph x_pend X X' p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. replace (m_maplen mr') with ml by (rewrite Emr; reflexivity).
split; [exact F10|]. unfold cnt_of. replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity). lia.
- intros i Hi. apply known_noshadow. exact NS.
- intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
- unfold st'. rewrite agt_metas. unfold st4. rewrite s_metas_upd_meta. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
+ rewrite !lookup_insert_eq. f_equal. fold st4. first [rewrite top_MR4; exact Emr| unfold mr'; f_equal; exact top_MR4].
+ rewrite !lookup_insert_ne by congruence. reflexivity.
- unfold st'. rewrite agt_groups. rewrite land31_id by lia. reflexivity.
- intros s. unfold st'. rewrite (agt_slots st4 sc m p cnt ai s); [| lia| rewrite top_MR4; fold mr'; lia].
rewrite top_MR4. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn. repeat split; reflexivity.
- pose proof (ia_ctx _ IA) as (C & _). exact C.
- intros sc0 Hsc0. unfold st'. rewrite agt_usage. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
- intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx in Hv. cbn in Hv.
destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. exact (ia_usage_keys _ IA sc0 v Hv). }
split; [exact INV'|]. split.
{ unfold st'. apply agt_TF0. apply (TF0_ctrl st2); [reflexivity| reflexivity| exact TF]. }
split; [exact MR'm|]. split; [unfold st'; rewrite agt_groups, lookup_insert_eq, land31_id by lia; reflexivity|].
split; [intros; reflexivity|]. split; [intros h; destruct h; reflexivity| reflexivity].
Qed.
End AG_TOP.
#[using="Type"] Lemma set_metas_id : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "L'QM'T4&Q;&T2'A&T7'B&T8%544321&T1&SO&T0%36872651'QI%=4<621'>r1&R5r2%211%53641&R<r3%2251%93H12p051pXF<1pW<K1").
Proof. intros st v. destruct st; cbn; intros ->; reflexivity. Qed.
Definition hdr3_f (i : Z) : bool := (Z.land (Z.lor (Z.land i 31) 192) 255 =? i + 192) && (Z.land (i + 192) 31 =? i).
#[using="Type"] Lemma hdr3_all : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "<'>'5&RD'B&Q4&Hz+Q0%3221%73651(;%;3:21"). Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma hdr3_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "J'B'=&RHzr1%3221+O%5231%7231'>&RG&RIr2%3217+V0%4221+WO%7221&RE%1275%;3D31%;22?%=3F1:%F231p0@1pV@I1").
Proof. intros i.
intros Hi. pose proof (forallb_zrange hdr3_f 0 32 i hdr3_all ltac:(lia) ltac:(lia)) as H. unfold hdr3_f in H.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.
Section AG_NESTED.
Variables (idle0 : list aptr) (st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m g bg : aptr) (aig idx sc cnt : Z).
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Let p : aptr := (fst bg, sstart (MR st1 g) idx).
Let X := mkX (m :: idle0) [] (Some p) None None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st1 L BL LS.
Hypothesis Hg : s_groups st1 !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st1 g).
Hypothesis SCg : m_sizeclass (MR st1 g) = j.
Hypothesis STR : get_stride (MR st1 g) = UNIT * size_class j.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF2 st1.
Hypothesis NIm : ~ In m idle0.
Let st2 := nest_layout st1 g idx j size cnt.
Let st3 := upd_meta m (m_set_maplen 0) st2.
Let st' := agt st3 sc m p cnt (cnt - 1).
Let mr' := agG sc p cnt (cnt - 1) meta0.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
#[using="RUNp idle0 L BL LS g bg idx p X INV IM"] Lemma nst_MRm : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'QI&KvSGvS;%3221&QJ%73621").
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
#[using="aig Hg"] Lemma nst_hosts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "5&LvSGvS3vS5%43321"). Proof. exists aig. exact Hg. Qed.
#[using="NEST Hsc"] Lemma nst_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "R3'=&RH+2vS4%3221+Q0%5231%7231&RJvSBvS9%3221+G%<231%>231&RE&Q8&RLvSD%22@1%5241&RA%11<%6271%G241%827F&RM+D%22J1%E241+@%N21='>'B&RK%12A5z%53421+SO%Q62A1'QIvS=(QL(3&Q;%211(4vS@%2241&QG&RO+1%22QA1%411%<99961B23Q=B%G3?>1&QB%11@%J3I1Q8%QK241%QL2E1%QM2H1%QN2O1%QO2Q21%R02Q81%R12QC1%R22QK1").
Proof.
pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0.
destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof (size_class_bound sc Hsc) as SB.
assert (Emr : mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0).
{ unfold mr', agG; cbv beta iota delta [m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_set_prev m_set_next m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]; cbn.
rewrite land31_id by lia. rewrite land63_id by lia. rewrite Z.sub_diag. reflexivity. }
assert (SJ : size_class j <= 127) by (change 127 with (size_class 23); apply size_class_le; lia).
repeat split; try lia.
- unfold size, UNIT. lia.
- unfold size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
- exact Emr.
- rewrite Emr. unfold get_stride. cbn -[Z.eqb size_class Z.mul]. replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
#[using="aig INV Hg Hidx STR NEST Hsc TF mr'"] Lemma nst_layout : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "RH'=&JvGvS0vSHvDv2vE%76654321'IvSG%2217'>'A&R;%11;%216%53421&M&Q9vS@-3%3221&RG&RIvS8+O%4221+V0%5221+WO%8221%>3L:1-2%?2>1&RF&RO&:'B%23J1C&REvS3%53M41&Q8%4221%9261%;213%H21A%N3Q<>1+1%O2@1&RN+8%2271%O21H%Q53QC51&RHzr1%3221vS4%5231%QN231&RLr2vSD%3221%K2H1+4%Q1221%QC2QB1%QE3R31>p0:1pVFQ31'QM&Q6&Q5vS5%26R41Q5QE=B%421R5%R436R<1%RA281%RB2K1%RC2Q31%RD2QD1%RE2R41%RF2R;1%RG2R?1").
Proof.
pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _).
pose proof (nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
(TF2_TF X st1 L BL LS INV TF)) as (A & _ & C & D & E & F & G & H & _).
refine (conj A (conj C (conj D (conj E (conj F (conj G (conj H _))))))). apply (nl_eq X st1 L BL LS g bg aig idx j size cnt INV Hg STR).
Qed.
#[using="RUNp idle0 L BL LS bg aig p X INV Hg Hidx STR NEST Hsc TF mr' IM"] Lemma nst_st3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "5'>'QMvSIvSH%43321").
Proof.
pose proof nst_layout as (INV2 & CE & _).
unfold st3, upd_meta, put_meta. apply set_metas_id.
assert (E : get_meta_rec st2 m = meta0) by (rewrite (get_meta_rec_ext st1 st2 m (ce_metas _ _ CE)); exact nst_MRm).
rewrite E. change (m_set_maplen 0 meta0) with meta0. apply insert_id. rewrite (ce_metas _ _ CE). exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))).
Qed.
#[using="aig X INV Hg Hidx SCg STR NEST Hsc EMP TF NIm IM"] Theorem ag_nested_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "R;'=&JvGvS1vSFvDv2vE%76654321&Q0%116'>'QI&KvS;%22;1vS=%63521'7'QC%211&SN&Q;'T4&T2'A&T7'B&T8%544321&T1&SO&T0%36872651%;4<51?&T5%14>73AvS@&R4%11Q3%C6BE6431(4(QK%22EM&ROvS4+1%3221%6251%82N1%Q73N:1&QN&Q:r1%22QB1vSG%4213%Q>3631pW8O1'QE&Q@%12QI8%2279%QD3<21pV>51&R;%11QN%21<%QI3Q;21%R5251%R62<1%R72E1%R82QG1%R92QO1%R:2R21").
Proof.
pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & Emr & Es).
pose proof nst_layout as (INV2 & CE & TK2 & K3 & K2 & K1 & KZ & Ewrs).
pose proof INV as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
pose proof INV2 as (IR & IA & IM2 & IL & IG2 & IS2 & ISH).
pose proof nst_st3 as E3.
assert (MR2 : forall x, MR st2 x = MR st1 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE)).
assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite E3, MR2, nst_MRm; reflexivity).
pose proof (created_masks (cnt - 1) (cnt - 1) ltac:(lia) ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
rewrite Z.sub_diag in *.
pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg)) as LI31.
pose proof (hdr3_facts idx ltac:(lia)) as [H3a H3b].
pose proof (sstart_res X st1 L BL LS INV bg g idx nst_hosts) as PR. fold p in PR.
assert (P16 : snd p mod 16 = 0).
{ unfold p. cbn [snd]. unfold IB in PR. pose proof (Z.div_mod (sstart (MR st1 g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st1 g) idx) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (sstart (MR st1 g) idx) 16 ltac:(lia)). lia. }
pose proof (hosts_gbase _ _ _ IM1 _ _ nst_hosts) as GB.
assert (S0 : sstart (MR st1 g) idx = snd bg + UNIT + get_stride (MR st1 g) * idx) by (unfold sstart; rewrite GB; reflexivity).
assert (Q : (snd p - snd bg - UNIT) / UNIT = size_class j * idx).
{ unfold p. cbn [snd]. rewrite S0, STR. unfold UNIT. replace (snd bg + 16 + 16 * size_class j * idx - snd bg - 16) with ((size_class j * idx) * 16) by lia. apply Z.div_mul. lia. }
assert (Qr : 0 <= size_class j * idx < 2 ^ 16).
{ pose proof (size_class_bound j ltac:(clear - N2 Hsc; lia)) as SB.
destruct (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia)) as (_ & _ & LT).
rewrite STR in LT. unfold cnt_of in LT. clear - SB LT Hidx. unfold UNIT in LT. nia. }
assert (NH : s_groups st1 !! p = None).
{ pose proof (is_part _ _ _ IS1 _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite (slot_start'_eq _ _ _ IM1 _ _ _ nst_hosts) in P5. fold p in P5.
destruct (s_groups st1 !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
assert (INV' : INVL X' st' L BL LS).
{ apply (INVL_create X X' st2 st' L BL LS m p (cnt - 1) mr' INV2 ltac:(left; reflexivity)).
all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- lia.
- lia.
- lia.
- intros _. reflexivity.
- left. lia.
- unfold tbit. repeat split; try lia; try assumption; try (intros i Hi Hb; rewrite Z.bits_0 in Hb; discriminate).
- intros _. rewrite <- Emr, Es. unfold size. clear - N1 N4. repeat split; lia.
- rewrite <- Emr, Es. lia.
- unfold UNIT. split; [| exact P16]. unfold p. cbn [snd]. pose proof (sstart0 _ _ _ IM1 _ _ nst_hosts). pose proof (sstart_mono _ _ _ IG1 _ _ 0 idx nst_hosts ltac:(lia)).
destruct (hosts_ok _ _ _ IG1 _ _ nst_hosts) as (a0 & _ & GO). pose proof (g_align _ _ _ _ _ _ GO). unfold UNIT in *. lia.
- left. reflexivity.
- reflexivity.
- intros x Hx. cbn [x_idle X X'] in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
- reflexivity.
- reflexivity.
- intros i Hi. unfold tbit. cbn [x_pend X']. apply one5_A; [apply M7; lia| rewrite Z.bits_0; discriminate| discriminate].
- intros s Hs. discriminate.
- intros _. exact EMP.
- right. rewrite <- Emr. cbn [x_pend x_orph X X']. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists g, idx, bg. rewrite !MR2.
split; [rewrite (ce_slots _ _ CE); unfold p; rewrite <- (slot_start'_eq _ _ _ IM1 _ _ idx nst_hosts); exact (is_total _ _ _ IS1 _ _ _ nst_hosts Hidx)|].
split; [apply (proj2 (hosts_ext st1 st2 (ce_groups _ _ CE) bg g)); exact nst_hosts|].
split; [reflexivity|]. split; [exact Hidx|]. split; [reflexivity|].
split; [rewrite Es; unfold p; cbn [snd]; rewrite STR; unfold cnt_of; replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity); unfold size in N3 |- *; lia|].
split; [rewrite SCg; replace (m_sizeclass mr') with sc by (rewrite Emr; reflexivity); lia|].
split; [rewrite STR, SCg; reflexivity|].
split; [exists (idx + 192); split; [| split; [exact H3b| clear - Hidx LI31; lia]]; rewrite <- H3a; exact K3|].
rewrite Q. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. rewrite <- Q.
replace (snd p - snd bg - UNIT) with (snd p - (snd bg + UNIT)) by lia.
split; [exact K2|]. split; [replace (fst p, snd p - 1) with (aadd (aadd p (-2)) 1) by (unfold aadd; cbn [fst snd]; f_equal; lia); exact K1|].
replace ((snd p - (snd bg + UNIT)) / UNIT) with (size_class j * idx) by (rewrite <- Q; f_equal; lia). exact Qr.
- rewrite <- Emr. intros i Hi. rewrite Es. replace (fst p, snd p + UNIT + size * i - IB) with (aadd p (UNIT + i * size - 4)) by (unfold aadd, IB; f_equal; lia).
apply KZ. unfold cnt_of in Hi. rewrite ?Emr in Hi. cbn [m_last_idx] in Hi. lia.
- intros o v tk Ho Hc. rewrite Ewrs in Hc. rewrite wrs_cells_other in Hc.
+ rewrite TK2. exact (TF2_ghdr_old X st1 L BL LS INV p TF P16 o v tk Ho Hc).
+ unfold nl_list. rewrite map_app. intros Hin. apply in_app_iff in Hin. unfold p in Ho. cbn [snd] in Ho. destruct Hin as [Hin|Hin].
* cbn [map fst In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold aadd in E; cbn [fst snd] in E; clear - E Ho N1 N5; lia.
* apply in_zlist in Hin as (k & Hk & E). apply (f_equal snd) in E. unfold aadd in E. cbn [fst snd] in E. unfold UNIT in E.
assert (0 <= k * size) by (apply Z.mul_nonneg_nonneg; clear - Hk N5; lia). clear - E Ho H Hk N5. lia.
- unfold st'. rewrite agt_metas. rewrite E3. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
+ rewrite !lookup_insert_eq. f_equal. rewrite MR2, nst_MRm. first [exact Emr| reflexivity].
+ rewrite !lookup_insert_ne by congruence. reflexivity.
- unfold st'. rewrite agt_groups, E3. rewrite land31_id by lia. reflexivity.
- intros s. unfold st'. rewrite (agt_slots st3 sc m p cnt (cnt - 1) s); [| lia| rewrite E3, MR2, nst_MRm; fold mr'; rewrite Es; lia].
rewrite E3, MR2, nst_MRm. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
- unfold st'. rewrite agt_shadow, E3. reflexivity.
- unfold st'. rewrite agt_regions, E3. reflexivity.
- unfold st'. rewrite agt_areas, E3. reflexivity.
- unfold st'. rewrite agt_next_rid, E3. reflexivity.
- unfold st'. rewrite agt_tick, E3. reflexivity.
- unfold st'. rewrite agt_secret, E3. reflexivity.
- unfold st'. rewrite agt_reserved, E3. reflexivity.
- unfold st'. rewrite agt_ctx, E3. repeat split; reflexivity.
- unfold st'. rewrite agt_ctx, E3. cbn [c_mmap_counter set_usage_map]. rewrite (ce_ctx _ _ CE). pose proof (ia_ctx _ IA1) as (C & _). exact C.
- intros sc0 Hsc0. unfold st'. rewrite agt_usage, E3. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
- intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx, E3 in Hv. cbn [c_usage set_usage_map] in Hv.
destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. rewrite (ce_ctx _ _ CE) in Hv. exact (ia_usage_keys _ IA1 sc0 v Hv). }
split; [exact INV'|]. split.
{
unfold TF2. unfold st'. rewrite E3.
apply (TW_mono _ (fun q => PS st1 q \/ In q (map fst (nl_list st1 g bg idx size cnt)))).
2:{ apply agt_TW. rewrite Ewrs. apply TW_wrs; [| intros q Hq; right; exact Hq]. apply (TW_mono _ (PS st1)); [intros q Hq; left; exact Hq| exact TF]. }
intros q [Hq|Hq].
- apply (PS_mono st1); [| exact Hq]. apply geom_kept_of.
+ intros b h Hb. rewrite <- E3. fold st'. unfold st'. rewrite agt_groups, E3, (ce_groups _ _ CE).
rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite NH in Hb. discriminate.
+ intros b x Hx. rewrite <- E3. fold st'. rewrite (agt_MR_other st3 sc m p cnt (cnt - 1) x), E3, MR2; [reflexivity|].
intros ->. exact (idle_not_live _ _ _ _ _ INV m ltac:(left; reflexivity) (ex_intro _ b Hx)).
- assert (Hm' : hosts (agt st2 sc m p cnt (cnt - 1)) p m) by (exists (Z.land (cnt - 1) 31); rewrite agt_groups, lookup_insert_eq; reflexivity).
assert (R' : MR (agt st2 sc m p cnt (cnt - 1)) m = mr') by (rewrite <- E3; exact MR'm).
exists p, m. split; [exact Hm'|]. rewrite R'.
unfold nl_list in Hq. rewrite map_app in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
+ cbn [map fst In app] in Hq. assert (E : fst q = fst p /\ snd p - 3 <= snd q <= snd p - 1).
{ destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst q; unfold aadd, p; cbn [fst snd]; split; first [reflexivity| lia]. }
destruct E as [E1 E2]. split; [symmetry; exact E1|]. right. split; [rewrite Emr; reflexivity| exact E2].
+ apply in_zlist in Hq as (k & Hk & ->). unfold aadd. cbn [fst snd]. split; [reflexivity|]. left. exists k.
split; [unfold cnt_of; rewrite Emr; cbn [m_last_idx]; clear - Hk; lia|].
unfold sstart. replace (gbase mr') with p by (rewrite Emr; reflexivity). rewrite Es. unfold p. cbn [snd]. unfold sstart, UNIT, IB. lia. }
split; [exact MR'm|].
split; [unfold st'; rewrite agt_groups, E3, lookup_insert_eq, land31_id by lia; reflexivity|].
split; [intros sc0; unfold st'; rewrite agt_active, E3; unfold active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
split; [intros h; unfold st'; rewrite agt_get_head, E3; unfold get_head, active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
unfold st'. rewrite agt_tick, E3. exact TK2.
Qed.
End AG_NESTED.
#[using="Type"] Lemma round_up_pg_div : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "D'B&RJzr1%3221'>&RL&RF&REr2+SoO%3221+TP0%6221%8212&R1%117%<3A31p0>1pXHC1").
Proof. intros x.
intros Hx. destruct (round_up_pg_spec x) as [A B].
pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as M1.
pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D2. rewrite B in D2. nia.
Qed.
Definition F63 (rid : N) (ml : Z) (mr : meta) : meta :=
m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))).
Section CREATE63.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (r : region) (needed : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.
Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).
#[using="RUNp L BL LS rid X INV IM"] Lemma c63_MRg : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'QI&KvSIvS5%3221&QJ%73621").
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))). reflexivity. Qed.
#[using="Hn"] Lemma c63_ml : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "F'=&RH+1vS<%3221&RJ&RM+2+QD%3221%5271%;271'>'B&RL+TP0%22=1&R1vS>%211%83741%E2:1").
Proof.
unfold ml. split; [| apply round_up_pg_div; lia].
split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.
#[using="Hn"] Lemma c63_F : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "9'>'QI&Q2vSAvS<&QJ%43321vS=%83721").
Proof.
pose proof c63_ml as [M _]. unfold F63, mr'; cbv beta iota delta [m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_set_prev m_set_next m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]; cbn.
rewrite land52_id by lia. reflexivity.
Qed.
#[using="Hn"] Lemma c63_stride : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "='>'B&QBvS=%211&RO&RLvS<+TP0%3221&Q8%6221%<3;81").
Proof. pose proof c63_ml as [M _]. unfold get_stride, mr'. cbn -[Z.mul Z.sub Z.eqb]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.
#[using="RUNp L BL LS g X INV IR"] Lemma c63_nogroup : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "L'>'7'QC%211&SN&Q;'T4&T2'A&T7'B&T8%544321&T1&SO&T0%36872651%;4<51?&T5%14>73AvS@&R4vSI%211%D6CF7541(3%11H%K3H31").
Proof. destruct (ir_orph _ _ _ IR rid eq_refl) as (r0 & _ & _ & NG). apply NG. reflexivity. Qed.
#[using="RUNp L BL LS X INV Hn IM"] Lemma c63_rec5 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "8'>'QI&QAvSKvS5%3221vS=%73621").
Proof. unfold get_meta_rec. cbn -[F63 get_meta_rec]. rewrite lookup_insert_eq. fold (MR st3 g). rewrite c63_MRg. exact c63_F. Qed.
#[using="r X INV Hr Kr Lr NS Hn TF IR IM"] Theorem create63_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WCreate2 "RF'=&JvGvS1vSLvDv2vE%76654321&O%116'>'QI&KvS5%22;1vS=%63521'7'QC%211&SN&Q;'T4&T2'A&T7'B&T8%544321&T1&SO&T0%36872651%;4<51?&T5%14>73AvS@&R4%11Q3%C6BE6431(4(QK%22EMz%3221%52K1%Q43K71'QH&R3%11Q>vSI%311%Q:3531&R;%11QC%215%Q>3Q021'R0%Q44Q2Q1L1&R7%11QI%21;%QD3421&QB%11QA&RO&RLvS<+TP0%3221&Q8%6221%QN3Q>81&R1vS>%211%R23QB71%R>251%R?2@1%R@2G1%RA2L1%RB2Q31%RC2R21%RD2R:1%RE2R=1").
Proof.
pose proof c63_ml as [M RU]. pose proof c63_stride as Es.
pose proof INV as (IR0 & IA & IM0 & IL & IG & IS & ISH).
assert (Emetas : s_metas st6 = <[g := mr']> (s_metas st3)).
{ change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g). rewrite c63_MRg, c63_F. reflexivity. }
assert (MR'g : MR st6 g = mr') by (unfold MR, get_meta_rec; rewrite Emetas, lookup_insert_eq; reflexivity).
assert (GAI : group_active_idx st4 p = 0).
{ unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite c63_nogroup. reflexivity. }
assert (Egroups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3)).
{ change (s_groups st6) with (s_groups st5). unfold st5. rewrite GAI. reflexivity. }
assert (INV' : INVL X' st6 L BL LS).
{ apply (INVL_create X X' st3 st6 L BL LS g p 0 mr' INV ltac:(left; reflexivity)).
all: cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed mr'].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- lia.
- lia.
- lia.
- intros _. reflexivity.
- right. lia.
- unfold tbit. repeat split; try lia; intros i Hi Hb; rewrite Z.testbit_0_l in Hb; discriminate.
- lia.
- fold mr'. rewrite Es. unfold UNIT. split; [lia|]. replace (ml * 4096 - 16) with ((ml * 256 - 1) * 16) by lia. apply Z_mod_mult.
- cbn. unfold UNIT. split; [lia| reflexivity].
- right. split; reflexivity.
- reflexivity.
- intros x Hx. destruct Hx.
- reflexivity.
- reflexivity.
- intros i Hi. unfold tbit. cbn [x_pend X' fst snd p]. apply one5_E; [rewrite Z.testbit_0_l; discriminate| rewrite Z.testbit_0_l; discriminate|].
assert (i = 0) by lia. subst i. rewrite Z.mul_0_r. reflexivity.
- intros s Hs. cbn [x_pend X'] in Hs. inversion Hs. subst s. exists 0. split; [lia|]. cbn [fst snd p]. rewrite Z.mul_0_r. reflexivity.
- intros H. lia.
- left. cbn [x_orph x_pend X X' fst snd p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. split; [exact RU|]. fold mr'. rewrite Es. unfold UNIT. lia.
- intros i Hi. apply known_noshadow. exact NS.
- intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn [fst p] in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
- exact Emetas.
- exact Egroups.
- intros s. unfold st6. rewrite c63_rec5. rewrite lookup_add_slots; [| lia| rewrite Es; unfold UNIT; lia]. fold mr'. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- repeat split; reflexivity.
- pose proof (ia_ctx _ IA) as (C & _). exact C.
- intros sc0 Hsc0. replace (sc0 =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r. reflexivity.
- intros sc0 v Hv. exact (ia_usage_keys _ IA sc0 v Hv). }
split; [exact INV'|]. split.
{ apply (TF0_ctrl (hdr_havoc p st4)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. apply (TF0_ctrl st3); [reflexivity| reflexivity| exact TF]. }
split; [exact MR'g|]. split; [rewrite Egroups, lookup_insert_eq; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Es| exact RU].
Qed.
End CREATE63.
End CEIL_WRAP_1.
