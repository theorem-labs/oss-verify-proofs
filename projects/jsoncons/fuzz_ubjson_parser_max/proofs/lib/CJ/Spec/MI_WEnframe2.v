(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2 MI_WEnframe.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WEnframe2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Ext."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Pres2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Shadow."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Tree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WEnframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WEnframe2.CEIL_WRAP_1.ENFRAME."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WGroup."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."; "stdpp.option."], [["0BL"; "1None"; "1Some"; "1cons"; "1fst"; "1id"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "3map"; "4N"]; ["4Z"; "0L"; "0LS"; "0Post"; "0RUNp"; "5mled"; "6ctrl_eq"; "7INVL"; "7MR"; "7blk"; "7bslot"; "7gbase"; "7known"; "7unknown"; "8blk_shadow_ok"; "9hl_ticks"]; [":ftree"; ";ef_list"; ";lastw"; "<EL"; "<pp"; "<qv"; "<resv"; "<stf"; "<stw"; "=TKS"; "=wrs"; ">IB"; ">UNIT"; ">aadd"; ">aptr"; ">cell_read"]; [">cellval"; ">cptr"; ">enframe_at"; ">enframe_full"; ">get_meta_rec"; ">get_shadow"; ">get_stride"; ">ghdr"; ">havoc"; ">m_mem"; ">mstate"; ">optr"; ">r_hav"; ">ret"; ">s_groups"; ">s_slots"]; [">s_tick"; ">slot_start'"; "?In"; "@add"; "@div"; "@land"; "@le"; "@lt"; "@modulo"; "@mul"; "@pow"; "@sub"; "0X'"; "0a"; "0bg"; "0c"]; ["0ctr"; "0g"; "0hl"; "0idx"; "0k"; "0n"; "0off"; "0p"; "0r"; "0st"; "0st'"; "0st2"; "Alookup"; "BN_countable"; "BZ_countable"; "Bprod_countable"]; ["Cprod_eq_dec"; "Dgmap"; "Dgmap_lookup"; "Eeq_dec"; "Feq_dec"; "Gfrom_option"; "0stride"; "0u"; "0v"; "0w"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma havoc_le0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "A&Q>'@'QJ&R6r2z%3221'<&QHr4r3%33217%53:18p071pUD<1pU<>1pU@@1").
Proof. intros p n st. intros H. unfold havoc. destruct (Z.leb_spec n 0); [reflexivity| lia]. Qed.
Section ENFRAME.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Hfit : n + IB <= get_stride (MR st g).
Hypothesis TF : TF2 st.
Hypothesis Hres : get_stride (MR st g) - IB - n < 2 ^ 32.
Let X' := xpend X None.
Let stride := get_stride (MR st g).
Let slack := (stride - IB - n) / UNIT.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Lemma ef_gbase : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 ":'<&Q>&K&HvRIvRA%3221%511vR>%93821"). Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
Lemma ef_c : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q0'<&Q>&Q=&S5'9'?'@%3221&5%112(8wz%348721&QI&QDvRIvRA%3221%511%A5==;71&R3&Q<&R9&QF%117vRC%4221%7261%K291vR?%O3N21").
Proof. fold (MR st g). change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. unfold c, sstart, aadd. rewrite ef_gbase. f_equal. lia. Qed.
Lemma ef_slot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 ";'<&Q>&R1&HvRIvRA%3221vRC%6221vR?%:3921"). Proof. exact (slot_start'_eq _ _ _ IM _ _ idx Hg). Qed.
Lemma ef_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q1'<'7'9&Q>'@%3221%511&RL'S1&S0'?&S3&S4%443291&RO&RM&RN%36762=51%:4?51=&S2%14A73?vR?&QOvRI%211%B6FD7541(2(8vRAvRC%34KJ21%52J1%Q03J71"). Proof. rewrite <- ef_slot. exact (is_total _ _ _ IS _ _ _ Hg Hidx). Qed.
Lemma ef_stride : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "<';&R6+@vS6%3221'<'@&R8%1256z%53421%;271").
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma ef_c16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 ";'<'@&R8&:'?vR?%33251+@%6221z%:3921").
Proof.
pose proof (sstart_res X st L BL LS INV bg g idx Hg) as R. unfold c. cbn [snd]. unfold IB in R.
pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.
Lemma ef_NH : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "L'<'7'QG%211&RL&Q>'S1&S0'?&S3'@&S4%544321&RO&RM&RN%36872651%;4<51?&S2%14>73AvR?&QNvRI%211%D6CF7541(1%11H%K3H31").
Proof.
destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.
Lemma ef_NB : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "@&I&R2r1v0%33421&='<&QA&Jr2%211vR?%63521%811p0:1pU:?1").
Proof. intros k.
destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
intros Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk.
Qed.
Lemma ef_q_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q='@';&R6zr1%3221+WO%5231%7231&R3&R9&Q<r2%3221vRE%6221&R;vS6&Q;%3221%B251&R4&:'?vR?%332I1r3%A2@1%C231vR>%837N1%F21D%@241%<21F%Q02O1&R7&R:+2+@%3221%5271%Q8271p0F1p0Q31pU>Q<1").
Proof using INV Hg Hidx HP Hn Hfit Hres. intros off.
intros Ho Hf. destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
pose proof (g_stride _ _ _ _ _ _ GO) as GS. pose proof (g_sc _ _ _ _ _ _ GO) as SC. pose proof (g_li _ _ _ _ _ _ GO) as LI.
unfold c. cbn [snd]. unfold sstart. rewrite ef_gbase. fold stride. pose proof ef_stride as [S16 SM].
replace (snd bg + UNIT + stride * idx + UNIT * off - (snd bg + UNIT)) with ((stride / 16 * idx + off) * 16)
by (unfold UNIT; pose proof (Z.div_mod stride 16 ltac:(lia)) as DM;
assert (E3 : stride * idx = 16 * (stride / 16 * idx)) by (rewrite DM at 1; rewrite SM; ring);
clear - E3; lia).
unfold UNIT. rewrite Z.div_mul by lia.
assert (0 <= stride / 16 * idx) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
split; [lia|].
destruct SC as [[SC1 _]|(SC63 & L0 & _)].
- destruct (GS ltac:(lia)) as (_ & _ & LT). unfold cnt_of in LT. fold stride in LT.
assert (stride * idx <= stride * (m_last_idx (MR st g))) by (apply Z.mul_le_mono_nonneg_l; lia).
pose proof (Z.div_mod stride 16 ltac:(lia)) as DM. unfold IB, UNIT in Hf.
assert (E3 : stride * idx = 16 * (stride / 16 * idx)) by (rewrite DM at 1; rewrite SM; ring).
assert (E4 : stride * m_last_idx (MR st g) = 16 * (stride / 16 * m_last_idx (MR st g))) by (rewrite DM at 1; rewrite SM; ring).
assert (E5 : stride * (m_last_idx (MR st g) + 1) = stride * m_last_idx (MR st g) + stride) by ring.
clear - E3 E4 E5 DM SM LT H0 Hf Hn Ho. lia.
- rewrite L0 in Hidx. assert (idx = 0) by lia. subst idx. rewrite Z.mul_0_r. lia.
Qed.
Definition pp (off : Z) : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition resv (off : Z) : Z := snd ee - snd (pp off) - n.
Definition qv (off : Z) : Z := (snd (pp off) - (snd bg + UNIT)) / UNIT.
Definition EL (off : Z) : list (aptr * Z) :=
(if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd (pp off) (-4), 0)] else [])
++ [(aadd (pp off) (-2), qv off); (aadd (aadd (pp off) (-2)) 1, Z.shiftr (qv off) 8); (aadd (pp off) (-3), idx)]
++ (if negb (resv off =? 0) then [(aadd ee (- resv off), 0)] else [])
++ (if 5 <=? resv off then [(aadd ee (-4), resv off); (aadd (aadd ee (-4)) 1, Z.shiftr (resv off) 8); (aadd (aadd ee (-4)) 2, Z.shiftr (resv off) 16); (aadd (aadd ee (-4)) 3, Z.shiftr (resv off) 24); (aadd ee (-5), 0)] else [])
++ [(aadd (pp off) (-3), Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5)].
Lemma EL_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "B'@'<'6'9&Q>%2215%411&Q1vRIvRAvRCvREr1%6554321&Q3%113%?3:31pU>A1").
Proof. intros off.
unfold ef_list, EL. rewrite (p0_eq st g idx n off). rewrite ef_c. fold (MR st g). fold stride.
change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. reflexivity.
Qed.
Lemma enframe_at_EL : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "G'@'<'9'QJ&Q>%3221&QBvRIvRAvRCvREr1%6554321(8&Q:&Q3%115%321:&Q4%118%74A@31%D3@91pU>F1").
Proof. intros off. rewrite (enframe_at_eq st g idx n off), EL_eq, (p0_eq st g idx n off), ef_c. reflexivity. Qed.
Definition stw (off : Z) : mstate := wrs (EL off) st.
Definition stf (off : Z) : mstate := havoc (pp off) n (stw off).
Lemma stw_TKS : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 ":'@&Q9&Q8r1%211&R0vRI%211%7241pU>91").
Proof. intros off. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "<'@'<'?&R0&Q8r1%211%411vRI%611%93831pU>;1"). Proof. intros off. exact (proj2 (wrs_ctrl (EL off) st)). Qed.
Lemma stw_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "8'@'FvRI&Q8r1%211%5241pU>71"). Proof. intros off. exact (proj1 (wrs_ctrl (EL off) st)). Qed.
Lemma pp16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 ">'@'<&R8&:'?&Q4r1%211%53481+@%8221z%;3<21pU>=1").
Proof. intros off. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ef_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
Lemma stw_hav : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q;'@'6'9'?%2241%411'<'7%113&RL'S1&S4&RN%34=218&S2%14?43:r2&QL&QE&Q8r3%211&4&Q4%114%33FI1%8251%:11%C6LG?=<1(2r1%22J1%J3H41&O&R0r4%A11%311%52F1p071pU6Q31pV@Q91pU>Q:1").
Proof. intros off u hl. intros Hu ch Hch. rewrite stw_tick. pose proof (stw_TKS off) as TK. rewrite <- (stw_tick off) in TK. rewrite <- (stw_tick off). exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
Lemma stf_ctrl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "@'@';'FvRI&Q7r1%211%5241'<'?&R0%115%219%53421%=271pU>?1").
Proof. intros off.
destruct (havoc_ctrl (pp off) n (stw off)) as [C T]. split; [exact (ctrl_eq_trans _ _ _ (stw_ctrl off) C)| rewrite T; apply stw_tick].
Qed.
Lemma stf_read_out : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q?'@'9'?%2213&=';'<&4r1%23791vR>%439;1%63:31&R6&:&Q4r2%211%43@B1%53AC;%7221&R7&R3vRE%2261%4261%E261%F2?1%H11'Q@&Q?&QE&Q7r3%211%L3Q1Q3C%5221%G3Q3Q5E%8221&Q8%117%:216%<215%Q53>51p0@1pUBQ:1pU>Q>1").
Proof. intros off r.
intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
apply (cell_read_havoc_out (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off)). exact Hr.
Qed.
Section SE.
Local Abbreviation SEC_T_EL_addrs := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "R2'@&Q>&R6zr2%3221&R3&R9&Q<r3%3221vRE%6221&R;vS6&Q;%3221%?251&R2&>'9%12DE&4%12FG&Q3r4%211%846J41%:3KC1';'<'?%:31Q07vR>%<33Q21%53431&:vR?%237Q61+3%K221%53:Q9@%Q8221&R7%Q626N+4%Q1221%4261%C261&=&Q4r5%211%A3FQE1%QD21=%QA22Q<%=2?1%L231%911%N2;1%O2I1p0Q11p0Q=1p0QJ1pTLQO1pU>R11")) (only parsing).
Variable off : ltac:(sec_ty2 constr:(SEC_T_EL_addrs) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_EL_addrs) 1%nat 0%nat).
Lemma EL_addrs : ltac:(sec_stmt2 constr:(SEC_T_EL_addrs) 2%nat 0%nat).
Proof.
intros Ho Hf Hin. pose proof ef_stride as [S16 _].
assert (R : 0 <= resv off) by (unfold resv, ee, pp, aadd; cbn [fst snd]; unfold IB, UNIT in *; lia).
unfold EL in Hin.
destruct (Z.eqb_spec off 0) as [O0|O0]; destruct (Z.eqb_spec (resv off) 0) as [R0|R0]; destruct (Z.leb_spec 5 (resv off)) as [R5|R5];
cbn [negb app map fst In] in Hin; unfold resv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold c; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.
End SE.
Lemma stf_known_w : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "R1'@&R6zr3%3221&R3&R9&Q<r4%3221vRE%6221&R;vS6&Q;%3221%?251&=';&:'?&Q4r5%211%534H1%H21A&R7%F23A%22D1%;241%=11'<'7%11Q1&Q2&Q3r6%211(8&4vR>%23EQ91%44FQ:1D(1%11Q<%;3831(2%12Q?Q7%A3?31&L&Q7r7%211%?4Q1QE<A&R5+WO%22Q21%83541p0:1p0M1p0Q<1p0QI1pVDQN1pVFQO1pU>R01").
Proof. intros off x w.
intros Ho Hf Hx HL. unfold known, SHd. cbn [fst snd].
rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.
Lemma stf_known_old : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "R1'@&R6zr3%3221&R3&R9&Q<r4%3221vRE%6221&R;vS6&Q;%3221%?251&=';&:'?&Q4r5%211%534H1%H21A&R7%F23A%22D1%;241%=11'<'7%11Q1&Q2&Q3r6%211(8&4vR>%23EQ91%44FQ:1D(1%11Q<%;3831%?3=12&LvRI%;4MQA8=%3321L&Q7r8%211r7%A4Q3QG>1%9331Dp071p0<1p0M1p0Q<1p0QI1pVBQN1pVFQO1pU>R01").
Proof. intros off x v.
intros Ho Hf Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.
Lemma EL_not_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "QE'@&R6zr2%3221&R3&R9&Q<r3%3221vRE%6221&R;vS6&Q;%3221%?251';&:'?&Q4r4%211%534G1%G21@&R7%E23@%22C1%;241&=&R2'9%12=Q0(8&4vR>%23AQ41%44BQ51@&>&Q>%921Q8%722Q9&Q3r5%211%745641%@3>91%B11p0D1p0Q11p0Q>1pTLQC1pU>QD1").
Proof. intros off a. intros Ho Hf Ha Hin. destruct (EL_addrs off _ Ho Hf Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.
Lemma stf_unknown : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q<'@&R6zr2%3221&R3&R9&Q<r3%3221vRE%6221&R;vS6&Q;%3221%?251';&:'?&Q4r4%211%534G1%G21@&R7%E23@%22C1%;241&M&Q7r5%211(8&4vR>%23AQ41%44BQ51@%9261p0;1p0H1p0Q51pTLQ:1pU>Q;1").
Proof. intros off a.
intros Ho Hf Ha. unfold unknown, SHd, stf. cbn [fst snd].
destruct (cell_read_havoc_in (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off) (fst bg, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite wrs_cells_other in Hc by (apply EL_not_in; assumption).
rewrite stw_tick. change (fst (pp off)) with (fst bg) in Hc.
apply (TF2_interior_old X st L BL LS INV g bg idx Hg Hidx ef_NH TF a v tk Hc).
unfold pp, aadd, c in Ha. cbn [fst snd] in Ha. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.
Ltac aeq :=
match goal with
| |- context [aptr_eqb ?a ?b] =>
first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd, c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
| rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd, c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
end.
Ltac lastw_eval :=
unfold EL; cbn [lastw app negb]; repeat aeq; reflexivity.
Lemma res_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "A'@'<&Q6r1%211&R;vS6&Q;%3221&R9&Q<%2218%7241vRE%9221%>3?;1pU>@1").
Proof. intros off. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.
Lemma qv_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "G'@'<&Q5r1%211&R4&R;&R3&:'?vR?%332;1&R9&Q<%221;%8241vR>%938A1%;215%=241%?217%D3EA1pU>F1").
Proof. intros off. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_blk_ok := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q6'@';&R6zr1%3221+WO%5231%7231&R3&R9&Q<r2%3221vRE%6221&R;vS6&Q;%3221%B251&N&Q7r3%211(8'9&Q>%221LvR?%543N17%643O1AvRAvRC%=4:321p0?1p0L1pU>Q51")) (only parsing).
Variable off : ltac:(sec_ty2 constr:(SEC_T_blk_ok) 0%nat 0%nat).
Lemma blk_ok : ltac:(sec_stmt2 constr:(SEC_T_blk_ok) 1%nat 0%nat).
Proof.
intros Ho Hf. pose proof ef_stride as [S16 SM].
destruct (stf_ctrl off) as [CE TK].
assert (MRE : MR (stf off) g = MR st g) by (apply MR_ext; exact (ce_metas _ _ CE)).
pose proof (res_eq off) as RE.
destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ef_gbase. fold stride.
replace (snd c + stride - IB - (snd c + UNIT * off) - n) with (resv off) by (rewrite RE; lia).
replace ((snd c + UNIT * off - snd bg - UNIT) / UNIT) with (qv off) by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
pose proof (ef_q_range off Ho Hf) as QR.
replace ((snd c + UNIT * off - (snd bg + UNIT)) / UNIT) with (qv off) in QR by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
assert (R0 : 0 <= resv off) by (rewrite RE; unfold IB, UNIT in *; lia).
assert (NP : forall x, x < snd (pp off) \/ snd (pp off) + n <= x -> ~ (snd (pp off) <= x < snd (pp off) + n)) by (intros; lia).
assert (PP : snd (pp off) = snd c + UNIT * off) by reflexivity.
split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
- destruct (Z.eqb_spec off 0) as [O0|O0].
+ apply (stf_known_old off); [lia| exact Hf| apply NP; lia| |].
* unfold EL. rewrite O0 at 1. cbn [Z.eqb negb app lastw].
destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
* subst off. pose proof (ish_hdr0 _ _ ISH bg g idx (ex_intro _ ai Hb) ltac:(unfold cnt_of; lia)) as K.
unfold c. cbn [snd]. replace (sstart (MR st g) idx + UNIT * 0 - 4) with (sstart (MR st g) idx - IB) by (unfold IB, UNIT; lia). exact K.
+ apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
unfold EL. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0). cbn [negb app lastw].
destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
-
replace (idx + 32 * Z.min (resv off) 5) with (Z.land (Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5) 255).
2:{ replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
destruct (Z.leb_spec 5 (resv off)).
- rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
- rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
unfold EL. destruct (off =? 0); destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
- unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
- unfold byte_of. rewrite Z.mul_1_r.
apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
- intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
assert (RS : resv off < 2 ^ 32).
{ rewrite RE. fold stride in Hres. unfold UNIT. lia. }
assert (E5 : (5 <=? resv off) = true) by (apply Z.leb_le; exact R5).
assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
1-4: apply (stf_known_w off); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|];
unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; repeat aeq; try reflexivity.
all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|].
unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
- intros RP.
replace (snd c + stride - IB - resv off) with (snd (pp off) + n) by (rewrite RE, PP; lia).
apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
unfold EL; rewrite EZ. destruct (off =? 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app];
try (destruct (Z.eq_dec (resv off) 5)); try (exfalso; lia); repeat aeq; reflexivity.
- intros a Ha. apply (stf_unknown off); [lia| exact Hf|]. rewrite PP. exact Ha.
Qed.
End SE.
Lemma ef_INVL : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "Q<'@';&R6zr1%3221+WO%5231%7231&R3&R9&Q<r2%3221vRE%6221&R;vS6&Q;%3221%B251&GvDvR<&Q7r3%211vA(3'9&Q>%221O%321Q0(8vR?%245Q31:%345Q41Fv0%:3621vB%C6BA>=21p0E1p0Q21pU>Q;1").
Proof. intros off.
intros Ho Hf. destruct (stf_ctrl off) as [CE TK]. pose proof ef_stride as [S16 _].
destruct Hg as [ai Hb] eqn:EHg.
apply (INVL_add_block X st (stf off) L BL LS c off n INV HP CE TK).
- intros m i Hs q Hq. rewrite ef_slots in Hs. inversion Hs. subst m i.
assert (NQ : ~ (fst q = fst bg /\ snd (pp off) <= snd q < snd (pp off) + n)).
{ intros [F R]. apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold pp, aadd, c in R. cbn [snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
rewrite (stf_read_out off q NQ). unfold stw. apply wrs_read_other.
intros Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & R & _). apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|].
rewrite sstart_succ. fold stride. unfold c in R. cbn [snd] in R. unfold IB in *. lia.
- intros rid sh Hsh. assert (REG' : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hb).
revert rid sh Hsh. change (DOMS st (stf off)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
+ rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
+ apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
- change (TKS (stf off) (s_tick st)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
+ rewrite havoc_le0 by lia. apply stw_TKS.
+ rewrite <- (stw_tick off). apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
- intros m i Hs. rewrite ef_slots in Hs. inversion Hs. subst m i. split; [exact Ho|]. split; [exact Hn|]. split; [exact Hf|].
apply blk_ok; assumption.
Qed.
Theorem enframe_ft : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WEnframe2 "RN'@'E'9'QJ&QK%3221!p021p071';&R6zr2%3221+WO%5231%7231&R3&R9&Q<r3%3221vRE%6221&R;vS6&Q;%3221%B251&GvDvR<vA(3&Q>%Q121Q3%Q221Q4(8vR?r4%346Q821%446Q91Cv0%:3721vB%@6?>I=21'FvRI%2219'<'?&R0r5%211%317%63521r8'7%11Hr6(2&Q=r7%Q=2Q<1%32J1%52O1%M4QO871%;2Q31p0=1p0E1p0I1p0Q;1p0QH1pUFR61pU>R:1&Q0%R:2R9B&QCvRAvRC&QM&QHr1%231QMR7%H2QB2%Q@4RBK21%62:1qU@QE1qUHRE1%<7=Q:;:R3R51%?5QL>QJ1R>p0A1pQ8RD1pU2RM1").
Proof. intros ctr Post.
intros HPost. pose proof ef_stride as [S16 SM].
assert (KR : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) by (intros q v; apply (known_range _ _ _ _ _ q v INV)).
assert (SL : 0 <= slack) by (unfold slack; apply Z.div_pos; unfold IB, UNIT in *; lia).
assert (SL16 : UNIT * slack <= stride - IB - n).
{ unfold slack, UNIT, IB in *. pose proof (Z.div_mod (stride - 4 - n) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (stride - 4 - n) 16 ltac:(lia)). lia. }
assert (GO : forall v, 0 <= v < 256 ->
ftree L (let '(st1, p) := enframe_at st g idx n (fold_off v slack) in ret (havoc p n st1, Some p)) Post).
{ intros v Hv. pose proof (fold_off_le v slack Hv SL) as FO.
assert (F255 : fold_off v slack <= 255).
{ unfold fold_off in *. destruct (Z.ltb_spec slack v); [| lia]. cbn zeta in FO. unfold fold_off in FO. lia. }
rewrite enframe_at_EL. cbn [ftree ret]. apply HPost.
- lia.
- unfold UNIT, IB in *. lia.
- apply ef_INVL; [lia|]. unfold UNIT, IB in *. lia.
- exact (proj1 (stf_ctrl _)).
- exact (proj2 (stf_ctrl _)). }
unfold enframe_full, enframe_read_off. fold (MR st g). fold stride. rewrite ef_slot.
change ((stride - IB - n) / UNIT) with slack.
apply rd8_ftree; [intros v; apply KR|]. intros b3 Hb3.
destruct (b3 =? 0); cbn [negb].
- apply GO. apply land255_range.
- apply rd16_ftree; [intros q v; apply KR|]. intros o16 Ho16. apply GO. apply land255_range.
Qed.
End ENFRAME.
End CEIL_WRAP_1.
