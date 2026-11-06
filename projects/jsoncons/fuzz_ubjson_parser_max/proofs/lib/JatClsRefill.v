(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG JatPoison JatInitCache ArtRuns ArtRunsMem JatRefill3 JatRefillCold JatPopulate1
JatCls JatFp JatClsPop3 JatClsRep JatClsGfa2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatClsRefill () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClsGfa2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3le"]; ["3lt"; "4nth"; "5Z"; "0EVOK"; "0GR"; "0HI"; "6machine_state"; "7bvmap"; "0M"; "0M'"; "0MA"; "0MG"; "0Q"; "8apart"; "8cell"; "8wr"]; ["9aev"; "9aruns"; ":msteps"; ";ret_ok"; "<art_cls"; "<art_cls_mfa'"; "<art_cls_needs_populate"; "<art_cls_new"; "<art_cls_ok"; "<art_cls_rep"; "<art_pc_hdr"; "<art_pc_hdr_foot"; "<art_refill_fp"; "<art_refill_n"; "<art_refill_rspec"; "<art_region_rep"]; ["<cl_cache"; "<cl_free"; "<cl_mu"; "=art_cls_pre_take"; "=art_gfa_fp"; ">art_agree"; "?art_ic_mem"; "@getr"; "@mkst"; "Amem_grows"; "Bloaded_segments"; "CIn"; "Dadd"; "Dle"; "Dlt"; "Dmul"]; ["Dof_nat"; "Dpow"; "Dsub"; "0c"; "0ca"; "0cl"; "0cl'"; "0fx"; "0inited"; "0j"; "0k"; "0km"; "0logE"; "0n"; "0pcp"; "0qs"]; ["0rA"; "0rG"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0t"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_ic_mem_fine : ltac2:(TCodec.tc2 tcn__JatClsRefill "QC'4'RKyR0%211'6y8%511%311p051'B&QMzr2%3221&QN&QLr3+TP0%3221&R1+2+R0%3221%9251'?r6uO%3221&>&Q;r5&RLr4%22O1%5241%711'<&QFr7r8%342?1:%31;%63Q321p081p0A1p0F1p0Q11pUNQ<1pT:Q71pQBQ91pTFQB1").
Proof.
induction k as [|k IH]; intros M ca x Hca Hca' Hk N; [reflexivity|]. rewrite art_ic_mem_S.
assert (N1 : ~ (ca + 80 * (Z.of_nat k + 1) + 4 <= U x < ca + 80 * (Z.of_nat k + 1) + 16)).
{ intros H. apply N. exists (Z.of_nat k + 1). lia. }
rewrite Wn_outside; [|lia|cbn; lia|cbn; lia]. rewrite Wn_outside; [|lia|cbn; lia|cbn; lia]. apply IH; [exact Hca|exact Hca'|lia|exact N].
Qed.
Lemma art_pc_hdr_ic : ltac2:(TCodec.tc2 tcn__JatClsRefill "Q3'RKyR0%211'6y8%511%311p051'B&QMzr1%3221&QN&QLr2+TP0%3221&R1+2+R0%3221%9251&Q:r3(9&QFr4uO%33251%73651p091p0D1pT:I1pQBK1").
Proof. intros M ca Hca Hca' c Hc. split; [apply cell_ic_mc|apply cell_ic_size]; first [lia | cbn; lia]. Qed.
Lemma art_pre_take_enough : ltac2:(TCodec.tc2 tcn__JatClsRefill "L'B'Q4';&QM+1r2%3221+N%5231%7231&Q8r3%2217'?&Q=r4%211&2&QA&QC%1259%311%52F1%:271p0<1p0@1pT<I1pT8K1").
Proof.
intros c cl Hc OK. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP.
- unfold art_cls_needs_populate in NP. apply Nat.ltb_lt in NP.
destruct OK as (_ & (Hau0 & Haumu) & _).
destruct (art_refill_need c Hc) as (Hneed & Hn). pose proof (art_class_size_facts c Hc) as (Hsz & _).
unfold art_cls_populate. cbn [cl_free]. rewrite length_app, art_carved_length.
assert (Hnew : Z.of_nat (art_refill_n c) <= art_cls_new c cl).
{ unfold art_cls_new. apply Z.div_le_lower_bound; [lia|]. lia. }
lia.
- unfold art_cls_needs_populate in NP. apply Nat.ltb_ge in NP. exact NP.
Qed.
Lemma art_pre_take_cache : ltac2:(TCodec.tc2 tcn__JatClsRefill "?'B'Q4'<'3%114&Q@&QCr2r1%3221%511%613%:3821pT<<1pT8>1").
Proof. intros c cl. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl); reflexivity. Qed.
Lemma art_cls_ok_pre_take : ltac2:(TCodec.tc2 tcn__JatClsRefill "QC'B'Q4';&QM+1r2%3221+N%5231%7231&Q8r3%2217'<'0&Q6r4%2216(9%63521&QL&QB%116+XPP0%4221+S`PPPP0%G221&Q5&R0&2&QA%11?%32Q01%511&Q7r5%221D%A241%;2F1+`PPPP0%Q5221%Q72?1p0G1&QC%129L%Q32:1p041p0Q31p0Q71pT<Q@1pT8QB1").
Proof.
intros c cl Hc OK Room. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP; [|exact OK].
destruct (Room eq_refl) as (R1 & R2). apply art_cls_ok_populate; assumption.
Qed.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_refill_tail := (ltac2:(TCodec.tc2 tcn__JatClsRefill "\='3'Q0%211'F!p021p041&Gy5'RKyR0%211%5241'6y8%611%311p061'B'4'Q4&QLr8+V@%3221r1&QO+R@r5%3221%9251&Q3r=%211';&QM+1r7%3221+N%5231%7231&R2r>+e0%3221%;2>1&QNr?&R1+2+Q?%3221%6251'<+RPP0r;%O221%43Q8J1+`PQoooPP0%I21A+Q5%=2<1%Q:2?1%:3Q>E1+TP0%Q=2B1rB%Q1221%Q2242rC%QB216rD%Q6221&M%QF2=:%244;61rE+QoonlP0%Q52D1%643?21zrA%Q@221+XPP0%QK21B+S`PPPP0%QD221&2&Q@%118%32R91%Q63R91I'?u1%221Iu8%42K1%R0231+4&R0&QA%11Q0%?2RE1%411%R?261+M%QJ2QI1%R9231&QIrQ2rQ1%3221&>&Q<rOrMrLrKrJrIrH&RL%12SAS2%:898765431%<11rQ4r2%211rQ5%113%R=3SC31p071pUNSJ1rQ3%J21I&QE&QDrQ0+Q0%S2221rN%5721JIHGF%731A9&Q:rG(9%3321B&N&QJrQ6+8%S>2Q:1%O2T?C%65542QJ1rQ7+@%SC2G1&QGrQ:(RI(:%23TJ;1%5241%Q:2TJ1%A5@:8R51rQ8+H%SN2Q:1rQ;+9%;3U31:%>231%QC2U31%J5I86R>1&OrQ9%24L1Q;S@&Q?%16Q=R5Q9S2QO3&@%12TLQ;rQ<%TM2TLQA%U32R51%U421M%RF1QK%U12RH1%U7231u4&A%S61QE%24U>R11S?%Q=5Q<;541p0=1pTDU@1rQ>+:%Q63UN1Q5%Q9231&RJ%12UOU5%TD3UO31rQ?%Q<3V4TJQ;%Q?221%U42NR3%72V51%TJ3V531rQ@%QD21Q@%;2V9S0%TN3V921rQA%QH21Q;%SC1RA%@2V>1%U33V>31%VA1VB&QK(1+3%QN3VF1QM%QO3VGSLQN+B%R13VI1R0+C%R33VK1R2+D%R53VM1R4+E%R73VO1R6+F%R93W11R8+G%R;3W31R:%R<3W4R5R;+I%R>3W61R=+J%R@3W81R?+K%RB3W:1RA(5%11J%I3K31%J3L61%K3M91%L3N<1%M3O>1%N3Q0A1%O3Q1D1%Q03Q2G1%Q13Q3J1%Q23Q4M1%Q33Q5Q01%Q43Q6Q21%Q63Q7W81rQD%S521T4rQE%S721T6%V@3WK31p061pUNQ>1%S;2T:R3%VD3WO1R1r3%S>21R0%R52X3QL%VH3X321r4%S@3X8W<S?%SC221rQB%VM3X821%QH3QJS9F%QI3QKSC1%QJ3QLQG1%QK3QMQI1%QM3QNWO1%SK2WDTJrQK%SM21TL%W63XA31p051pUNR41rQH%UC21X4rQC%U@8N1@R=RARGRNU7%UB11%X>1U5%;1U6%W@3XF21p041pUNXM1%UL2:X4'8%12XIXI(7%14XKXKT4V:%QK13%RC3421rQI%U9321XKrQ=r9%U432U21&Q9r:%26SCQCQEQ5S<1rR2rR1&QHvR7r<rQJ%45321X6Q4%7261p091p0=1p0A1p0J1p0L1p0Q51p0Q81p0QD1p0QJ1p0QO1pQDYI1pU:YO1'Q1vCvDrQGrQF+Zjf<%UB3Z81UA/01Z8%J5IRB1SOT3%97V087J651p0;1p0R?1p0SO1p0T51p0T:1p0TA1p0TI1p0U:1p0U=1p0UA1p0UK1p0V71p0V?1p0VD1p0VM1p0W01p0WF1p0WK1p0X61p0X=1p0XC1p0XH1p0XL1p0Y11p0Y51p0Y:1p0Y<1p0YA1p0YF1p0YI1p0YO1p0Z71p0Z=1p0ZF1tTN[6ZJ1tT:[7[11pT>[61pTL[81pTH[:1pT8[;1pU0[<1pU<[=1pUB[>1pUL[?1pQ<[@1pU@[A1pU6[I1pU>[D1pQH[E1pQF[F1pQB[G1pU4[M1pU8[N1pTJ\91pQJ\61")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 0%nat 0%nat).
Variable logE : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 2%nat 0%nat).
Variable rG : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 4%nat 0%nat).
Variable MA : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 5%nat 0%nat).
Variable MG : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 6%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 7%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 8%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 9%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 10%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 11%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 12%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 13%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 14%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 15%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 16%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 17%nat 0%nat).
Variable cl' : ltac:(sec_ty2 constr:(SEC_T_art_refill_tail) 18%nat 0%nat).
Lemma art_refill_tail : ltac:(sec_stmt2 constr:(SEC_T_art_refill_tail) 19%nat 0%nat).
Proof using Type Q logE regs rG M MA MG rom raw sp HI t spb ris qs c km n cl'.
intros ca pcp
Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Hkm Hkm' Lc Hn Hnf GA AAf GG AG PH F1 F8 F9 Wt RRG CH E10 E2 E8 E9 KG K.
assert (Eca : ca = t + 208) by reflexivity. assert (Epcp : pcp = t + 208 + 80 * c) by reflexivity.
assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
unfold art_gfa_fp, art_pop_fp in AG.
pose proof Atk as Xk. unfold apart in Xk. pose proof Ats as Xs. unfold apart in Xs.
assert (TFR : forall a v, sp - 24 <= a -> a + 8 <= sp -> cellA MA a 8 v -> cellA MG a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_tr1 _ MA MG _ _ _ AG); [|exact C]. clear - Ha Ha' HHI Hsp' Hris Eris Hspb Espb Hc Ht Ht' Hkm Hkm'. zarith_t. }
pose proof (art_refill_b_fn rG MG rom raw sp pcp (Z.of_nat n) (U (getr regs 8)) (U (getr regs 9)) E2 E8 E9 E10
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret (UB _) (UB _) ltac:(unfold apart; lia)
ltac:(eapply wr_grows; [exact GG|]; eapply wr_sub; [exact Wt|lia|lia])
ltac:(apply TFR; [lia|lia|exact F1]) ltac:(apply TFR; [lia|lia|exact F8]) ltac:(apply TFR; [lia|lia|exact F9])) as RUNB.
match type of RUNB with msteps _ _ (mkst ?R _ ?X _) => set (rB := R) in RUNB; set (MB := X) in RUNB end.
eapply ar_steps; [exact RUNB|]. apply ar_done.
assert (AB : art_agree [(pcp, 4)] MG MB). { unfold MB. eapply art_agree_sub; [zagree|]. zsub. }
assert (GB : mem_grows MG MB) by (unfold MB; apply Wn_grows).
apply (K rB MB).
- unfold rB; gres. exact E10.
- unfold rB; gres. reflexivity.
- unfold rB; gres. reflexivity.
- intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ unfold rB; gres; apply Z_to_bv_bv_unsigned | unfold rB; gres; apply KG; inl ].
- eapply mem_grows_trans; [exact GA|]. eapply mem_grows_trans; [exact GG|exact GB].
- intros x N. rewrite <- (AAf x N). unfold art_refill_fp in N.
repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
rewrite (AB x) by (cbn; split; [lia|exact I]). apply AG. cbn [art_out fst snd]. fold ca in Epcp. repeat split; lia.
- exact GB.
- exact AB.
- intros c' Hc'. destruct (PH c' Hc') as [P1 P2]. fold ca in AG. split.
+ apply (art_cell_tr1 _ MG MB _ _ _ AB); [clear - Epcp Eca Hc Hc' Ht Ht' HHI Hsp'; zarith_t|].
apply (art_cell_tr1 _ MA MG _ _ _ AG); [|exact P1]. clear - Epcp Eca Hc Hc' Xk Xs HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hkm Hkm'. zarith_t.
+ apply (art_cell_tr1 _ MG MB _ _ _ AB); [clear - Epcp Eca Hc Hc' Ht Ht' HHI Hsp'; zarith_t|].
apply (art_cell_tr1 _ MA MG _ _ _ AG); [|exact P2]. clear - Epcp Eca Hc Hc' Xk Xs HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hkm Hkm'. zarith_t.
- split.
+ split.
* rewrite Lc. unfold MB. apply cell_Wn_hit; [lia|cbn; lia].
* intros j Hj. rewrite Lc in Hj. apply (art_cell_tr1 _ MG MB _ _ _ AB); [|apply CH; exact Hj]. clear - Hj Hn Epcp Eca Hc Ht Ht' HHI Hsp'. zarith_t.
+ pose proof RRG as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
apply (art_region_rep_upd spb ris c 0 0 cl' cl' MG MB [(pcp, 4)]); try reflexivity;
first [ lia | exact RRG | exact GB | exact AB | (intros; reflexivity) | idtac ].
* clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hnf. zarith_t.
* apply (art_cell_tr1 _ MG MB _ _ _ AB); [|exact Rmx]. clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* apply (art_cell_tr1 _ MG MB _ _ _ AB); [|exact Rnf]. clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* apply (art_cell_tr1 _ MG MB _ _ _ AB); [|exact Rna]. clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_refill_prologue := (ltac2:(TCodec.tc2 tcn__JatClsRefill "YI&Gy5'RKyR0%211%5241'6y8%611%311p061'B'0&QLr3+V@%3221'<&QGr9(RI+1(:%33F21%6251r6%93F21r:+2%93L17%<231&RJ%12M7%@3M31r;+:%@3Q31>%C231%72Q3H%F3Q321r<+;%F3Q91D%I231r4&QO+R@%221F%Q3241%B2Q>1%Q13Q>71r=+<%Q13QD1O%Q4231+QVmdH%I2QE1%Q83QE31r>+=%Q83QK1Q6%Q;231r8%Q02QL1%Q?3QL31';&QM%12Q>Q@+N%32QB1%5231+VbTP0+Q0%QL221%821Q2&QN&R1+Q?%22QB1%42L1+TP0%?21N%R52H2%R621R4&R2r?%221>%E241&O&QJrCr@%821D%54431ErD%74614?&Q:rE%23Q8=1&NrFrA%QI2QH1%RJ2B1u4z%75A6321'='Q2&QHvR7rJ+Zjd<%RM3S>1RK/01S>rIrH%8576321r2+Zjl<%S43SE1S2/01SEr1%>5=5217%@3Q371%S;27S6+Zjf<%S;3SL1S9/01SL%S@3SM41%S@2<S5%Q?2OQK%S52T11%SD3T131+8%SC3T61SA%SF2B1rB%RM2RLQ<%SN221%S=2T91%SL3T951+9%SK3T>1SI%SN2J1&R0&Q=%11QE%311%SF2TB1%T53TB61%T52Q1SC%T73TD1S0%T72Q3S?+R`0%T>2B1%SM2TI1%T<3TI41%T<2Q8S9%T02TLR1%T?3TL21%T?2Q;S5+@%TF2H1%T52U11%TD3U141+>%TC3U61TA%TF2QB1%TH3U51D%U81U9&QK(1+3%TJ3U=1TH+4%TL3U?1TJ+B%TN3UA1TL+C%U03UC1TN+D%U23UE1U0+E%U43UG1U2+F%U63UI1U4+G%U83UK1U6+H%U:3UM1U8+I%U<3UO1U:+J%U>3V11U<+K%U@3V31U>(5%11L%K3M31%L3N61%M3O91%N3Q0<1%O3Q1?1%Q03Q2B1%Q13Q3E1%Q23Q4H1%Q33Q5K1%Q43Q6N1%Q53Q7Q11%Q63Q8Q41%Q83Q9RI1%V22U8RNrL%V421S0%V63VC31p051pUNQ?1&QI%12S8S1&QE'8%12VCVC(7%14VEVERMTH+RD%VE2RI1+R[<%54VIVI21%Q017%QJ3821%QK3971%<31SES>&>rG%TG21U3&RL%12W:SC%U<231%U4225%U?221%811&Q;%72W@SM%22TF1%<11%V:1W8%Q21W9%W73W?21p041p091pUNWG1(9%TM3SD1T3%TK5U5T4SCTFTE%U;2TKSIu8%E2WNG%TO5U9T8321%U?2TOS1%WB2TESM%I2X21%U35U=T<361%UC2U3R:%WF2TISI%M2X61%U75UAT@3:1%V:251%V;2:1%V<2?1%V=2A1%V>2D1%V?2Q81%V@2QF1%VA2QI1%VB2S:1%VC2S?1%VD2SE1%VE2SI1%VF2SO1%VG2T21%VH2T<1%VI2TE1%VJ2TJ1%VK2U01qQFXC1%UC2XD1qU2XJ1%UE2XK1p0UG1p0V01p0V41p0V71p0V>1p0VE1p0VH1p0VN1p0W31p0W:1p0WB1p0WJ1p0X61p0X=1p0XE1tT:Y5Y01pTBY51pT8Y71pULY81pU@Y91pU6YA1pU>Y<1pQBY=1pU8YC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 4%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 6%nat 0%nat).
Variable inited : ltac:(sec_ty2 constr:(SEC_T_art_refill_prologue) 7%nat 0%nat).
Lemma art_refill_prologue : ltac:(sec_stmt2 constr:(SEC_T_art_refill_prologue) 8%nat 0%nat).
Proof using Type regs M rom raw sp t c inited.
intros ca H1 H2 H10 H11 H12 H13 Hc IMG Hsp' Ht Hts W Wt PH C0.
assert (Eca : ca = t + 208) by reflexivity.
assert (Emc : art_ic_mc c / 2 = Z.of_nat (art_refill_n c)).
{ unfold art_refill_n. rewrite Z2Nat.id; [reflexivity|]. apply Z.div_pos; [pose proof (art_ic_mc_range c ltac:(lia)); lia|lia]. }
set (MF := Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))).
assert (AF : art_agree [(sp - 32, 32)] M MF). { unfold MF. eapply art_agree_sub; [zagree|]. zsub. }
assert (GF : mem_grows M MF) by (unfold MF; zgrows).
assert (FC : cellA MF (sp - 8) 8 (U raw) /\ cellA MF (sp - 16) 8 (U (getr regs 8)) /\ cellA MF (sp - 24) 8 (U (getr regs 9))).
{ unfold MF. repeat split; zcell. }
destruct FC as (FC1 & FC8 & FC9).
destruct inited.
-
destruct (PH c ltac:(lia)) as [Pmc _]. cbn in Pmc.
pose proof (art_refill_a_fn regs M rom raw sp ca c 1275544 (art_ic_mc c) H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) IMG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
(art_ic_mc_range c ltac:(lia)) ltac:(unfold apart; lia) W Pmc) as RUN.
fold MF in RUN. match type of RUN with msteps _ _ (mkst ?R _ _ _) => set (rA := R) in RUN end.
exists rA, MF. split; [exact RUN|].
split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|].
split; [unfold rA; gres; rewrite Emc; reflexivity|]. split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|].
split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; rewrite Emc; reflexivity|].
split. { intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; (unfold rA; gres; reflexivity). }
split; [exact GF|]. split; [eapply art_agree_sub; [exact AF|]; zsub|].
split. { intros x N1 _. apply AF. cbn. split; [lia|exact I]. }
split. { intros c' Hc'. destruct (PH c' Hc') as [P1 P2]. cbn in P1, P2. split; ztr. }
split; [ztr|]. split; [exact FC1|]. split; [exact FC8|exact FC9].
-
destruct (PH c ltac:(lia)) as [Pmc _]. cbn in Pmc.
destruct (art_refill_a_cold regs M rom raw sp ca c 1275544 H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) IMG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold apart; lia) W ltac:(eapply wr_sub; [exact Wt|lia|lia]) Pmc)
as (rA & RUN & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & KA).
fold MF in RUN. set (MA := art_ic_mem MF ca 31) in *.
assert (AI : art_agree [(ca + 84, 2412)] MF MA).
{ intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold MA. apply art_ic_mem_outside; [lia|lia|lia|]. cbn. lia. }
assert (GI : mem_grows MF MA) by apply art_ic_mem_grows.
exists rA, MA. split; [exact RUN|].
split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [rewrite A9, Emc; reflexivity|]. split; [exact A10|]. split; [exact A11|].
split; [exact A12|]. split; [exact A13|]. split; [rewrite A14, Emc; reflexivity|]. split; [exact KA|].
split; [eapply mem_grows_trans; [exact GF|exact GI]|].
split; [exact (art_agree_trans _ _ _ _ _ AF AI)|].
split. { intros x N1 N2. unfold MA. rewrite art_ic_mem_fine by (first [lia | exact N2]). apply AF. cbn. split; [lia|exact I]. }
split; [apply art_pc_hdr_ic; lia|].
split. { unfold MA. apply cell_ic_count; [lia|lia|lia|lia|]. ztr. }
split; [ztr|]. split; ztr.
Qed.
End SE.
#[using="Type"] Theorem art_refill_rspec_holds : ltac2:(TCodec.tc2 tcn__JatClsRefill "5&Q>vCvDvR7%43321").
Proof.
unfold art_refill_rspec.
intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs c km inited cl
H1 Hret H2 H4 H10 H11 H12 H13 Hc HHI Hsp' GEO W Wt PC L T PH RC OK Ecache Emu ST Room EV K.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x691000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
clear G9 G10 G15 G16.
destruct RC as [[CR0 _] RR]. rewrite Ecache in CR0. cbn in CR0.
destruct ST as (m1 & m2 & sv & Cm1 & Cm2 & Csv).
pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & _ & _).
assert (Hkm : 0 <= km) by lia.
set (n := art_refill_n c). set (ca := t + 208) in *. assert (Eca : ca = t + 208) by reflexivity.
destruct (art_refill_need c Hc) as (_ & Hn). fold n in Hn.
destruct (art_refill_prologue regs M rom raw sp t c inited H1 H2 H10 H11 H12 H13 Hc ltac:(lia) Hsp' G7 ltac:(lia)
ltac:(eapply wr_sub; [exact W|lia|lia]) Wt PH CR0)
as (rA & MA & RUNA & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & KA & GA & AA & AAf & PHA & CRA & F1 & F8 & F9).
fold ca n in A8, A9, A11, A13, A14, AA, AAf, PHA, CRA.
eapply ar_steps; [exact RUNA|].
pose proof G11 as X11. unfold apart in X11. pose proof G18 as X18. unfold apart in X18. pose proof At_i as Xi. unfold apart in Xi.
assert (PCA : art_prim_consts spb ris MA). { eapply art_prim_consts_fp; [exact AA| |exact PC]. intros z Hz. cbn. clear - Hz Xi Eca HHI G1 G7 G8. repeat split; lia. }
assert (LA : art_layout MA). { eapply art_layout_fp; [exact AA| |exact L]. intros z Hz. cbn. clear - Hz Xi Eca HHI G1 G7 G8. repeat split; lia. }
assert (TA : art_tsd MA tp key tsd ctx t).
{ eapply art_tsd_fp; [exact AA| | |exact G19|exact G20|exact G21|exact G22|exact T].
- intros z Hz. cbn. clear - Hz Xi Eca HHI G1 G7 G8. repeat split; lia.
- intros z Hz. cbn. clear - Hz X18 Eca HHI G1 G7 G8 G13 G14. repeat split; lia. }
assert (RRA : art_region_rep spb ris c 0 cl MA).
{ pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
apply (art_region_rep_upd spb ris c 0 0 cl cl M MA [(sp - 32, 32); (ca + 84, 2412)]); try reflexivity;
first [ lia | exact RR | exact GA | exact AA | (intros; reflexivity) | idtac ].
- clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
- clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
- clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8 Hnf4 Hmfa1. zarith_t.
- apply (art_cell_tr1 _ M MA _ _ _ AA); [|exact Rmx]. clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
- apply (art_cell_tr1 _ M MA _ _ _ AA); [|exact Rnf]. clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
- apply (art_cell_tr1 _ M MA _ _ _ AA); [|exact Rna]. clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t. }
assert (OK1 : art_cls_ok c (art_cls_pre_take c cl)).
{ apply art_cls_ok_pre_take; [exact Hc|exact OK|]. intros NP. destruct (Room NP) as (R1 & R2 & _). split; assumption. }
pose proof (art_pre_take_enough c cl Hc OK) as Hen. fold n in Hen.
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
apply (art_gfa_aruns EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log rA MA rom (0x56acc : bv 64)%bv (sp - 32) HI t ctx tp key tsd spb ris qs c km m1 m2 sv cl
A1 ltac:(unfold ret_ok; bveq) A2 ltac:(rewrite KA by inl; exact H4) A10 ltac:(rewrite A11; f_equal; lia) A12 ltac:(rewrite A13; f_equal; lia) A14
Hc ltac:(lia) ltac:(lia) GEO ltac:(eapply wr_grows; [exact GA|]; eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_grows; [exact GA|exact Wt])
PCA LA TA RRA OK Emu
ltac:(apply (art_cell_tr1 _ M MA _ _ _ AA); [clear - Eca HHI Hsp' G2 G7 G8; zarith_t|exact Cm1])
ltac:(apply (art_cell_tr1 _ M MA _ _ _ AA); [clear - Eca HHI Hsp' G2 G7 G8; zarith_t|exact Cm2])
ltac:(replace (t + 2792) with (ca + 2584) by lia; apply (art_cell_tr1 _ M MA _ _ _ AA); [clear - Eca HHI Hsp' G2 G7 G8; zarith_t|exact Csv])
ltac:(intros NP; destruct (Room NP) as (R1 & R2 & R3 & R4); repeat split; first [assumption | eapply wr_grows; [exact GA|assumption]]) EV).
intros rG MG Q10 Q2 Q1' QK QG QA QRR QCH QSH QST.
assert (Lc : length (cl_cache (art_cls_refill c cl)) = n).
{ rewrite art_cls_refill_eq. fold n. cbn [art_cls_take cl_cache]. rewrite length_skipn. lia. }
pose proof OK1 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hmfa11) & Hnf41 & _ & _).
assert (Hnf' : 4 * Z.of_nat (length (cl_free (art_cls_refill c cl))) <= 2 ^ 29).
{ rewrite art_cls_refill_eq. fold n. cbn [art_cls_take cl_free]. rewrite length_firstn. lia. }
apply (art_refill_tail Q (log ++ art_refill_events spb c cl) regs rG M MA MG rom raw sp HI t spb ris qs c km n (art_cls_refill c cl)
Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s Hkm ltac:(lia) Lc Hn Hnf' GA).
- intros x N. apply AAf.
+ intros H. apply N. unfold art_refill_fp. left. lia.
+ intros H. apply N. unfold art_refill_fp. right. right. left. exact H.
- exact QG.
- exact QA.
- exact PHA.
- exact F1.
- exact F8.
- exact F9.
- eapply wr_grows; [exact GA|exact Wt].
- exact QRR.
- intros j Hj. pose proof (QCH j Hj) as C. fold ca. replace (ca + 80 * c + 16 + 4 * Z.of_nat j) with (t + 208 + 80 * c + 16 + 4 * Z.of_nat j) by lia. exact C.
- exact Q10.
- exact Q2.
- rewrite QK by inl. exact A8.
- rewrite QK by inl. exact A9.
- intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; (rewrite QK by inl; apply KA; inl).
- intros regs' M' P10 P2 P1 PK PG PAf PGG PAB PPH PCR.
apply (K regs' M' P10 P2 P1 PK PG PAf PPH PCR).
+ rewrite art_cls_refill_eq. apply art_cls_ok_take; [exact OK1|rewrite art_pre_take_cache; exact Ecache|exact Hen|lia].
+ intros NP j Hj. pose proof (QSH NP j Hj) as C. pose proof At_s as Xs. unfold apart in Xs.
apply (art_cell_tr1 _ MG M' _ _ _ PAB); [|exact C]. clear - Hj Xs Eca Hc G4 Espb Hkm Emu Hmu3 G6 Eris G2 G7 G8. zarith_t.
Qed.
End Spec.
