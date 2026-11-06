(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG JatPoison JatInitCache ArtRuns ArtRunsMem JatRefill1 JatPopulate1 JatPopulate4
JatCls JatFp JatClsPop3 JatClsRep JatClsGfa1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatClsGfa2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClsGfa1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClsGfa2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3sub"]; ["4le"; "4lt"; "5Forall"; "5nth"; "6Z"; "0EVOK"; "0GR"; "0HI"; "7machine_state"; "8bvmap"; "0M"; "0M'"; "0M1"; "0ME"; "0Q"; "9apart"]; ["9cell"; "9wr"; ":aev"; ":aruns"; ";class_size"; "<ret_ok"; "=art_cls"; "=art_cls_mfa'"; "=art_cls_needs_populate"; "=art_cls_new"; "=art_cls_ok"; "=art_cls_refill"; "=art_cls_take"; "=art_cptr_ok"; "=art_evok_list"; "=art_geo"]; ["=art_prim_consts"; "=art_refill_events"; "=art_refill_n"; "=art_region_rep"; "=cl_au"; "=cl_cache"; "=cl_free"; "=cl_mu"; ">art_gfa_fcells"; "?art_cls_pre_take"; "?art_gfa_fp"; "@art_agree"; "@art_out"; "Aart_tsd"; "Bart_layout"; "Cgetr"]; ["Cmkst"; "Dmem_grows"; "Eloaded_segments"; "FIn"; "Gadd"; "Gle"; "Glt"; "Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0W"; "0c"; "0chp"; "0cl"; "0cl1"]; ["0ctx"; "0fa"; "0fx"; "0j"; "0k"; "0key"; "0km"; "0log"; "0logE"; "0m1"; "0m1'"; "0m2"; "0m2'"; "0n"; "0qs"; "0r"]; ["0rE"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "HBV"; "HZ_to_bv"; "Hbv"; "0sv"; "0sv'"; "0t"; "0tp"; "0tsd"]; ["0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_cls_pre_take (c : Z) (cl : art_cls) : art_cls := if art_cls_needs_populate c cl then art_cls_populate c cl else cl.
Lemma art_cls_refill_eq : ltac2:(TCodec.tc2 tcn__JatClsGfa2 "@'D'Q6'=&Q;r2r1%3221&Q<&QB%115&QI%1276%5231%;3<71pTN=1pTJ?1").
Proof. reflexivity. Qed.
Definition art_gfa_fp (sp t spb ris qs c km : Z) : list (Z * Z) :=
(sp - 128, 128) :: (t + 208 + 80 * c + 16, 64) :: art_pop_fp (sp - 128) t spb ris qs c km.
Lemma art_prim_consts_fp : ltac2:(TCodec.tc2 tcn__JatClsGfa2 "Q='4'9'D%2211%411'S:yR0%211'7y8%511%311p051&QKr5r4r3%43321'<&R5+RPP0r1%3221&R6+VbTP0%2241%8241&QLr8r2%3221p051pW4N1&Q@r6%23DC1%33FE2p021p061p0F1pV:Q61pV@Q71pQHN1pQFO1pTHQ81").
Proof.
intros W M M' spb ris A O (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
assert (TI : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x691000 -> cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros x Hx. apply A. apply O. lia. }
unfold art_prim_consts. repeat split; apply TI; first [assumption | cbn; lia].
Qed.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_gfa_tail := (ltac2:(TCodec.tc2 tcn__JatClsGfa2 "]N'4'Q2%211'H!p021p041&Iy5'S:yR0%211%5241'7y8%611%311p061'D'5'Q6&R4r7&R7r4&R9+2+Q0%3221%6251%9281+S`PPPP0%;221+T0r5%<221%?2>1r:+V@%B221+R@r6%C221%F241+@%H221&?&3&QF%11I%32Q01%521A&Q5r?%211'<&R5+1r9%3221+N%5231%7231&R:r@+d0%3221%;2>1&R6rA+Q?%Q>2Q=1%4231'=+RPP0r=%QE221%43QKH1+`PQoooPP0%G21?+Q5%QH2QG1%QM2=1%:3R1C1+TP0%R02@1rD%O221%Q0242rE%R5216rF%Q4221&O%R92=:%244;61rG+VbTP0%Q321H%643?I1'@u1rB%3221u8%5231%QC231rC%QL16%QN2RK1%:231+4&R8%R116%R32S01%311%RM251+M%RM2RL1%QO231'B&Q=&Q4%11K&QD%11Q7%5231%R?1Q9%83S>21%51Q8%R:21S3&QCrLrKrI+QL%S?2S>1rQ3%766542Q?1&Q0&R2rQ4+RQP0+ZooooPPPPoooO%55432Q81&Q1rQ5rO%34821R0&R1rQ7rQ6%3221&QK&QJrQ1rQ0rNrM%57F43<21KrQ8%8321;%=22<(2'9%12TCTC(8rJ%TC21SL+8%44THTH21(6%117%:3831rQ9%F321?%TK2Q;T4%R11Q;%Q75Q642R:1&QHrQ:&QOrQ>(S8(;%23UA@1%5241+9%53UD14%8271+B%83UG17%;2:1+C%;3UJ1:%>2=1+D%>3UM1=%A2@1+E%A3V01@%D2C1+F%D3V31C%G2F1+G%G3V61F%J2I1+H%J3V91I%M2L1+I%M3V<1L%Q02O1+J%Q03V?1O%Q32Q21+K%Q33VB1Q2%Q62Q51%Q9?Q8R6QLQ2OLIFC@=:741%Q63VEV3Q5%Q92Q81&S9%U12R0UO%22VG1%TI3VG41rQ?%Q?21Q;%62VKR8%TM3VK21rQ@+;%QB3W11QA%QE231rQ2%SL11%VF2SN1%VI2RA1%@2W51%U73W561rQA+=%QL3W;1QK%QO231%F2W;S2%U=3W;21rQB+>%R23WA1R1%R5231%T;1S>%M2WB1%UD3WB31rQC%R:21QM+QM%W82W71%Q32WH1%UJ3WH41rQD%R@21R0%TF1S;%W@2TH1%WC2SK1%Q:2WO1%V13WO51rQE+3%RF3X51RE%RI231rQF%RK213%V83X631%RK3X:U3RJ%RN241rQG%S0213%V=3X;31r2+:%S23XA1S1%S5231%QL2XAW2%VC3XA21r3%S921R1%R02XEK%VG3XE21%S:3XIW8S9%S=2X:1%VJ3XH1D%XK1XL&R3r1%SL13%T534R>1%T635RB1%T736RF1%T837RJ1%T938RN1%T:39S21%T;3:S61%T<3;S:1%T=3<S>1%T>3=SB1%T?3>SF1%T@3?SJ1%TA3@Q21%TB3AQ81%A3B@1%T22Y1Q0rQO%T421Q2%WA3Y?31p051pW2H1rQL%U921XLrQH%U671QAQEQLR2R9R?rQM%U9321XI%U>22Y=%Y?2S1XH%TO4YCYC1TL+R0%U14YEYETA1+R8%YD2S61%U44YHYH1U1%U54YIYIS8U2%U93U71U0%U:3U831%U;3U971%U<3U::1rQNr8%UI3321z&Q<%12RGRN%VC6GR2R;31XL&A%12QBR=r<%W:1R3%Z42W<1%Z72S51u4&C&QE%<2RARE%211%44Z@R;1?%VH5VG:761p0<1pU8ZB1rR6rR5&R0vRBr;%352BK1QC%6251p081p0H1p0M1p0Q=1p0Q?1p0QD1p0QG1p0RA1p0RE1p0RJ1pQH[61pV8[<1'Q3vEvFrQKrQJ+ZkX0%V83[E1V7/01[E%I5HR21SFSM%97WF87I651p0;1p0S>1p0SD1p0SL1p0T41p0T;1p0TC1p0TJ1p0U51p0U:1p0UA1p0VL1p0W01p0W>1p0W@1p0WJ1p0WO1p0X41p0X;1p0XD1p0XG1p0Y11p0Y;1p0Y@1p0YH1p0YM1p0Z11p0Z61p0Z81p0Z=1p0ZB1p0ZE1p0ZK1p0[11p0[71p0[@1tU:\D[D1tTL\F[K1tV0\G\51tU4\H\:1pU0\G1pUL\I1pU>\K1pTJ\L1pUN\M1pV:\N1pV@\O1pVL]01pQ@]11pV>]21pV4]:1pV<]51pQL]61pQJ]71pQF]81pV2]>1pV6]?1pUB]J1pQN]G1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 0%nat 0%nat).
Variable logE : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 2%nat 0%nat).
Variable rE : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 4%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 5%nat 0%nat).
Variable ME : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 6%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 7%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 8%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 9%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 10%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 11%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 12%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 13%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 14%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 15%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 16%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 17%nat 0%nat).
Variable cl1 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail) 18%nat 0%nat).
Lemma art_gfa_tail : ltac:(sec_stmt2 constr:(SEC_T_art_gfa_tail) 19%nat 0%nat).
Proof using Type Q logE regs rE M M1 ME rom raw sp HI t spb ris qs c km n cl1.
intros fa r chp k
Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ati Hn Hnl Hnf Hcp Hau RR1 Crd Wt GM1 AM1 G1E A1E Cnf F E2 E8 E11 E13 E14 E19 E20 E3 E4 K.
assert (Hr : r = ris + 128 * c) by reflexivity. assert (Hfa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity. assert (Hchp : chp = t + 208 + 80 * c + 16) by reflexivity.
assert (Hk : Z.of_nat k = Z.of_nat (length (cl_free cl1)) - Z.of_nat n) by (unfold k; lia).
pose proof RR1 as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa.
set (ws := skipn k (cl_free cl1)).
assert (Lws : length ws = n) by (unfold ws; rewrite length_skipn; unfold k; lia).
assert (Nws : forall j, (j < n)%nat -> nth j ws 0 = nth (k + j) (cl_free cl1) 0). { intros j Hj. unfold ws. apply nth_skipn. }
pose proof (art_class_size_facts c Hc) as (Hsz & _).
unfold apart in Atk, Ati.
pose proof (art_cell_norm _ _ _ _ Rna) as Rnan. pose proof (art_mod64_range (cl_na cl1)) as Hnan.
destruct (art_clsgfa_finish ws rE ME rom raw sp r ris (512 * qs + 2 ^ 30) c chp (fa + 4 * Z.of_nat k) (cl_na cl1 mod 2 ^ 64)
(getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
E2 E8 ltac:(rewrite Lws; exact E11) E13 ltac:(rewrite Lws; exact E14) E19 E20 Hret ltac:(rewrite Lws; exact Hn)
ltac:(lia) Hsp' Hr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(rewrite Lws; unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) Hnan
ltac:(rewrite Lws; eapply wr_grows; [exact G1E|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact G1E|exact Wr])
ltac:(intros j Hj; rewrite Lws in Hj; rewrite (Nws j Hj); split;
[ assert (X : art_cptr_ok (AsanTab.class_size c) (cl_au cl1) (nth (k + j) (cl_free cl1) 0)) by (apply (proj1 (Forall_forall _ _) Hcp); apply nth_In; lia);
pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl1) _ ltac:(lia) Hau X); lia
| replace (fa + 4 * Z.of_nat k + 4 * Z.of_nat j) with (fa + 4 * Z.of_nat (k + j)) by lia;
apply (art_cell_tr _ M1 ME _ _ _ A1E); [zgap|lia|cbn; lia|apply Rfa; lia] ])
ltac:(ztr) ltac:(ztr) ltac:(ztr) F)
as (rF & MF & RUNF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F3 & F4 & GF & AF & Cch & Cna' & Cmx').
rewrite Lws in AF.
eapply ar_steps; [exact RUNF|]. apply ar_done.
assert (A1F : art_agree [(r + 16, 8); (chp, 64); (r + 72, 8); (r, 8)] M1 MF).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact A1E|exact AF]|]. zsub. }
assert (G1F : mem_grows M1 MF) by (eapply mem_grows_trans; eassumption).
assert (Lfn : length (firstn k (cl_free cl1)) = k) by (rewrite length_firstn; unfold k; lia).
apply (K rF MF F10 F2 F1).
- intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ rewrite F3; exact E3 | rewrite F4; exact E4 | assumption ].
- eapply mem_grows_trans; [exact GM1|exact G1F].
- eapply art_agree_sub; [eapply art_agree_trans; [exact AM1|exact A1F]|]. unfold art_gfa_fp, art_pop_fp. fold r chp. clear - Hr Hchp. zsub.
- exact G1F.
- exact A1F.
- apply (art_region_rep_upd spb ris c (2 ^ 60) 0 cl1 (art_cls_take n cl1) M1 MF [(r + 16, 8); (chp, 64); (r + 72, 8); (r, 8)]);
try reflexivity; fold r fa; cbn [art_cls_take cl_free cl_na]; fold k; rewrite ?Lfn.
+ lia.
+ lia.
+ lia.
+ lia.
+ exact Hnf.
+ lia.
+ intros j Hj. rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
+ exact RR1.
+ exact G1F.
+ exact A1F.
+ zgap.
+ zgap.
+ zgap.
+ exact Cmx'.
+ ztr.
+ apply art_cell_mod_add. rewrite Lws in Cna'. exact Cna'.
- intros j Hj. cbn [art_cls_take cl_cache]. fold k ws. apply Cch. rewrite Lws. exact Hj.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_gfa_aruns := (ltac2:(TCodec.tc2 tcn__JatClsGfa2 "];'4'Q2%211'H!p021p041&Iy5'S:yR0%211%5241'7y8%611%311p061'D'Q6'5&QBr6%211&R4r?+V@%3221&R7+R@r7%3221%8251+@%:221'=&QOrF(S8+1(;%33Q121%6251rC%93Q121&Q5rD%211rH+2%<3Q:1:%?231&S9%12Q;7%C3Q;31rI+4%C3QA1A%F231rA%82QB1%J3QB31rJ+:%J3QH1H%M231+QVmdH%?2QI1%Q13QI31rK+;%Q13QO1O%Q4231rE+Rf@%QC221%H2R21%Q:3R251rL+<%Q:3R81Q8%Q=231r>%O2R91%QA3R931rM+=%QA3R?1Q?%QD231r8%Q62R@1%QH3R@31rN+>%QH3RF1QF%QK231&R8r:%211%Q?2RI1%R13RI51'<&R5%12R0Q<+N%32Q>1%5231&R:+d0%22O1%82Q91&R6&R9+Q?%22R11%42N1&Q?rG%28Q1Q8QAQHR61RAQ=&Q1&R2rQ2rO%@21?%54431@rQ3+TP0%8472Q31&Q@rQ4%23R4R;1&QNrQ5%211&QMrQ6rQ0rQ1%463@Q>QE21&QCzrQ7%36QIR0R@2R51&Q:%12R;S;&QG%11M+XPP0%SH21R?%SB3T331&Q0rQ:+RiH%T12E1u8%55Q3421RFrQ;+Rj0%T62G1%95Q7315RJrQ<+Rg8%T:2E1%=5Q;319RN'1&Q8%12NS1(:%T53421%H1RK%TB21G+S`PPPP0%R6221&Q7&3&QF%11S2%32TO1%RB11&Q9%12Q;S6%TM231%92S81+`PPPP0%RB221rQ>+QoooPP0+XP0%U021R3%U5231+M%R?2T>1%U42QG1%U9241+QPP0%U721QK%U<231%R>4R=<13+^PPPP0%U?261+RPPPP0%RB4RA@21%S5251%S62C1%S72Q01p0Q51&Q>vErQ@&QA%13RAR9T4%53431r2%UA21TE%U22V<U?%UD3V<21r3%UE21U7rQ?%U72VA1%UI3VA31r4%UJ21UErQA%UM3VE21%VH1VI&R3r1(2+3%V03VN1UN+8%V23W01V0+9%V43W21V2+B%V63W41V4+C%V83W61V6+D%V:3W81V8+E%V<3W:1V:+F%V>3W<1V<+G%V@3W>1V>+H%VB3W@1V@+I%VD3WB1VB+J%VF3WD1VD+K%VH3WF1VF(6%11O%M3Q031%N3Q161%O3Q291%Q03Q3<1%Q13Q4?1%Q23Q5B1%Q33Q6E1%Q43Q7H1%Q53Q8K1%Q63Q9N1%Q73Q:Q11%Q83Q;Q41%Q93Q<VD1%Q:3Q=Q81%Q=3Q>Q<1%W<2WBQLrQG%W>21QN%W@3X831p051pW2QD1&R1rQEr5%3221&QK&QJrQCrQ9rQ8%473R0SOT3T821rQF%7321X;rQ=&Q;%12T=U0%TJ63T5T>TI1X7&A%12R4U0%V81RD%X=2WA1%XB2U31u4&C&QE%;2<@%211%44XNRL1U4%TK5UIV@761p0;1pU8XO1%T?2TDU7%XB3TA1T>%V@2U:RC%V82RDSE%VC221r<%XN2SOS:%Y32T11%Y02S2SM%Y5221%Y22SLT5%Y7221%Y821S<u1+WJ%U=5V;:321p0<1pU8YC1p0A1'>r=rQH%YB21UB%UE5VC31UASC%YD23U?%UG5VE51UCSI%YF25U=%UI5VG71UES<%W;231%W<261qVJZ01%<2Z11qUJZ21%>2Z31qUFZ41%@2Z51rQN&0rQM%T:3SLU2QN%33ZK21&R0vRBrQIr;rQJ%554Q9321%;271p0=1p0O1p0QC1p0R21p0R71p0R@1p0RE1p0T;1p0T@1p0TF1pQHZM1pV8[31'Q3vFrQB+Zjl<%Z>3[:1Z</01[:%I5HTG1U6TL%77WOU86IRK51p091p0U61p0U=1p0VH1p0VM1p0W21p0W91p0W?1p0WB1p0WG1p0WM1p0X11p0X51p0X91p0X@1p0XD1p0XJ1p0XO1p0Y61p0Y@1p0YH1p0Z01p0Z:1p0ZB1p0ZJ1p0[21p0[61tTL\1[A1tUL\0[M1pTN\21pVH\41pUH\51pUD\61pU>\71pTJ\81pUN\91pV:\:1pV@\;1pW0\<1pU<\=1pVN\>1pU2\?1pVL\@1pQ@\A1pV>\B1pV4\J1pV<\E1pQF\F1pV6\L1pU@]71pQN]41")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 4%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 5%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 12%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 13%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 14%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 15%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 16%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 17%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 18%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 19%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 20%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_gfa_aruns) 21%nat 0%nat).
Lemma art_gfa_aruns : ltac:(sec_stmt2 constr:(SEC_T_art_gfa_aruns) 22%nat 0%nat).
Proof using Type Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs c km m1 m2 sv cl.
intros n chp
H1 Hret H2 H4 H10 H11 H12 H13 H14 Hc HHI Hsp' GEO W Wt PC L T RR OK Emu Cm1 Cm2 Csv Room EV K.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x691000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
assert (Ac_i : apart ctx 4096 0x10000 (0x691000 - 0x10000)) by (unfold apart; clear - G15; lia).
clear G9 G10 G15 G16.
pose proof PC as (Pspb & Pris & _ & _ & Pmask & _).
pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
pose proof OK as (_ & (Hau0 & Haumu) & Hrem0 & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
destruct (art_refill_need c Hc) as (Hneed & Hn). fold n in Hneed, Hn.
set (r := ris + 128 * c) in *. set (fa := spb + c * 2 ^ 32 + 3758096384) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
assert (Er : r = ris + 128 * c) by reflexivity. assert (Efa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity. assert (Echp : chp = t + 208 + 80 * c + 16) by reflexivity.
destruct (art_clsgfa_lock regs M rom raw sp (t + 2768) c chp (Z.of_nat n) spb ris (512 * qs + 2 ^ 30) H1 H2 H10 H11 H12 H13 H14
ltac:(lia) Hsp' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W|lia|lia]) Wr Pspb Pris Rmx)
as (rL & ML & RUNL & L2 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & L3 & L4 & GL & AL & FL & CmxL).
fold r in L8, L10, AL, CmxL. fold fa in L20.
eapply ar_steps; [exact RUNL|].
assert (RRL : art_region_rep spb ris c (2 ^ 60) cl ML).
{ apply (art_region_rep_upd spb ris c 0 (2 ^ 60) cl cl M ML [(sp - 128, 128); (r, 8)]); try reflexivity; fold r fa nf;
first [ lia | exact RR | exact GL | exact AL | exact CmxL | (intros; reflexivity) | idtac ].
- clear - Er HHI G6 Eris Hc. zgap.
- clear - Er HHI G6 Eris Hc. zgap.
- clear - Er Efa HHI G6 Eris Hc G4 Espb Hnf4 Hmfa1. zgap.
- ztr.
- ztr. }
assert (Hfor' : Forall (art_cptr_ok (AsanTab.class_size c) (cl_au cl)) (cl_free cl)) by (apply Forall_app in Hfor; exact (proj2 Hfor)).
assert (CrdL : cellA ML 0x10400 8 0xafffff00000fffff) by ztr.
assert (WtL : wrA ML t 4096) by (eapply wr_grows; [exact GL|exact Wt]).
assert (AML : art_agree (art_gfa_fp sp t spb ris qs c km) M ML).
{ eapply art_agree_sub; [exact AL|]. unfold art_gfa_fp, art_pop_fp. fold r. clear - Er. zsub. }
assert (Hnf : 0 <= nf) by (unfold nf; lia).
assert (Hkm : 0 <= km) by lia.
destruct (art_cls_needs_populate c cl) eqn:NP.
-
assert (Hlt : (length (cl_free cl) < n)%nat) by (unfold art_cls_needs_populate in NP; apply Nat.ltb_lt in NP; exact NP).
destruct (Room eq_refl) as (Room1 & Room2 & Wsh1 & Wsh2).
assert (Eev : art_refill_events spb c cl = art_pop_events spb c cl) by (unfold art_refill_events, art_pop_events; rewrite NP; reflexivity).
rewrite Eev in EV, K.
pose proof (art_cls_ok_populate c cl Hc OK Room1 Room2) as OK1.
pose proof (art_gfa_popa_fn rL ML rom 1275544 r chp (Z.of_nat n) nf (r + 8) L8 L9 L10 L13 L14 ltac:(lia) ltac:(lia) ltac:(unfold nf; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ztr)) as RUNP.
match type of RUNP with msteps _ _ (mkst ?R _ _ _) => set (rP := R) in RUNP end.
eapply ar_steps; [exact RUNP|].
pose proof G17 as X17. unfold apart in X17.
assert (PCL : art_prim_consts spb ris ML). { eapply art_prim_consts_fp; [exact AL| |exact PC]. intros z Hz. cbn. clear - Hz Er HHI G1 G6 Eris Hc G4. repeat split; lia. }
assert (LL : art_layout ML). { eapply art_layout_fp; [exact AL| |exact L]. intros z Hz. cbn. clear - Hz Er HHI G1 G6 Eris Hc G4. repeat split; lia. }
assert (TL : art_tsd ML tp key tsd ctx t).
{ eapply art_tsd_fp; [exact AL| | |exact G19|exact G20|exact G21|exact G22|exact T].
- intros z Hz. cbn. clear - Hz Er HHI G1 G6 Eris Hc G4. repeat split; lia.
- intros z Hz. cbn. clear - Hz X17 Er HHI G1 G6 G13 G14 Eris Hc G4. repeat split; lia. }
pose proof G11 as X11. unfold apart in X11.
set (Q1 := fun (lg : list aev) (st : machine_state) => exists rQ MQ,
st = mkst rQ (0x56e48 : word) MQ rom /\ lg = log ++ art_pop_events spb c cl
/\ getr rQ 10 = Z_to_bv 64 1 /\ getr rQ 2 = Z_to_bv 64 (sp - 128)
/\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rQ x = getr rP x)
/\ mem_grows ML MQ /\ art_agree (art_pop_fp (sp - 128) t spb ris qs c km) ML MQ
/\ art_region_rep spb ris c (2 ^ 60) (art_cls_populate c cl) MQ
/\ (forall j, 0 <= j < 32768 -> cellA MQ (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250)
/\ (exists m1' m2' sv', cellA MQ (t + 2872) 8 m1' /\ cellA MQ (t + 2880) 8 m2' /\ cellA MQ (t + 2792) 8 sv')).
apply (aruns_bind ASEGS EVOK GR Q1 Q).
+ apply (art_populate_aruns EVOK GR Q1 log rP ML rom (0x56e48 : bv 64)%bv (sp - 128) HI t ctx tp key tsd spb ris qs c km (Z.of_nat n - nf) (2 ^ 60) m1 m2 sv cl
ltac:(unfold rP; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold rP; gres; exact L2) ltac:(unfold rP; gres; rewrite L4; exact H4)
ltac:(unfold rP; gres; reflexivity) ltac:(unfold rP; gres; exact L11) ltac:(unfold rP; gres; exact L12) ltac:(unfold rP; gres; reflexivity)
ltac:(unfold rP; gres; reflexivity)
Hc ltac:(lia) ltac:(lia) GEO ltac:(unfold nf; lia) ltac:(assert (AsanTab.class_size c * (Z.of_nat n - nf) <= AsanTab.class_size c * Z.of_nat n) by (apply Z.mul_le_mono_nonneg_l; [pose proof (art_class_size_facts c Hc); lia|lia]); lia)
ltac:(eapply wr_grows; [exact GL|]; eapply wr_sub; [exact W|lia|lia]) WtL PCL LL TL RRL OK Emu
ltac:(ztr_c ltac:(clear - X11 Er HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb)) ltac:(ztr_c ltac:(clear - X11 Er HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb))
ltac:(ztr_c ltac:(clear - X11 Er HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb))
Room1 Room2 ltac:(eapply wr_grows; [exact GL|exact Wsh1]) ltac:(eapply wr_grows; [exact GL|exact Wsh2]) EV).
intros rQ MQ Q10 Q2 Q1' QK QG QA QRR QSH QST. exists rQ, MQ. repeat (split; [first [reflexivity | assumption]|]). assumption.
+ intros lg st (rQ & MQ & -> & -> & Q10 & Q2 & QK & QG & QA & QRR & QSH & QST).
pose proof QRR as (Qmx & Qnf & _ & _ & _ & _ & _ & _ & _ & _ & Wr' & _ & _). fold r in Qmx, Qnf, Wr'.
unfold art_pop_fp in QA. fold r in QA.
pose proof OK1 as (_ & (Hau1 & Haumu1) & _ & _ & _ & Hmu31 & _ & (_ & Hmfa11) & Hnf41 & Hfor1 & _).
set (cl1 := art_cls_populate c cl) in *. set (nf2 := Z.of_nat (length (cl_free cl1))) in *.
assert (Hnew : Z.of_nat n - nf <= art_cls_new c cl).
{ unfold art_cls_new. apply Z.div_le_lower_bound; [pose proof (art_class_size_facts c Hc); lia|].
assert (AsanTab.class_size c * (Z.of_nat n - nf) <= AsanTab.class_size c * Z.of_nat n) by (apply Z.mul_le_mono_nonneg_l; [pose proof (art_class_size_facts c Hc); lia|lia]). lia. }
assert (Enf2 : nf2 = nf + art_cls_new c cl).
{ unfold nf2, cl1, art_cls_populate. cbn [cl_free]. rewrite length_app, art_carved_length, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
assert (Hnn : (n <= length (cl_free cl1))%nat) by (fold nf2 in Enf2; lia).
pose proof (art_gfa_popb_fn rQ MQ rom r fa chp (Z.of_nat n) nf2 (r + 8) Q10
ltac:(rewrite QK by inl; unfold rP; gres; exact L8) ltac:(rewrite QK by inl; unfold rP; gres; reflexivity)
ltac:(rewrite QK by inl; unfold rP; gres; exact L20) ltac:(rewrite QK by inl; unfold rP; gres; reflexivity) ltac:(rewrite QK by inl; unfold rP; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Wr' Qnf) as RUNB.
match type of RUNB with msteps _ _ (mkst ?R _ ?X _) => set (rB := R) in RUNB; set (MB := X) in RUNB end.
eapply ar_steps; [exact RUNB|].
assert (A1E : art_agree [(r + 16, 8)] MQ MB). { unfold MB. eapply art_agree_sub; [zagree|]. zsub. }
pose proof At_i as Xi. unfold apart in Xi.
apply (art_gfa_tail Q (log ++ art_pop_events spb c cl) regs rB M MQ MB rom raw sp HI t spb ris qs c km n cl1 Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_i Hn Hnn
ltac:(fold nf2; lia) ltac:(apply Forall_app in Hfor1; exact (proj2 Hfor1)) ltac:(lia) QRR
ltac:(ztr_c ltac:(clear - Xi Er HHI Hsp' G1 G2 G6 G7 G8 Eris Hc G4 Espb Emu Hmu3 Hkm)) ltac:(eapply wr_grows; [exact QG|exact WtL])
ltac:(eapply mem_grows_trans; [exact GL|exact QG])
ltac:(eapply art_agree_sub; [eapply art_agree_trans; [exact AL|exact QA]|]; unfold art_gfa_fp, art_pop_fp; fold r; clear - Er; zsub)
ltac:(unfold MB; apply Wn_grows) A1E).
* fold r. unfold MB. replace (Z.of_nat (length (cl_free cl1) - n)) with (nf2 - Z.of_nat n) by (unfold nf2; lia). apply cell_Wn_hit; [lia|cbn; lia].
* pose proof (art_agree_trans _ _ ML MQ MB QA A1E) as AQB.
eapply (art_gfa_fcells_tr _ ML MB); [exact AQB| |lia|lia|exact FL].
clear - Er HHI Hsp' G1 G2 G6 G7 G8 Eris Hc G4 Espb Emu Hmu3 Hkm. zgap.
* unfold rB; gres. exact Q2.
* unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L8.
* unfold rB; gres. fold chp. f_equal. lia.
* unfold rB; gres. reflexivity.
* unfold rB; gres. reflexivity.
* unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L19.
* unfold rB; gres. fold fa. f_equal. unfold nf2. lia.
* unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L3.
* unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L4.
* intros regs' M' P10 P2 P1 PK PG PA PG1 PA1 PR PC'. apply (K regs' M' P10 P2 P1 PK PG PA).
-- unfold art_cls_refill. rewrite NP. exact PR.
-- unfold art_cls_refill. rewrite NP. exact PC'.
-- intros _ j Hj. pose proof (QSH j Hj) as C. fold r chp in PA1. pose proof At_s as Xs. unfold apart in Xs.
ztr_c ltac:(clear - Hj Xs Er Echp HHI Hsp' G1 G2 G6 G7 G8 Eris Hc G4 Espb Emu Hmu3 Hkm).
-- destruct QST as (m1' & m2' & sv' & S1 & S2 & S3). exists m1', m2', sv'. fold r chp in PA1.
repeat split; ztr_c ltac:(clear - X11 Er Echp HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb).
-
assert (Hnn : (n <= length (cl_free cl))%nat) by (unfold art_cls_needs_populate in NP; apply Nat.ltb_ge in NP; exact NP).
unfold art_refill_events in K. rewrite NP in K. rewrite app_nil_r in K.
pose proof (art_gfa_mid_fn rL ML rom r fa chp (Z.of_nat n) nf L8 L20 L13 L14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold nf; lia) ltac:(lia)
ltac:(eapply wr_grows; [exact GL|exact Wr]) ltac:(ztr)) as RUNM.
match type of RUNM with msteps _ _ (mkst ?R _ ?X _) => set (rM := R) in RUNM; set (MM := X) in RUNM end.
eapply ar_steps; [exact RUNM|].
assert (A1E : art_agree [(r + 16, 8)] ML MM). { unfold MM. eapply art_agree_sub; [zagree|]. zsub. }
apply (art_gfa_tail Q log regs rM M ML MM rom raw sp HI t spb ris qs c km n cl Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_i Hn Hnn ltac:(fold nf; lia) Hfor' ltac:(lia)
RRL CrdL WtL GL AML ltac:(unfold MM; apply Wn_grows) A1E).
+ fold r. unfold MM. replace (Z.of_nat (length (cl_free cl) - n)) with (nf - Z.of_nat n) by (unfold nf; lia). apply cell_Wn_hit; [lia|cbn; lia].
+ eapply (art_gfa_fcells_tr [(r + 16, 8)] ML MM); [exact A1E| |lia|lia|exact FL]. clear - Er HHI G6 Eris Hc. zgap.
+ unfold rM; gres. exact L2.
+ unfold rM; gres. exact L8.
+ unfold rM; gres. fold chp. f_equal. lia.
+ unfold rM; gres. exact L13.
+ unfold rM; gres. exact L14.
+ unfold rM; gres. exact L19.
+ unfold rM; gres. fold fa. f_equal. unfold nf. lia.
+ unfold rM; gres. exact L3.
+ unfold rM; gres. exact L4.
+ intros regs' M' P10 P2 P1 PK PG PA PG1 PA1 PR PC'. apply (K regs' M' P10 P2 P1 PK PG PA).
* unfold art_cls_refill. rewrite NP. exact PR.
* unfold art_cls_refill. rewrite NP. exact PC'.
* intros X. discriminate X.
* exists m1, m2, sv. fold r chp in PA1. pose proof G11 as X. unfold apart in X.
repeat split; ztr_c ltac:(clear - X Er Echp HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb).
Qed.
End SE.
End Spec.
