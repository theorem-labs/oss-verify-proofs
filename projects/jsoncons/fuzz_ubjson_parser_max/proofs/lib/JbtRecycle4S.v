(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtFree1 JbtCellEx JbtCls JbtSecAllocPost
JbtRecycle1 JbtRecycle2C JbtRecycle3 JbtRecycle4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle4S () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle2C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle4S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtSecAllocPost."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2or"]; ["3sub"; "4map"; "4nth"; "5Z"; "0EVOK"; "0GR"; "0HI"; "6machine_state"; "7bvmap"; "0M"; "0M'"; "0Q"; "8apart"; "8cell"; "8wr"; "9AMunmap"]; ["9aev"; "9aruns"; ":ret_ok"; ";art_evok_list"; "<art_agree"; "<art_gap"; "=art_tsd"; ">SB"; ">art_layout"; ">kHighMemBeg"; "?art_gbb_scan"; "@art_flush_events"; "@art_sec_cells"; "@art_sec_geo"; "@art_swap_remove"; "Aart_cbr_sec_fp"]; ["Bappmem"; "Cgetr"; "Cmkst"; "Dmem_grows"; "Eloaded_segments"; "FIn"; "Fnth_error"; "Gadd"; "Gdiv"; "Gle"; "Glt"; "Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0W"]; ["0a"; "0b"; "0b1"; "0bl"; "0cb"; "0ctx"; "0f1"; "0f2"; "0fx"; "0idx"; "0k"; "0key"; "0log"; "0m"; "0mb"; "0ms"]; ["0n"; "0parr"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; "0spb"; "HBV"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0t"; "0tp"; "0tsd"]; ["0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_cbr_sec_fp (sp t parr idx last mb ms : Z) : list (Z * Z) :=
[ (sp - 80, 80); (t + 2800 + 40, 16) ] ++ art_secd_fp sp t parr idx last mb ms.
Lemma art_sec_scan : ltac2:(TCodec.tc2 tcn__JbtRecycle4S "QE'C'6';%1233%311'7&Q=r9r8r7r6r5%6554321'>'9%11<&QF%13>76(1(:r4r3%34FF21%52D1%;3971'=&QI%12@6&QJ&QG%12C:%32:1%7251&Q:z&A&4%12Q5Q5%34Q3Q61N%63C51%K3Q81Np091p0B1p0O1pTLQ<1pU0Q=1pTNQ>1pTDQ:1pT8Q<1pU4QA1pT<QB1pULQC1pQ>QD1").
Proof.
intros HI t ctx parr bl idx mb ms m (_ & _ & _ & _ & _ & _ & GB & GD) Hnth Hm.
pose proof (nth_error_In _ _ Hnth) as Hin.
destruct (GB _ Hin) as (_ & _ & _ & Hmb & _). cbn [fst snd] in Hmb.
apply art_gbb_scan_is.
- left. apply in_map_iff. exists (mb, ms). split; [reflexivity|exact Hin].
- lia.
- lia.
- intros ch Hch Hle. apply in_map_iff in Hch. destruct Hch as (b' & <- & Hin').
destruct (In_nth_error _ _ Hin') as (j & Hj).
destruct (Nat.eq_dec idx j) as [->|NE].
+ rewrite Hnth in Hj. injection Hj as <-. cbn. lia.
+ pose proof (GD idx j (mb, ms) b' Hnth Hj NE) as Ap. destruct (GB _ Hin') as (_ & _ & Hs & _). unfold apart in Ap. cbn [fst snd] in Ap. lia.
Qed.
Lemma art_sec_cells_tr : ltac2:(TCodec.tc2 tcn__JbtRecycle4S "RG'6';'C%2211%411'RKyR0%211'9y8%511%311p051&Q=r5r4r3r2r1%6554321&QJr6&QM+2+Q?%3221%6251&QCr9r8%3221&Q4r;r:%33216&Q5r<+QWUPH+c8%43321&M&QD&QG%1265u4z%655>321r>&QK+8&QL&5r7%22QB1%411%7261%E39K1&QE%13QGQ8NrA&4%13QKQKQ<+Q0%L3421p061pT4QN1&Q<r?%231Q3Q8%332Q5Q4p021p061p0@1p0K1p0Q31p0Q91p0Q>1p0QC1p0QK1pT8R;1pU4R>1pT<R?1pULR@1pQ>RA1pQFR81pQDR91pT0RB1").
Proof.
intros W M M' HI t ctx parr bl (Gp1 & Gp2 & Gp3 & _ & _ & _ & GB & _) HHI G A G0 CL GP GBk (C1 & C2 & C3 & _ & WP & CB).
unfold art_sec_cells.
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact C1]. }
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact C2]. }
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact C3]. }
split; [exact CL|]. split; [eapply wr_grows; [exact G|exact WP]|].
intros j b Hj. destruct (CB j b Hj) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (nth_error_In _ _ Hj) as Hin. destruct (GB _ Hin) as (_ & _ & Hs & Hb0 & Hb1 & _).
assert (Hjl : (j < length bl)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
pose proof (proj1 (Nat2Z.inj_lt _ _) Hjl) as Hjl'.
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact GP|lia|cbn; lia]|lia|cbn; lia|exact B1]. }
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact (GBk b Hin)|lia|cbn; lia]|lia|cbn; lia|exact B2]. }
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact (GBk b Hin)|lia|cbn; lia]|lia|cbn; lia|exact B3]. }
split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact (GBk b Hin)|lia|cbn; lia]|lia|cbn; lia|exact B4]. }
split; [eapply wr_grows; [exact G|exact B5]|eapply wr_grows; [exact G|exact B6]].
Qed.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_cbr_sec_aruns := (ltac2:(TCodec.tc2 tcn__JbtRecycle4S "^I'6'Q0%211'G!p021p041&Hy5'RKyR0%211%5241'9y8%611%311p061'C';%1222%E11'7'>&QArG(RI+1(<%33E21%6251rD%93E21&Q2rE%211rI+2%<3N1:%?231&RJ%12O7%C3O31rJ+4%C3Q51A%F231%72Q5@%I3Q521rK+:%I3Q;1G%L231r@%>2Q<1%Q03Q<31rL+;%Q03QB1N%Q3231r<%E2QC1%Q73QC31&QI&Q9rH%3221&QN+S0%22J1%72Q21&QJ&QM+Q?%22Q51%42J1&N&QDrO%<2G;%44321<'=zrF%E221+R0%>2QA1%@241%7241+Vb\P0%K217&QG+Q5%E2QH1%32R51%H21E&MrQ3+QWTnH+Q0%9221u8%65I521Q5%RJ1RC&QFr?%23RFQE1(1(:%14RKRKRDJ%32RJ1%RH3851&Q<rQ5rA%332R?1&Q=rQ2rMrNrB%55432R>1&L%14R@RGR3N+TP0%Q22R<1%QO21RJ+@%Q52RE1%Q62R9R@%R3221%R42QARH+X0%QN2RJ1%QE231%QO2S2Q4%R12RM1%QH261rQ<u4+3&QK%12:RF%QD231%Q@5R36J51rQ=%QG2KS6%QC5R6218RK&Q8rQ>%211&Q6rQ?rQ:rQ9rQ8rQ7rQ6%76654321%S02Q33%R525Q4%S221@&Q@%129Q7'?%R:2<Q9+RPP0%S8221%S92R??%5221rQDrQ;%S04RO21Q@%S>2QAL%RC2IQBrQB%SA221%?2IQErQ@%RH21QG%SE21>%SF2RL3%B221rQA%QN46QL1QL+V[jY8rQE+RH%SI221%SN241rQF+8%S5221%T221S8%T3298+QP0%S9261%T621S<rQN+QV`l0+QiaW0%S95SL32S41rQO%S;5SN13S6R?rR0+QV`o0%S>5T121S9UCrR1+Qii[8+T@%SG221%SC5T641S>T1rR2rQI+Rg@%SL221+Q8%SN221%SJ5T=61SEQ8rR3rQJ%T2217+Q@%T4221%T05TC51SKQ>&Q3vDrR6&2&Q;rQG%221Q9(3(O%124Q<(8%11W;%53W<31%:3W=71%>3=<1r2%VI21VDrR5%VL3W821r3%VM21V?%V>2W<4%W03W<21%W?1W@&QEr1%W13WCS?VO%W23WDQMW0+9%W43WF1W2+B%W63WH1W4+C%W83WJ1W6+D%W:3WL1W8+E%W<3WN1W:+F%W>3X01W<+G%W@3X21W>+H%WB3X41W@+I%WD3X61WB+J%WF3X81WD+K%WH3X:1WF%Q81K%Q<3L21%Q=3M51%Q>3N81%Q?3O;1%Q@3Q0>1%QA3Q1A1%QB3Q2D1%QC3Q3G1%QD3Q4J1%QE3Q5M1%QF3Q6Q01%QG3Q7Q31%QH3Q8WC1%QI3Q9Q61%Q93Q:Q81r6%X<21QDrR<%X>21QF%X@3XL31p061pU6QA1&Q4&Q?rR7&QL%11SD&4&B&@&5%12XOSEu1%4221%V:4Y4Y4W4W4%74Y32SI1%93Y6Y61rQMrQL%@7?S<SE=321rR:r4%D3321&RL%12YFR6%X22SG1%W72SHSL%WL231%WC231r7%11RF(0%11YI%YB3YI31p061pV2Z01&Q7&QH%12T2T?%WD231%XA21@%42T7TB%WG231%X<2C1%X3241r8%11S6%Y?2Z9X5%W=2Z91%Z23Z931p061pV2Z@1%XM2X:S<%X22S9S=%XG21X8rR4%W641T5Q3S<rRBr5%XG4XF21Q6r=%XI4XH1R23p031p071p0:1p0=1pTFZH1pT2ZI1&Q>%14ZIQGTHTA%WN3ITJ1rRA%T;2TLU1%T82TMU2%T:3[A1T6%T?3[B31%T@3[C51&QBvR8r:rR=r9rR>%6554321%K281p0?1p0C1p0Q41p0QE1p0R31p0RI1p0T<1p0TA1pQF[D1pU<[J1'Q1vErR9rR8+Z`^4%[B3\21[@/01\2%I5HS21U;TL%87Z2U=7I651p0:1p0U21p0UB1p0UI1p0V11p0V71p0V;1p0V>1p0VC1p0VG1p0VI1p0VN1p0W41p0W71p0W=1p0W?1p0WC1p0WE1p0WI1p0X01p0X31p0X61p0X81p0XA1p0XE1p0XI1p0Y11p0Y51p0Y:1p0Y?1p0YC1p0YF1p0YM1p0Z21p0Z<1p0ZD1p0ZJ1p0ZM1p0[61p0[<1p0[B1p0[G1p0[L1p0\41p0\<1p0\C1p0\K1p0\O1pTD]:1pT8]<1pT@]@1pT>]A1pU2]B1pT6]C1pTL]D1pU0]E1pTN]F1pU4]G1pUB]H1pT:]I1pUL]J1pT<]K1pV0]L1pTH]M1pUN]N1pQ>]O1pU@^01pU8^81pU>^31pQD^41pU:^:1pTJ^E1pQH^B1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 4%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 5%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 7%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 8%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 9%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 10%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 11%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 12%nat 0%nat).
Variable cb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 13%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 14%nat 0%nat).
Variable parr : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 15%nat 0%nat).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 16%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 17%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 18%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 19%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 20%nat 0%nat).
Variable f1 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 21%nat 0%nat).
Variable f2 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 22%nat 0%nat).
Variable bl : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 23%nat 0%nat).
Variable idx : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sec_aruns) 24%nat 0%nat).
Theorem art_cbr_sec_aruns : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_sec_aruns) 25%nat 0%nat).
Proof using Type Q log regs M rom raw sp HI tp key tsd ctx t cb spb parr mb ms m b1 n f1 f2 bl idx.
intros
H1 Hret H2 H4 H10 H11 HHI0 HHI Hsp' W Hcb Hspb Hspb' Cspb Hnth SC GEO Abk Hm1 Hm2 Hb1 Hn Chw Cn LAY TSD Ht Ht' Apt Gti Wt Hctx Hctx' Apc Gci Atc
Htp Htp' Htsd Htsd' Cpc Cpg Cgot Cmm Cf1 Cf2 EV K.
unfold kHighMemBeg in HHI0.
pose proof GEO as (Gp1 & Gp2 & Gp3 & Gp4 & Apt' & Apc' & GB & GD).
pose proof (nth_error_In _ _ Hnth) as Hin.
destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & Hmb3 & Abp & Abt & Abc). cbn [fst snd] in Hmb4k, Hms4k, Hmb0, Hmb1, Hmb2, Hmb3, Abp, Abt, Abc.
assert (Hmb4 : 0 <= mb) by lia.
assert (Hlen1 : 1 <= Z.of_nat (length bl)). { assert ((idx < length bl)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
pose proof TSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
pose proof SC as (S1 & S2 & S3 & S4 & SWP & SB_).
destruct (SB_ idx (mb, ms) Hnth) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [fst snd] in B1, B2, B3, B4, B5, B6.
assert (At_i : apart t 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; lia). clear Gti.
assert (Ac_i : apart ctx 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; lia). clear Gci.
assert (Hsec : m < spb \/ spb + 2 ^ 37 <= m) by (unfold apart in Abk; lia).
assert (Hsech : mb + 4096 < spb \/ spb + 2 ^ 37 <= mb + 4096) by (unfold apart in Abk; lia).
destruct (art_cbr_sa regs M rom raw sp cb m spb H1 H2 H10 H11 ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]) Hcb ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hspb Hspb' Hsec Cspb)
as (r1 & RUN1 & A1 & A2 & A8 & A9 & A19 & A20 & A10 & A11 & AK).
destruct (art_f48_facts M sp raw regs ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G01 & AG01).
destruct (art_f48_cells M sp raw regs ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (E1 & E8 & E9 & E18 & E19 & E20).
set (M1 := art_f48 M sp raw regs) in *. clearbody M1.
assert (T1 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 48) 48 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M1 a k v).
{ intros a k v Ap Ha Hk C. apply (art_cell_tr _ M M1 a k v AG01); [cbn [art_gap fst snd]; split; [exact Ap|exact I]|exact Ha|exact Hk|exact C]. }
assert (Lchs : length (map fst bl) = length bl) by apply length_map.
assert (Cchs : forall j, (j < length (map fst bl))%nat -> 0 <= nth j (map fst bl) 0 < 2 ^ 64 /\ cellA M1 (parr + 8 * Z.of_nat j) 8 (nth j (map fst bl) 0)).
{ intros j Hj. rewrite Lchs in Hj.
assert (En : nth j (map fst bl) 0 = fst (nth j bl (0, 0))) by (exact (map_nth fst bl (0, 0) j)). rewrite En.
pose proof (nth_error_nth' bl (0, 0) Hj) as Hj'. pose proof (nth_error_In _ _ Hj') as Hinj.
destruct (GB _ Hinj) as (_ & _ & Hs & Hb0 & Hb1' & _). destruct (SB_ j _ Hj') as (X1 & _).
pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hjz.
split; [clear - Hb0 Hb1' Hs HHI Hsp'; lia|]. apply T1; [unfold apart; cbn; clear - Hjz Gp2 HHI; lia|clear - Gp1; lia|cbn; clear - Hjz Gp2 HHI Hsp'; lia|exact X1]. }
destruct (art_gbb_run (map fst bl) r1 M1 rom (0x5423c : bv 64)%bv (sp - 48) HI m parr mb mb ms A1 ltac:(unfold ret_ok; bveq) A2 A10 A11
ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G01|]; eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)])
ltac:(rewrite Lchs; clear - Hlen1; lia) ltac:(rewrite Lchs; exact Gp3) Gp1 ltac:(rewrite Lchs; exact Gp2) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))
ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S4]) ltac:(rewrite Lchs; apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S3]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S2]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S1])
Cchs ltac:(symmetry; apply (art_sec_scan HI t ctx parr bl idx mb ms m GEO Hnth); (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hmb4k
ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact B2]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact B3]) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)))
as (r2 & RUN2 & B10 & B2' & BK).
destruct (art_gbb_mem_facts M1 (sp - 48) (0x5423c : bv 64)%bv r1 ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G12 & AG12 & CL2).
set (M2 := art_gbb_mem M1 (sp - 48) (0x5423c : bv 64)%bv r1) in *. clearbody M2.
replace (sp - 48 - 32) with (sp - 80) in AG12 by (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia).
assert (G02 : mem_grows M M2) by (eapply mem_grows_trans; [exact G01|exact G12]).
assert (AG02 : art_agree [(sp - 48, 48); (sp - 80, 32); (0x139418 + 616, 4)] M M2).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact AG01|exact AG12]|]. intros z Hz H. exact H. }
assert (T02 : forall a (k : nat) v, art_gap [(sp - 48, 48); (sp - 80, 32); (0x139418 + 616, 4)] a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M2 a k v).
{ intros a k v Gp Ha Hk C. apply (art_cell_tr _ M M2 a k v AG02 Gp Ha Hk C). }
destruct (art_cbr_sb r2 M2 rom spb (mb + 4096) B10 ltac:(rewrite BK by inl; exact A19) ltac:(rewrite BK by inl; exact A20) Hspb Hspb' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hsech
ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cspb]))
as (r3 & RUN3 & C18 & CK).
pose proof (art_cell_norm _ _ _ _ Cf1) as Cf1n. pose proof (art_mod64_range f1) as Hf1n.
pose proof (art_cell_norm _ _ _ _ Cf2) as Cf2n. pose proof (art_mod64_range f2) as Hf2n.
assert (Chi : cellA M (m + 2) 2 0).
{ destruct (cell4_split M m (3 + 256 * b1) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Chw) as (_ & _ & X). replace ((3 + 256 * b1) / 65536) with 0 in X by (symmetry; apply Z.div_small; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)). exact X. }
assert (TSD2 : art_tsd M2 tp key tsd ctx t).
{ apply (art_tsd_tr _ M M2 tp key tsd ctx t AG02); [| | | |exact TSD]; cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ac_i; unfold apart in *; cbn in *; lia)]. }
destruct (art_cbr_stats r3 M2 rom (sp - 48) HI tp key tsd ctx t m n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64)
ltac:(rewrite CK by inl; exact B2')
ltac:(rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4)
ltac:(rewrite CK by inl; rewrite BK by inl; exact A9)
ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G02|]; eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)])
TSD2 Ht Ht' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G02|exact Wt])
ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hn Hf1n Hf2n
ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Chi])
ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cn])
ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cf1n])
ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cf2n]))
as (r4 & RUN4 & DK).
destruct (art_cbr_stats_mem_facts M2 (sp - 48) t n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G23 & AG23).
set (M3 := art_cbr_stats_mem M2 (sp - 48) t n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64)) in *. clearbody M3.
replace (sp - 48 - 32) with (sp - 80) in AG23 by (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia).
assert (G03 : mem_grows M M3) by (eapply mem_grows_trans; [exact G02|exact G23]).
assert (AG03 : art_agree [(sp - 48, 48); (sp - 80, 32); (0x139418 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] M M3).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact AG02|exact AG23]|]. intros z Hz H. exact H. }
assert (AG13 : art_agree [(sp - 80, 32); (0x139418 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] M1 M3).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact AG12|exact AG23]|]. intros z Hz H. exact H. }
assert (TF : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA M1 a 8 v -> cellA M3 a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_tr _ M1 M3 a 8 v AG13); [|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)|exact C].
cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)]. }
assert (T03 : forall a (k : nat) v, art_gap [(sp - 48, 48); (sp - 80, 32); (0x139418 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] a (Z.of_nat k) ->
0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M3 a k v).
{ intros a k v Gp Ha Hk C. apply (art_cell_tr _ M M3 a k v AG03 Gp Ha Hk C). }
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Q8r. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Q9r. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Q18r.
pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Q19r. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Q20r.
change (bv_modulus 64) with (2 ^ 64) in Q8r, Q9r, Q18r, Q19r, Q20r.
destruct (art_cbr_tails r4 M3 rom raw sp spb (mb + 4096) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
ltac:(rewrite DK by inl; rewrite CK by inl; exact B2')
ltac:(rewrite DK by inl; exact C18)
ltac:(rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; exact A19)
ltac:(rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; exact A20)
ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hspb Hspb' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hsech
ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cspb])
ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E1]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E8]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E9])
ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E18]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E19]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E20]))
as (r5 & RUN5 & V1 & V2 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & VK).
eapply ar_steps.
{ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|exact RUN5]. }
assert (SC3 : art_sec_cells M3 parr bl).
{ apply (art_sec_cells_tr _ M M3 HI t ctx parr bl GEO ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) G03 AG03); [| | | |exact SC].
- cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)].
- apply (art_cell_tr _ M2 M3 _ _ _ AG23); [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact CL2].
- cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Apt'; unfold apart in *; cbn in *; lia)].
- intros b Hb. destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & _ & _ & Hbt & _).
cbn [art_gap fst snd]. repeat split; first [exact I|(clear - Hs Hb0 Hb1' Hbt HHI Hsp' Ht Ht'; unfold apart in *; cbn in *; lia)]. }
assert (LAY3 : art_layout M3).
{ apply (art_layout_tr _ M M3 AG03); [| | |exact LAY]; cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]. }
assert (TSD3 : art_tsd M3 tp key tsd ctx t).
{ apply (art_tsd_tr _ M M3 tp key tsd ctx t AG03); [| | | |exact TSD]; cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i Ac_i Atc; unfold apart in *; cbn in *; lia)]. }
apply (art_secd_aruns EVOK GR Q log r5 M3 rom raw sp HI tp key tsd ctx t parr mb ms bl idx V1 Hret V2
ltac:(rewrite VK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4) V10 V11 V12
ltac:(unfold kHighMemBeg; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) HHI Hsp' ltac:(eapply wr_grows; [exact G03|exact W]) Hnth SC3 GEO LAY3 TSD3 Ht Ht' Apt
ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)) ltac:(eapply wr_grows; [exact G03|exact Wt]) Hctx Hctx' Apc ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ac_i; unfold apart in *; cbn in *; lia)) Atc Htp Htp' Htsd Htsd'
ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cpc])
ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cpg])
ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cgot])
ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cmm]) EV).
intros r6 M6 F1 F2 FK FA FN FS FW FSC.
apply (K r6 M6 F1 F2).
- intros x Hx. rewrite (FK x Hx). cbn [In] in Hx.
destruct Hx as [<-|Hx]. { rewrite VK by inl. rewrite DK by inl. rewrite CK by inl. rewrite BK by inl. apply AK. inl. }
destruct Hx as [<-|Hx]. { rewrite VK by inl. rewrite DK by inl. rewrite CK by inl. rewrite BK by inl. apply AK. inl. }
destruct Hx as [<-|Hx]. { rewrite V8. apply Z_to_bv_bv_unsigned. }
destruct Hx as [<-|Hx]. { rewrite V9. apply Z_to_bv_bv_unsigned. }
destruct Hx as [<-|Hx]. { rewrite V18. apply Z_to_bv_bv_unsigned. }
destruct Hx as [<-|Hx]. { rewrite V19. apply Z_to_bv_bv_unsigned. }
destruct Hx as [<-|Hx]. { rewrite V20. apply Z_to_bv_bv_unsigned. }
repeat (destruct Hx as [<-|Hx]; [rewrite VK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; apply AK; inl|]).
destruct Hx.
- eapply art_agree_sub; [eapply art_agree_trans; [exact AG03|exact FA]|]. unfold art_cbr_sec_fp, art_secd_fp.
intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; (clear - H Hz; lia).
- exact FN.
- exact FS.
- intros a k Ha Hk Ap Wa. apply (FW a k Ha Hk Ap). eapply wr_grows; [exact G03|exact Wa].
- exact FSC.
Qed.
End SE.
End Spec.
