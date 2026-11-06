(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W9 ASlot_W13 ASlot_W14 ASlot_M4P.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_M5P () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M4P."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_M5P.CEIL_WRAP_1.NEST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W13."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Bool.Bool."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.list_basics.list."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1bool"; "1fst"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3N"; "3Z"; "4sm_rec"; "5nt_stT"; "5nt_stW"; "5nt_written"; "6pp"; "7rdv"; "8meta_slot"; "8ticks_ok"; "9mem"; "9pans_mem"; ":grp_hdr_cov"; ":slot_ok"; ";Known"; ";RKGroup"]; [";UNIT"; ";Unknown"; ";active"; ";aptr"; ";area"; ";cell_read"; ";cellval"; ";conc"; ";ctx"; ";get_meta_rec"; ";get_shadow"; ";get_stride"; ";ghdr"; ";hav_add"; ";hdr_havoc"; ";m_mem"]; [";m_set_maplen"; ";mctx"; ";meta"; ";mkMeta"; ";mstate"; ";nest_layout"; ";optr"; ";put_meta"; ";r_cells"; ";r_hav"; ";r_havp"; ";r_kind"; ";r_len"; ";region"; ";rkind"; ";round_up_pg"]; [";s_areas"; ";s_ctx"; ";s_groups"; ";s_metas"; ";s_next_rid"; ";s_regions"; ";s_reserved"; ";s_shadow"; ";s_slots"; ";s_tick"; ";shadow"; ";size_class"; ";stale"; ";upd_meta"; ";usage"; ";wr8"]; [";zero_hdrs"; "<Is_true"; "=existsb"; ">lt"; "?add"; "?div"; "?land"; "?le"; "?lt"; "?ltb"; "?modulo"; "?mul"; "?of_nat"; "?sub"; "0T"; "0X"]; ["0b"; "0b'"; "0bb"; "0c"; "0ch"; "0cnt"; "0f"; "0g"; "0gh"; "0h"; "0hl"; "0i"; "0idx"; "0j"; "0jn"; "0k"]; ["0l"; "0m"; "0mm"; "0o"; "0off"; "0p"; "0q"; "0r"; "0req"; "0rid"; "0s"; "0sc"; "0st"; "0st'"; "0st1"; "0st3"]; ["0stF"; "@filter"; "@lookup"; "AN_countable"; "AZ_countable"; "Aprod_countable"; "BIs_true_dec"; "Bprod_eq_dec"; "Cgmap"; "Cgmap_lookup"; "Dlist_filter"; "Eeq_dec"; "Feq_dec"; "0strideg"; "0szc"; "0t"]; ["0u"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma wr8_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "RB&Q3'A'QD';'<'T8'@&T;&T3'QM%544321&R5&R?r3r2r1%43321%611%713%?3921&T7&T<%24@?E1&T5&T4%26CBAH41'Q<%F4K521&R2%11=%21?%K3421'Q4%L4Q1;81&R0%11C%21E%Q13421&R9%11G%21I%Q53Q321&R4%11K%21M%Q93Q721'4'8%12Q?Q?%311&R6%11Q3%21Q5%QA3421'QA&R1%11Q8%21Q:%QF3421%<2QKQJ%QG4QLQ6Q31&R8%11Q>%21Q@%QL3421'QB%QM4R2Q<Q91&R3%11QD%21QF%R23421%R4271%R52>1%R62D1%R72M1%R82Q21%R92Q71%R:2Q>1%R;2QK1pWJR=1pY4R?1pW>RA1").
Proof. intros q v st. repeat split; reflexivity. Qed.
Lemma cells_wr8_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q<'QD'8'@'A%3221&>'<r1&9r3%23871%53841%711'6%=2;<%211&T2'T8&T<&T4%34A216&T9%14C438r2&QH&Q:&R?r4r5%332D1&3%13ML4%7231%911%B6OD><;1%:274%<11%E6Q2GA?>1%Q03G41p0K1pW8Q51pY4Q61pW>Q61pWJQ;1").
Proof. intros st q v o. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma cells_wr8_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q;'QD'8'@'A%3221'<'6%6245%211&T2'T8&T<&T4%34:216&T9%14<438&9r2%23@?1&QH&Q:&R?r1r3%33721&3%13HG9%7231%911%D6JF@>;1(1(7&RF+WO%22<1&R9%11=%64Q2Q331%82O1%Q23O:1pY4Q51pW>Q51pWJQ:1").
Proof. intros st q v. rewrite get_shadow_wr8_same. cbn [r_cells]. apply lookup_insert_eq. Qed.
Lemma hav_wr8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q5'QD&Q3'A';'<'T8&T<&T4'4'8'@%2291%411%84;761&QI&Q:&R?r2r1r3%43321&3%13<D5%8231%:11%:263%<11%G3>31%G4JFEB&QJ%117%216%L3421%N261pY4Q01pW>Q21pWJQ41").
Proof. intros st q v. rewrite get_shadow_wr8_same. split; reflexivity. Qed.
Lemma cells_wr8_other' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q;'QD'@'A&>'<r1r3%33521%511'6'8%129:%311&T2'T8&T<&T4%34?216&T9%14A438r2&QH&Q:&R?(7r5r4%34JI21r6%632G1%8215%:11%C6NE?=<1%;258%=11%F6Q1HB@?1%Q03H41p0M1pW8Q41pY4Q51pW:Q61pWDQ81pWJQ:1").
Proof. intros st rid off v o. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.
Lemma hav_wr8_any : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "N'QD&Q3'A'@'<'T8&T<&T4'4'8%1287%311%74:651&QI&Q:&R?r3r2r4%43321r1%7221%911%9253%;11%E3=31pWDG1pY4I1pW>K1pWJM1").
Proof. intros st q v rid. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.
Lemma havp_wr8_any : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "J'QD&Q3'A'@'<'T8&T<&T4%346215&QJ&Q:&R?r3r2r4%43321r1%7221%911%9253%;11%A3=31pWDC1pY4E1pW>G1pWJI1").
Proof. intros st q v rid. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.
Lemma shadow_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "D'QD&Q3'QB'@'<'R:&Q:&QGr3r2r4%43321r1%7221%8242%;3:21pWD=1pW@?1pW4A1pWJC1").
Proof. intros st m r rid. reflexivity. Qed.
Lemma cell_read_wr8_other' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "O'QD'@'A&>'<r1r3%33521%511'Q6&Q5&Q:&R?(7r5r4%34?>21r6%632<1%8215r2%;221%;258%=213%D3?31p0A1pW8H1pY4I1pW:J1pWDL1pWJN1").
Proof. intros st rid off v o. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.
Lemma cell_read_wr8_same' : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q5'QD'@'A&Ir4%211';&RGzr2%3221&RH+X0%2241%8241'<'Q6&Q5&Q:&R?(7r5%24ED1Br3r6%63321%8215%:21G(N%116%?3>31p0A1p0K1pY4O1pW:Q01pWDQ21pWJQ41").
Proof. intros st rid off v. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.
Lemma cell_read_wr8_same_land : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "N'QD'@'A&Ir4%211'<'Q6&Q5&Q:&R?(7r3%24<;91r2r5%63321%821=%:216(N&RF+WO%2281%411%B3A61p0D1pY4H1pW:I1pWDK1pWJM1").
Proof. intros st rid off v.
intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
- apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.
Lemma ticks_ok_same2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "K'QD'<'T8'@&T;&T3'R:%544321&R7r1%211r2%411%<3631&R9%114r3%311%A3?31&Ir4%211p011p051p0;1pWNI1pWJJ1").
Proof. intros st st1. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.
Section ZH.
Variables (p : aptr) (s : Z).
Lemma zh_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "RF'5'A'QD&R@vSEvSJr2r3r1%6554321';'<'T8'@&T;&T3'QM%544321&R5%11;%21>%:3421&Q3&T7&T<%24<;H1&T5&T4%26?>=K41'Q<%B48521&R2%11H%21K%G3421'Q4%H4>;81&R0%11N%21Q1%M3421&R9%11Q2%21Q5%Q13O21&R4%11Q6%21Q9%Q53Q321'4'8%12QBQB%311&R6%11Q>%21QA%Q=3421'QA&R1%11QC%21QF%QB3421%<2Q8QM%QC4Q9Q6Q31&R8%11QI%21QL%QH3421'QB%QI4Q?Q<Q91&R3%11QO%21R2%QN3421%R0271%R12>1%R22D1%R32M1%R42Q21%R52Q71%R62Q>1%R72QL1tWLR@R91pWJRA1pVHRC1pW0RE1").
Proof.
induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [repeat split; reflexivity|].
destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. repeat split; reflexivity.
Qed.
Lemma zh_shadow_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "L'@&>'<r1&3'AvSE%33721%63851%811'5'QD'R:&Q:&R@vSJr2r3%45<321?r5%7221%82B2%D3:21pWJ<1pVHC1pW0?1p0A1pW>K1").
Proof. intros q.
intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.
Lemma zh_hav : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q7'5'A'QD';'<'T8&T<&T4'4'8'@%22:1%411%84<761&QI&Q:&R@vSEvSJr2r3r1%6554321&3%13>G7%:231%<11%<263%>11%I3@31%I4MHGD&QJ%117%216%N3421%Q0261pWJQ21pVHQ41pW0Q61").
Proof.
induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.
Lemma zh_cells_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "R3'A'5'QD';&RGr3r1%3221&RH&RD&RLr4%211%4281%6281%<281&>'<r6&RM&9'@vSE%332G1&Q0%@221&RKr2vSJ%3221%E251+4%=221%@3Q1?1%B11p0D1pVLQ41'6'8%12Q7B%311&T2'T8&T<&T4%34Q=216&T9%14Q?438r5&QH&Q:&R@%15NHQ?Q9I&3%13Q1QFQ0%5231%711%@6QIB<:91%82O4%:11%C6QLE?=<1%Q<3E41p0J1pWJQM1pVHR01pW0R01pW8R21").
Proof. intros o.
induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
rewrite IH by (intros j Hj; apply Ho; lia).
pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.
Lemma zh_cells_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "R3&RHzvSJ%3221'5'A'QD';&RGr3r1%3221&RD&RLr4%211%4271%A271%;271'<'6'8'@%22B1%411&T2'T8&T<&T4%34H216&T9%14J438&RM&9vSE%23=N1&Q0%I221&RKr2%221Q6%M241+4%;221&QH&Q:&R@r5%25>Q>Q21Q7&3%13LQ=@%6231%811%L6Q@NHF:1(1(7&R9%11Q@%34QEQ4QI1%52Q41%Q93Q471p0Q;1pVLQI1pWJQI1pVHQK1pW0QM1p0QO1").
Proof.
intros HS. induction k as [|k IH]; intros i st j Hj; cbn [zero_hdrs]; [lia|].
destruct (Z.eq_dec j i) as [->|NE].
- rewrite zh_cells_other by (intros j' Hj'; nia).
pose proof (cells_wr8_same st (aadd p (UNIT + i * s - 4)) 0) as C. cbn [fst snd aadd] in C.
replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. rewrite C. reflexivity.
- rewrite (IH (i + 1) _ j) by lia. reflexivity.
Qed.
Lemma zh_cell_read_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "QG'A'5'QD';&RGr3r1%3221&RH&RD&RLr4%211%4281%6281%<281&>'<r6&RM&9'@vSE%332G1&Q0%@221&RKr2vSJ%3221%E251+4%=221%@3Q1?1%B11p0D1pVLQ41'Q6&Q5&Q:&R@%15C=Q4N>&3%13FQ;E%5231r5%8221%82D4%:213%Q03<31p0>1pWJQA1pVHQD1pW0QD1pW8QF1").
Proof. intros o.
intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.
Lemma zh_ticks_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "B'5'A'QD&Ir1%211&R@vSEvSJr3r4r2%6554321%:11p091pWJ=1pVH?1pW0A1").
Proof. induction k as [|k IH]; intros i st TK; cbn [zero_hdrs]; [exact TK|]. apply IH. apply ticks_ok_wr8. exact TK. Qed.
Lemma zh_cell_read_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "QG&RHzvSJ%3221'5'A'QD&Ir2%211';&RGr4%2215&RD&RLr5%211%4261%C2;1%:271'<'Q6&Q5&Q:&R@vSEr6%352J<1@&3'@%231J5%8241&RM&9%135N9&Q0%G221&RKr3%221Q6%K241+4%:221%E2<1(N%11Q=%J3I31p0L1p0Q81pVLQ=1pWJQ=1pVHQ?1pW0QA1p0QC1").
Proof.
intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
destruct (Z.eq_dec j i) as [->|NE].
- rewrite zh_cell_read_other by (intros j' Hj'; nia).
pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
- apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.
Lemma existsb_filter_gt12 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q:'4'8'A'@%3221%511'2p031'<r2r1%211(:%53721&RH+<&3%13?>8%4231p061pV:@1&RB&T1&T:%11D&RA&RI%;3IHA%22=1%411qV:J1&T6%114qY6M1r3%=6ON;521%?3Q0K1%@3Q1L3%N3Q021p0C1pV>Q11pW2Q41").
Proof. intros l f.
intros Hf. induction l as [|ch l IH]; [reflexivity|].
rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.
Lemma stale_hav_add_ge : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "L'4'8'A'@%3221%511'6%114&RG+<r3%3221'<'2&R<&Q=r5%23871r4r2%63321%73532%:3921p0<1pY0A1pUNF1pV6H1pVFF1").
Proof. intros hl bb T t.
intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.
Lemma cell_read_hdr_havoc_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q>'QD'8'@'A%3221'<&RJ&9r2%23761+@%5221z%83:21&>';&RGr3%;3@?1%321;&RH&RD+<%2251%42@1%:261%<11'Q6&Q5&Q:&Q>r4r5%3221&3%13Q1Q04%7231%921D%9263%;21F%Q33=31p0?1p0M1pW8Q81pV2Q81pWJQ=1").
Proof. intros st b o.
intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id].
unfold cell_read. cbn [r_cells r_hav r_havp].
destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
- rewrite E, lookup_insert_eq. cbn [default from_option id].
assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
fold (get_shadow st (fst b)).
destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma hav_hdr_havoc_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q?'QD'8'@'A%3221&>'<r1&RE&9r2%23981+@%5221%83;71%:11'6'4%A2?@%211%411&T2'T8&T<&T4%34F216&T9%14H438&QI&Q:&Q>r3r4%3221&3%13Q1Q04%7231%911%A6Q3C=;L1%:274%<11%D6Q6F@>O1%Q43F41p0L1pY2Q91pV2Q91pWJQ>1").
Proof. intros st b u.
intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma cells_hdr_havoc : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q1'QD&Q3';'<'T8'A&T<&T4'8'@%2251%746541&QH&Q:&Q>r1r2%3221&3%13:>4%7231%911%9263%;11%E3=31%E4DCB@&QJ%117%216%J3421%L261pV2N1pWJQ01").
Proof. intros st b.
unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.
Section NEST.
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.
Definition nt_stW : mstate :=
wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.
Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : forall o v t, X <= o < X + strideg - 4 ->
(r_cells (get_shadow st3 (fst b))) !! o = Some (v, t) -> (t < s_tick st3)%N.
Lemma pp_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P ":'<&Q3&FvSOvS7vS0vS<%544321vSE%93821").
Proof. reflexivity. Qed.
Lemma szc_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "8';&RG+1vT>%3221+WoO%5231%7231").
Proof. unfold szc. apply size_class_range. exact SC. Qed.
Lemma nest_model_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "G'<'QD&R=vSB&Q@z%211&QEvSOvS7vS<vS>&RK&Q0&R;vSK%211%5241vS5%<6;:9821%B3A>1&C%F3E21").
Proof.
unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
unfold upd_meta. rewrite rec_zero_hdrs.
change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.
Lemma ntW_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "R4';'<'T8'@&T;&T3'QM%544321&R5&D%211vSO%411%<3631&Q3&T7'A&T<%34?>21&T5&T4%26BA@541'Q<%E49521&R2%11@%21?%J3421'Q4%K4?;81&R0%11F%21E%Q03421&R9%11J%21I%Q43Q221&R4%11N%21M%Q83Q621'4'8%12LL%311&R6%11Q6%21Q5%Q@3421'QA&R1%11Q;%21Q:%QE3421%<2Q9Q7%QF4Q:Q6Q31&R8%11QA%21Q@%QK3421%QM271%QN2=1%QO2F1%R02K1%R12Q01%R22Q71%R32QF1").
Proof. repeat split; reflexivity. Qed.
Lemma ntT_proj : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "R4';'<'T8'@&T;&T3'QM%544321&R5&C%211vSO%411%<3631&Q3&T7'A&T<%34?>21&T5&T4%26BA@541'Q<%E49521&R2%11@%21?%J3421'Q4%K4?;81&R0%11F%21E%Q03421&R9%11J%21I%Q43Q221&R4%11N%21M%Q83Q621'4'8%12LL%311&R6%11Q6%21Q5%Q@3421'QA&R1%11Q;%21Q:%QE3421%<2Q9Q7%QF4Q:Q6Q31&R8%11QA%21Q@%QK3421%QM271%QN2=1%QO2F1%R02K1%R12Q01%R22Q71%R32QF1").
Proof.
unfold nt_stT. destruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.
Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
destruct (decide (q = mm)) as [->|NE].
- rewrite get_meta_rec_put_same, G0. reflexivity.
- rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.
Lemma ntT_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P ";'A'<&QF&Q2&Cr1%3221vSO%5213%83731pV8:1").
Proof. intros c. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.
Lemma ntT_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P ":'A'<&R>&Cr1%3221vSO%5213%73831pVH91").
Proof. intros i. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.
Lemma ntT_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "8'<'QA&Q8&C%211vSO%411%73631").
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.
Lemma ntT_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P ";&Q3'<'A&Q7&Cr1%3221vSO%5213%83731pW>:1").
Proof. intros q. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.
Lemma ntT_shadow_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "D'@&>'<r1&3'AvS0%33721%63851%811'R:&Q:&Cr2%3221vSO%5213%?3731p091pW>C1").
Proof. intros q.
intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
rewrite get_shadow_wr8_other by exact NE.
change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.
Lemma ntW_hav : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "N';'<'T8'A&T<&T4'4'8'@%2261%411%948761&QI&Q:&D&3vS0%239>1%5241%711vSO%8214%:11%F3<41%F4EDC@&QJ%118%216%K3421%M261").
Proof.
unfold nt_stW, enf0_st, wr16.
split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.
Lemma ntT_hav : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "N';'<'T8'A&T<&T4'4'8'@%2261%411%948761&QI&Q:&C&3vS0%239>1%5241%711vSO%8214%:11%F3<41%F4EDC@&QJ%118%216%K3421%M261").
Proof.
unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
rewrite A, B. exact ntW_hav.
Qed.
Definition nt_written (o : Z) : Prop :=
o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).
Lemma ntW_cells_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "QC'A&>'<r1&RMvRO+3%3221%63851%811r2+2%8271%;3=31%=11r3+1%=2<1%@3B31%B11'6'8'@%22G1%411&T2'T8&T<&T4%34M216&T9%14O438r4&QH&Q:&D&3vS0%23@Q61%5241%711%@6Q9B<:91vSO%9215%;11%D6Q=F@>=1%Q<3F51p0L1p0Q21p0Q81pW8QB1").
Proof. intros o.
intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
rewrite !cells_wr8_other' by lia. reflexivity.
Qed.
Lemma ntW_cell_read_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q7'A&>'<r1&RMvRO+3%3221%63851%811r2+2%8271%;3=31%=11r3+1%=2<1%@3B31%B11'Q6&Q5&Q:&D&3'@vS0%332K1%6251r4%9221vSO%:215%<214%Q03>41p0@1p0F1p0L1pW8Q61").
Proof. intros o.
intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.
Lemma ntT_cells_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q4'A&>&Er1%211%411'<'6'8'@%22:1%411&T2'T8&T<&T4%34@216&T9%14B438r2&QH&Q:&C&3vS0%23@I1%5241%711%@6LB<:91vSO%9215%;11%D6Q0F@>=1%K3F51p0M1pW8Q31").
Proof. intros o.
intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
rewrite zh_cells_other.
2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.
Lemma ntT_cell_read_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "H'A&>&Er1%211%411'<'Q6&Q5&Q:&C&3'@vS0%332>1%6251r2%9221vSO%:215%<214%?3>41p0A1pW8G1").
Proof. intros o.
intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.
Lemma ntW_ticks_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "3&I&D%211").
Proof.
unfold nt_stW. apply ticks_ok_wr8.
assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.
Lemma ntT_cell_read_zero : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q4'A';&RGzr1%3221vS5%5231%7231'<'Q6&Q5&Q:&C&3'@vS0%332A1%6251&RDvRO+<%3221&RKr2+@vT>%4221%5241%:271%C2<1(N%11M%H3G31p0J1pVLQ31").
Proof. intros j.
intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.
Lemma ntT_cell_read_hdr : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q0'A';&RG+1r1%3221+3%5231%7231'='<'Q6&Q5&Q:&C&3'@vS0%332B1%6251&RMvROr3%3221%<251(N%11F%A3@31qY4L1%D2M1p0F1pW0O1").
Proof. intros k.
intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
(wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
(wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
(wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
(wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
(wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
(wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
destruct (Z.eq_dec k 3) as [->|N3].
{ eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
rewrite 2 cell_read_wr8_other' by lia.
destruct (Z.eq_dec k 1) as [->|N1].
{ eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
assert (k = 2) by lia. subst k.
rewrite cell_read_wr8_other' by lia.
eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.
Lemma slot_geom : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "SA';'<&QF&Q?&Q9vSOvS7%3221%511(1&Q3vS0%3221%<3;51'6'QM%211&T2'@'T8&T;&T3%344217&T9%146439&3'A%2391@&R5%11H%=6<?8631vSG%G2A1%Q03A31'QN&QK%115(O%Q53421&RGz&9%13H@O%4231&RJ+@%2241%Q>3E17vS<%:291vT=%<261%8227%QD3K1=&RDvRO%2216&QO&QL%11L%311%F251&RK%12=?%I2H1'8%12Q@Q8'Q<%QF11&T7&T<%24QEQCQ=1&T5&T4%26QHQFQEQ@41%QH4R1418%QE4R2529r2&R2%11R:%QO6>=5431r1%R92?1%RB3?31r3%QL3R3QK1%RE3R41QK'?r4%Q@3R7QO1+9%Q5221&RM+4%22Q71%QH241%42Q83%QJ218%;231p0=1p0A1pVBQ21pV4Q41%S72Q71%S82Q;1%S92QD1%S:2QG1%S;2QJ1%S<2QM1%S=2R21%S>2R81%S?2R>1%S@2S31").
Proof.
destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
fold strideg in Sspan, Ss16, Ssmod, Snogrp.
assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
repeat (split; [first [assumption | unfold X; lia] |]).
intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.
Lemma X_mod16 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "8'<'A&RJvRO+@%3221z%73621").
Proof.
destruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _).
unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.
Lemma nt_tail_hyps : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "T3';&H&CvSB%3221'<'QB&Q9%1265(QC(0&Q3%211z%59222111111%:3971'6'QM%211&T2'@'T8&T;&T3%344217&T9%146439&3'AvSE%33:21&R5%11N%>6=@9731(1vSG%22C1%Q03C41&RG&9%13D<;%32L1&RJ+@%2241%Q83A1Q0&RD%1274&QO&QL%11?%311%>251'Q<%Q611&T7&T<%24Q5Q3M1&T5&T4%26Q8Q6Q5Q041%Q84QB418%Q54QC529&R2%11QN%Q>6QF<43Q41%QH1=%QN3=21'8%12QAQ9r2%QD62B:917r1%Q72D1%R53D31r3%QA3QHQ@1%R83QI1Q?'?r4%Q93QLQD1+9%Q4221%Q=21Q;%Q62Q<3%Q?215%8231p0:1p0>1pVBQ41pV4E1%QE2QC@&RH+<%Q@2QF1%32D1%S0251%M2R5R=%RB11%R>4R7Q;Q82%R;4R8Q<Q93&QH&Q:%12S5R9%311%RF6R=865J1(7%14R?RGQ0Q5%R:2;1%S83;41&RC&R9%11S>%32Q61p051p0C1pY0S01pY4RI1pW8RJ1vSO%911%SD3S591%SJ241%SK2Q11%SL2QI1%SM2R91%SN2RA1%SO2RF1%T02RK1%T12SB1%T22SN1").
Proof.
destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
destruct ntT_proj as (PR & PG & PA & PT & _).
split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
split. { rewrite PR. exact Sreg. }
split. { unfold p, X. cbn. lia. }
split. { exact X_mod16. }
split. { unfold p. cbn [snd]. lia. }
split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
eapply FRESH3; [| exact Hc]. lia. }
exact PT.
Qed.
Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.
Lemma ntF_rec_mt : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "@'<'QB&Q9vT0vSB%3221&BvSKvS5&RM+1%2231zvSE%867632:1%?3>:1").
Proof.
apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.
Lemma ntF_stride : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "='<'A&Q;&Q9vT0vSB%3221%511&RK+@vT>%3221%<3;51").
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.
Lemma ntF_shadow_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "@'<'T8'@&T;&T3'R:%544321&R7vT0%211&Q>vSE&C%3221%711%?3961").
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.
Lemma ntF_cell_read_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q0'A&>';&RGvROr1%3221&RH&RD+<%2261%4261%:261%<11'<'Q6&Q5&Q:vT0&3'@vS0%332F1%6251r2%9221&C%:215%<214%?3>41p0A1pW8O1").
Proof. intros o.
intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.
Lemma ntF_cells : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "N'A'<'6'8'@%2251%411&T2'T8&T<&T4%34;216&T9%14=438r1&QH&Q:vT0&3vS0%23@D1%5241%711%@6GB<:91&C%9215%;11%D6KF@>=1%K3F51pW8M1").
Proof. intros o.
unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.
Lemma ntF_havp : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "C'<'T8'A&T<&T4'@%544321&QJ&Q:vT0&3vS0%237:1%5241%711vSO%8214%:11%B3<41").
Proof.
unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.
Lemma ntF_hav : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q9'A&>'<r1&REvRO+@%3221%63851%811'6'4'8'@%22>1%411%611&T2'T8&T<&T4%34E216&T9%14G438r2&QI&Q:vT0&3vS0%23AN1%5241%711%@6Q1B<:91vSO%9215%;11%D6Q5F@>=1%Q43F51p0N1pY2Q81").
Proof. intros u.
intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.
Section SE.
Variables (req : Z).
Lemma nt_slot_ok : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
intros RQ FIT. pose proof szc_range as SZR.
destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
destruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
pose proof ntF_stride as STF.
pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
destruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _). fold stF in PF1, PF2, PF3, PF4.
destruct ntT_proj as (PR & PG & PA & PT & _).
constructor; rewrite ?STF.
- rewrite ntF_rec_mt. reflexivity.
- rewrite PF1, PR. exact Sreg.
- exact Skind.
- exact TP0.
- exact TP16.
- rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
- lia.
- rewrite Z.mul_comm. apply Z_mod_mult.
- lia.
- exact RQ.
- exact FIT.
- intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
+ left. unfold p. cbn [snd]. lia.
+ rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf); [left; lia| right]. nia.
- unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
- intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
- unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
- apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
- rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
- rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.
End SE.
Lemma ntF_span_cells : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "QA'A';&RG&RDvRO+@%3221r1%6221&RH&RM&RKvT>%2281%;281+4%6221%82:1%A2:1'<'6'8'@%22G1%411&T2'T8&T<&T4%34M216&T9%14O438r2&QH&Q:vT0&3vS0%23@Q61%5241%711%@6Q9B<:91vSO%9215%;11%D6Q=F@>=1%K3F51p0M1pW8Q@1").
Proof. intros o.
intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.
Lemma ntF_span_hav : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "Q:'A&RG&RDvRO+@%3221r1%6221'<'6'4'8'@%22=1%411%611&T2'T8&T<&T4%34D216&T9%14F438&REr2%221E&QI&Q:vT0&3vS0%23CO1%5241%711%B6Q2D><91vSO%9215%;11%F6Q6HB@=1%O3H51p0Q11pW8Q91").
Proof. intros o. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.
Lemma ntF_rdv13 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "R3&J'<'6'8'A'@%3221%511&T2'T8&T<&T4%348216&T9%14:438&RDvRO+=%3221&QH&Q:vSO&3vS0%23CD1%5241%711%C6GE?=91(0%11G%M3G31'4%11J%O11%I4NHG2%F4OIH3&RE+@%22D1&QI%11?%Q16Q597631%>1:%Q:3:21%Q:1Q7%Q44Q9Q3Q2Q8%Q14Q:Q4Q3Q9+TP0%<2N1&QJ%11I%Q;6Q?Q>6531%H1Q?%QD3921&G&Kr4vT0(7%14QFQGQ3Q9%65QL5431z%QM3QJ21p0:1p0E1p0Q31pW8R21").
Proof. intros o.
intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.
Lemma ntF_unknown : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "R4'A&RGzr2%3221'<'Q6&Q5&Q:vT0&3'@vS0%332=1%6251r3%9221(Q1%11?%>3=31'?&Lr4%23>:1';vSO%B21=%D215%;1=%H3G21&>&RMvRO+3%3221%Q221=&RH%12?5%>231%911'=r1%Q92Q81vS5%Q;231%E231r5&RD+<%22A1&RK+@vT>%3221%42=1%8261%QC3QH:1%Q12<1qVLQJ1%C2QK1%N11%Q52F1%Q62Q11%Q;2Q81p0Q=1p0QM1pVDR21pW:R31").
Proof. intros off h.
intros Ho Hc. pose proof szc_range as SZR.
destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
all: right; rewrite ntF_cell_read_other in Hc by lia.
- destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
+ rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
split; [exact Hc|]. split; [lia|]. intros (j & Hj & E). nia.
+ exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
- destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
[destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
+ rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
+ exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
+ rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
split; [exact Hc|]. split; [lia|]. intros (j & Hj & E).
apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.
Lemma ntF_shadow_other : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_M5P "D'@&>'<r1&3'AvS0%33721%63851%811'R:&Q:vT0r2%3221vSO%5213%?3731p091pW>C1").
Proof. intros q.
intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.
End CEIL_WRAP_1.
