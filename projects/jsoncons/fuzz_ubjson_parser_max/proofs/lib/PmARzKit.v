(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AxSymExec3Sound HeapIface HeapIfaceA IcptIfaceA
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR HeapIfaceAJx PmLayout PmLayoutA PmSpecsA PmSpecsAa PmModelFactsA PmStepA XIcptAs0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan Require Import XIcptA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARzKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepA.PMKA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.XIcptA.XIA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A0"; "0Aw"; "1None"; "1andb"; "1bool"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2ex"; "2not"; "2or"; "3Z"; "0FF"; "0H0"; "0HI"; "0ICok"; "0IL"; "0ILY"; "0K"; "0L"; "0LB"; "0LB'"; "0LK"]; ["4Model"; "4event"; "4page_base"; "5bvmap"; "0M"; "0M1"; "0M3"; "0MV"; "0P"; "0R"; "0R0"; "0R1"; "0R3"; "6mrestrict"; "7msteps"; "8credit"]; ["8regs_preserved"; "9BIGSHADOW_HI"; "9BIGSHADOW_LO"; "9aacc"; "9aclient"; "9ahid"; "9ar_sptop"; "9byte_at"; "9fframe"; "9hl_tp"; "9in_shadow_of"; "9model_rt"; "9ri_inv"; "9vml_of"; ":HIGHSH_HI"; ":HIGHSH_LO"]; [":LOWSH_HI"; ":LOWSH_LO"; ":aicpt_ok"; ":as0_icpt_layout"; ":icpt_layout"; ";CS"; "=defined"; "=ra_ok"; "=range"; "=writable"; "<SCFG"; ">avis"; "?agsh"; "@cfg"; "Awapp"; "BFPState"]; ["Bgetr"; "Bmkst"; "Bseg_rom"; "CTSet"; "Dsrealizes"; "Emem_grows"; "Fahpres"; "Famodel_ok"; "Faobj"; "Fastk"; "GAS0_CELLS"; "Gapp8"; "Gcells_ok"; "Gshadow_ok"; "Hloaded_segments"; "0SCFG_P"]; ["IIn"; "Iexistsb"; "Jadd"; "Jdiv"; "Jeqb"; "Jle"; "Jlt"; "Jmodulo"; "Jmul"; "Jof_nat"; "Jpow"; "Jsub"; "0W"; "0a"; "0a'"; "0ar"]; ["0c"; "0cr"; "0d"; "0dst"; "0fx"; "0fx0"; "0i"; "0k"; "0l"; "0len"; "0m"; "0model"; "0model1"; "0n"; "0n'"; "0o'"]; ["0p"; "0pc0"; "0pd"; "0q"; "0r"; "0scr"; "0sp"; "0src"; "KZ_to_bv"; "Kbv"; "0sz'"; "0x"; "0y"]]).
Module PMARZK.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma aacc_zero : ltac2:(TCodec.tc2 tcn__PmARzKit "QA'T9yR0%211':y8%511%311p051'D&S5zr2%3221&S6%1243&QCr5r4r3%43321'?&S2+QoooPP0&S3r6+8%3221%6251r1%D221&S;%:27?+1%3221%;219%>2=1%G281%A281&QGr8%231MNp041pXHQ21p0H1p0N1p0Q11pWLQ61pX2Q71pR:Q91").
Proof. intros M p n.
intros Hp Hn AC x Hx. set (a := 8 * (x - 0x7fff8000) + 7).
pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as R1.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as R2.
assert (Ha : p <= a < p + n) by (unfold a; lia).
assert (Sa : HeapIfaceA.S a = x).
{ unfold HeapIfaceA.S, HeapIfaceA.SB, a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
assert (Ma : a mod 8 = 7).
{ unfold a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.mod_add by lia. reflexivity. }
destruct (AC a Ha) as [Z0 | (v & Bv & Rv & Lv)]; [rewrite Sa in Z0; exact Z0 | lia].
Qed.
Lemma aacc_last : ltac2:(TCodec.tc2 tcn__PmARzKit "QE'T9yR0%211':y8%511%311p051'D&S6zr1%3221&QCr4r3r2%43321'A'?&QGr6&S2+QoooPP0&S3&S;r5%521=+1%4221+8%7221%:291%=3<1F'C'@%13LIJ&S7%1298%N21L&S5+7%22O1%H241%:281%J2<1qW@Q61%M2Q71p0O1p0Q51pWLQ:1pX2Q;1pR:Q=1").
Proof. intros M p n.
intros Hn AC. destruct (AC (p + n - 1) ltac:(lia)) as [Z0 | (v & Bv & Rv & Lv)]; unfold HeapIfaceA.S, HeapIfaceA.SB in *.
- exists 0. split; [rewrite Z.add_comm; exact Z0 | left; reflexivity].
- exists v. split; [rewrite Z.add_comm; exact Bv | right; lia].
Qed.
Lemma page_base_word : ltac2:(TCodec.tc2 tcn__PmARzKit "Q5'D'?&S5zr2%3221&S6&S:+2+R0%3221%5271%;271'@&S3r4+TP0%3221r3%5213%73D31'T9yR0%211&Q2&T8r5%2251%411%427>%611%B3831p0<1p0E1p0F1pXJQ31pXHQ41").
Proof. intros x y.
intros Hx Hy E. unfold page_base, page_base_of, page_size. rewrite !L5.unsigned_lit by lia. rewrite E. reflexivity.
Qed.
Lemma ahid_page : ltac2:(TCodec.tc2 tcn__PmARzKit "Q='7'<'D%2211%411'Q0'?&S5zr2%3221&S6&S:+2+R0%3221%5271%;271'@&S3r4+TP0%3221r3%5213%73G31'5&QEr7r6&T8yR0r5%3221%73651%524?%93871%C3;31p0=1p0F1p0G1pXJQ71pXHQ81pWHQ61p6Q81").
Proof. intros Aw model x y. intros Hx Hy E. unfold ahid, mkH. rewrite (page_base_word x y Hx Hy E). reflexivity. Qed.
Lemma shadow_okV : ltac2:(TCodec.tc2 tcn__PmARzKit "S?'T9yR0%211'5p021':y8%711%311p071'D'?&S5zr2%3221&S6&S:+2+R0%3221%5271%;271'@&S3r4+TP0%3221r3%5213%73D31r9&T8r5%22Q11%411%42Q3;%611%?3Q331p091p0B1p0C1pXJQ01pXHQ11%Q02O@%M2Q0A&S2%12>F+Q?%Q02O1%Q6231&QCr7r6%3321E&R;+QoooPP0+8%Q2261%=231&S;%?298+1%3221%Q8217%5217%D214%<3Q481&S8%Q=2Q6<%H2>1%Q?21>%42?1r1%QN221r8%N2Q=1%A21?%QF21E%Q12G1%QH21G%=2H1%Q421I%R32:1%R92:1&Br;%QG2RFR9%211(3%11RC%R43RC31%711p091pXHRD1&RM&Q=r:%22<1%431R4Hp061p0Q21p0Q@1p0QE1p0QK1p0QM1p0QO1pWLS11pX2S21pR:S41pQ>S:1").
Proof. intros H0 M p n.
intros HP Hp Hn Hpn AC AV SD. unfold XIA.shadow_ok, XIA.SB.
assert (Q1 : 0 <= p / 8). { apply Z.div_pos; lia. }
assert (Q2 : (p + n - 1) / 8 < 2 ^ 44). { apply Z.div_lt_upper_bound; lia. }
assert (Q3 : p / 8 <= (p + n - 1) / 8). { apply Z.div_le_mono; lia. }
assert (VIS : forall x, 0x7fff8000 + p / 8 <= x <= 0x7fff8000 + (p + n - 1) / 8 -> H0 (Z_to_bv 64 x) = false).
{ intros x Hx. replace x with (0x7fff8000 + p / 8 + (x - (0x7fff8000 + p / 8))) by lia. apply AV. lia. }
split; [|split].
- intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
rewrite <- (Z_to_bv_bv_unsigned 64 x). rewrite (mrestrict_visible H0 M); [| apply VIS; lia].
exact (aacc_zero M p n Hp Hn AC (bv_unsigned x) Hx).
- destruct (aacc_last M p n Hn AC) as (k & Bk & Rk). exists k. split; [| exact Rk].
rewrite (mrestrict_visible H0 M); [exact Bk| apply VIS; lia].
- intros Hn64 x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
rewrite <- (Z_to_bv_bv_unsigned 64 x). set (u := bv_unsigned x) in *.
assert (W1 : 8 * ((0x7fff8000 + p / 8) / 8) <= 0x7fff8000 + p / 8) by (pose proof (Z.mul_div_le (0x7fff8000 + p / 8) 8); lia).
assert (W2 : 0x7fff8000 + (p + n - 1) / 8 < 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) + 8).
{ pose proof (Z.div_mod (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
assert (HV : H0 (Z_to_bv 64 u) = false).
{ destruct (Z_lt_le_dec u (0x7fff8000 + p / 8)) as [LT|GE].
- rewrite (HP u (0x7fff8000 + p / 8)); [apply VIS; lia| lia| lia|].
assert (E1 : u / 8 = (0x7fff8000 + p / 8) / 8).
{ pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + p / 8) 8 ltac:(lia)). lia. }
change 4096 with (8 * 512). rewrite <- !Z.div_div by lia. rewrite E1. reflexivity.
- destruct (Z_le_gt_dec u (0x7fff8000 + (p + n - 1) / 8)) as [LE|GT]; [apply VIS; lia|].
rewrite (HP u (0x7fff8000 + (p + n - 1) / 8)); [apply VIS; lia| lia| lia|].
assert (E1 : u / 8 = (0x7fff8000 + (p + n - 1) / 8) / 8).
{ pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
change 4096 with (8 * 512). rewrite <- !Z.div_div by lia. rewrite E1. reflexivity. }
rewrite (mrestrict_visible H0 M _ HV). apply SD. exact Hx.
Qed.
Lemma shadow_words_mapped : ltac2:(TCodec.tc2 tcn__PmARzKit "R>'T9yR0%211':y8%511%311p051'D'C'?&S5&R1r1%3221&S6&R0%2241%8241&QO%9217&QN%7291%=231%?261&B'@r5&T8r2%22M1%411(3%11L%83L31%:11p0<1pXHM1z%H21:&RKr4r3%3221&S8+8&S3&S2+QoooPP0r6%4215%4231%6217%9281%Q;21Q9&S;%927M+1%3221%=21>%=2<1%?21@%B2A1%@21B%QA2QC1%QG2;1r8%11Q5%Q:3QN1Q3%Q<11p051pXHQO1p0M1p0Q21p0Q51pWLR31pX2R41pR:R61").
Proof. intros M p n.
intros SD Hn AP x Hx. apply SD. unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in AP. unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI.
assert (U1 : 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) + 8 <= 0x7fff8000 + (p + n - 1) / 8 + 8).
{ pose proof (Z.mul_div_le (0x7fff8000 + (p + n - 1) / 8) 8). lia. }
destruct AP as [(A0 & A1) | (A0 & A1)].
- left. assert (L1 : 0x7fff8000 <= 8 * ((0x7fff8000 + p / 8) / 8)).
{ assert (0x7fff8000 = 8 * (0x7fff8000 / 8)) by reflexivity. assert (0x7fff8000 / 8 <= (0x7fff8000 + p / 8) / 8) by (apply Z.div_le_mono; [lia| pose proof (Z.div_pos p 8); lia]). lia. }
assert (L2 : (p + n - 1) / 8 <= (0x7fff7fff - 9) / 8) by (apply Z.div_le_mono; lia).
assert (L3 : 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) <= 0x7fff8000 + (p + n - 1) / 8) by (apply Z.mul_div_le; lia).
change ((0x7fff7fff - 9) / 8) with 268431358 in L2. lia.
- right. assert (L1 : 0x2008fff7000 <= 8 * ((0x7fff8000 + p / 8) / 8)).
{ assert (0x2008fff7000 = 8 * (0x2008fff7000 / 8)) by reflexivity. assert (0x2008fff7000 / 8 <= (0x7fff8000 + p / 8) / 8).
{ apply Z.div_le_mono; [lia|]. assert (0x10007fff8000 / 8 <= p / 8) by (apply Z.div_le_mono; lia). change (0x10007fff8000 / 8) with 2199291686912 in *. lia. }
lia. }
assert (L2 : (p + n - 1) / 8 <= (0x7fffffffffff - 9) / 8) by (apply Z.div_le_mono; lia).
assert (L3 : 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) <= 0x7fff8000 + (p + n - 1) / 8) by (apply Z.mul_div_le; lia).
change ((0x7fffffffffff - 9) / 8) with 17592186044414 in L2. lia.
Qed.
Lemma fill_msteps : ltac2:(TCodec.tc2 tcn__PmARzKit "V6'R?&Q3y5'T9yR0%211%5241':y8%611%311p061'D'@&R@r6&T8&S9u1%211%42B1%7261r1%72C1%;3C31&R7r2%211r8u2%=11%?2M1%B241r4%B2N1%F3N31r9u:%E11%G2Q51%J241r7%J2Q61%N3Q631r:u<%M11%O2Q=1%Q2241%Q43Q<17'?&S5+1%221I&S:+2+Q8%3221%72N1%9261&RK%12AI+`PPP0&S;+R`0%22M1%?241&S6+R0%?2>1%32J1&S2+QoooPP0&S3r=r<%5221%>21I+8%6221%9281%:213r;%D21C%Q1231'Cr>%@21=%I2=H%Q6221%Q72?4%6221&R9&RNr@%Q02EO%44321Q0rAr?%746251&RL&RJrB%33:21&RMrC%23149'A'Q>&RArHrG+^li@%S12S=1rF&RB%11G%8576431%S62SB@%:59RM1S13%<3K31&RE%128S4z%R921S6%QJ2S7QH%R<221&B%R=2AS6%QJ2B?%QO2S81%RA231%511%R62CR5r3%RD221%R522F%RG221%;11r5%11S:rJ%11S<%T23T531p061p0=1p0D1pVLT71&R6rErD%33T121'8&S0&R5%233T51%T;1T2%T=2TK1%T@2SM1rI%TB213%TD3TL31p071pW>;1%TF2T:SM%TE2U1@%TI3U121%SE241%SF2A1%SG2F1%SH2Q@1%SI2QC1qR>U11%R22U21qRJU81%R42U91p0R61p0R:1p0R?1p0RC1p0RI1p0S11p0S@1p0SE1p0SK1p0SN1p0T91p0T@1p0TI1p0U21p0U61pX:UC1pX>UD1pWFUE1pX6UF1pR@UH1pRDUN1pW:V51").
Proof. intros fx R MV pd m sp r.
intros H1 RA H2 H10 H12 Hm AP S0 S1 S2 S3 WS WD CO SO.
assert (P0 : 0 <= pd /\ pd + m + 8 <= 2 ^ 47) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in AP; lia).
destruct (as0_icpt_fill fx MV (getr R (reg 11)) pd m sp R (Z_to_bv 64 r) Hm AP S0 S1 S2 S3) as (R3 & Mj & MS & KO & A10 & FZ & MG).
{ replace (Z_to_bv 64 (sp - XIA.SCR)) with (Z_to_bv 64 (sp - 2560 + 0)) by (f_equal; unfold XIA.SCR; lia).
replace (Z.to_nat XIA.SCR) with (Z.to_nat 2560) by reflexivity. apply WS; lia. }
{ replace (Z_to_bv 64 pd) with (Z_to_bv 64 (pd + 0)) by (f_equal; lia). apply WD; lia. }
{ exact CO. } { exact SO. } { exact (L5K.ret_ok_lit r RA). } { exact H1. } { exact H2. } { exact H10. } { reflexivity. } { exact H12. }
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr R (reg 11)))) (Z.to_nat m)) in *.
assert (LEN : length bs = Z.to_nat m) by (unfold bs; apply repeat_length).
exists R3, (wbytes Mj (Z_to_bv 64 pd) bs). split; [exact MS|].
split. { intros x Hx. apply (wbytes_grows bs Mj (Z_to_bv 64 pd)). apply MG. exact Hx. }
split.
{ intros a Ha Hout Hsc. destruct (Z_lt_le_dec a pd) as [Lo|Hi].
- rewrite wbytes_below by (rewrite !L5.unsigned_lit by lia; lia). apply FZ. rewrite L5.unsigned_lit by lia. unfold XIA.SCR. lia.
- rewrite wbytes_above by (rewrite !L5.unsigned_lit by lia; rewrite LEN, Z2Nat.id by lia; lia). apply FZ. rewrite L5.unsigned_lit by lia. unfold XIA.SCR. lia. }
split.
{ intros i Hi. replace (pd + i) with (bv_unsigned (Z_to_bv 64 pd) + Z.of_nat (Z.to_nat i)) by (rewrite L5.unsigned_lit by lia; lia).
rewrite AX2S.wbytes_nth; [discriminate| rewrite L5.unsigned_lit by lia; lia| rewrite LEN; lia]. }
split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.
Lemma agsh_frame : ltac2:(TCodec.tc2 tcn__PmARzKit "R5'T9yR0%211':y8%511%311p051'D!p021'?&S5zr1%3221&S6&S:+2+R0%3221%5271%;271&Br5r2%211%411'@r7&T8r3%22O1%411r8%113%83N31p0:1p0@1pXHO1%@1J'C&QB%K2B1&QA%Q121D%5231p071pXHQ81r4%Q62Q51&S2%12L3+Q?%Q52Q41%Q;231&R<r9r6%342I1Q3p051p0;1p0>1p0H1pWLQH1pVLQI1pRBQH1pR<QL1pR:QM1").
Proof. intros M M1 P a n.
intros FR PX H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
apply FR; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia|]. intros X. specialize (PX _ X). unfold BIGSHADOW_LO, BIGSHADOW_HI in PX. lia.
Qed.
Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma in3_of_existsb : ltac2:(TCodec.tc2 tcn__PmARzKit "Q6'<'D%2211%3212'7%112'@'5&S1&4&S4&6r1%23;<1%33==1r3%53>?1%63@@1%8241&=%13CC7%23DD5%<221%>251%53FG<%63GH:%@221%B241qW6I1%E3J1A(>%I3H21&S0r2%23OC1p041pWBO1pW2Q21").
Proof. intros c l.
intros E. apply existsb_exists in E as (d & Hd & E). destruct c as [[a w] v], d as [[a' w'] v']. cbn in E.
apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1, E2, E3. subst. exact Hd.
Qed.
Lemma cells_okV : ltac2:(TCodec.tc2 tcn__PmARzKit "Q='7'<'D%2211%411&QH%611&Q?'T9yR0%211':y8%511%311p051'Q0&QLvGr7r6r5r4r3r2&QMr1%211%;8:9876541&RL&RN&RJ&Q=&QE%12<:%321<%73651p091pWHF1pR:H1p6Q41pW4Q21pR0Q41pQ<Q51pQLQ81").
Proof. intros LB FF LK cr Aw M model.
intros HH. pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & VIMG & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (L5A.aly_segs L C LYa) in CS. rewrite Forall_forall in CS.
unfold XIA.cells_ok. rewrite Forall_forall. intros [[a w] v] Hin.
assert (D4 : In (a, Z.of_nat w, v) L5A.AS0_ALY_CELLS_D4 /\ 0 <= a /\ a + Z.of_nat w <= 0x691000).
{ cbn [XIA.AS0_CELLS] in Hin. unfold XIA.SB, XIA.HIGHEND in Hin.
repeat (destruct Hin as [E|Hin]; [injection E; intros <- <- <-; split; [apply in3_of_existsb; vm_compute; reflexivity| cbn; lia]|]). destruct Hin. }
destruct D4 as (D4 & Ha & Hw).
pose proof (CS (a, Z.of_nat w, v) (L5A.aly_cells L C LYa _ D4)) as X. cbn [fst snd] in X. unfold cell_is in X. rewrite Nat2Z.id in X.
rewrite (rdn_mrestrict_eq RSEGS (ahid Aw model) w M _); [exact X|].
apply L5A.range_avoids_of_avis; [apply VIMG; lia| lia| lia].
Qed.
Lemma agsh_ahpres : ltac2:(TCodec.tc2 tcn__PmARzKit "QN'7'<'D%2211%411&QH%611&R8%811'T9yR0%211':y8%511%311p051&RFvLvS?r9r8r7r6r5r4r3%:9987654321&S0(;r2%24MM51r:%53N21&R>%11=&S5z%221>&S2%12A@&S:+2+Q?%3221%9251&R<%14KJIHp031p0;1p0?1p0B1p0I1p2QC1pX8QD1pR<Q71pR:Q81pVJQA1pX<QH1pX>QI1pQ<QF1pQNQI1").
Proof. intros LB' FF sp scr W M M1 q A.
intros (P & _ & _) Hin WA H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
apply P. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia|]. split.
- unfold aclient, aclient_g. do 6 right. exists (q, A). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
- apply PMKA.wapp_outside_shadow; [exact WA| exact SX].
Qed.
Lemma in_shadow_sub : ltac2:(TCodec.tc2 tcn__PmARzKit "L'D&S5r5r3%3221&S2r4%2214r6%4217%9231&S6z%2217&QJ%137=9r9r8%4321@p041p071p0;1p0B1pXHG1pWNH1pVNI1pWLJ1pVLK1").
Proof. intros a n a' n' x. intros H1 H2 H3 [X1 X2]. unfold in_shadow_of. split; eapply Z.le_trans; [| exact X1| exact X2|]; apply PMKA.S_mono; lia. Qed.
Lemma fill_stage_pre : ltac2:(TCodec.tc2 tcn__PmARzKit "Y4'7'<'D%2211%411&QH%611&Q?'T9yR0%211':y8%511%311p051'Q0'R?&Q3y5%221:&RC&QLvGrAr@r?r>r=r<&QMr;%211%;8:9876541&RG%1286'Q>&RN&RAr:&T8r9%22Q11&Q=&QE%12CA%321C&RB%11;%;5D:731r8+^li@%<2Q;1%?5F3175%B3A51'C'?&S5&R1r1%3221&S6&R0%2241%8241&QO%9217&QN%7291%=231%?261&B'@r2%Q22R11%QC11(3%11R0%63R031%811p0:1pXHR?1&R@&S9u1%211%Q>2R31%52Q@1r6%QA2R@1%B3R@31&R7r7%211u2%<11%QH2R=1%?2R41%J3RH1QHu:%A11%QM2RB1%D2R:1%QO2RNR:%Q03RN21u<%G11%R32RH1%J2RA1%Q53S316+1%QF21RC&S:+2+K%3221%QK2RH1%QM261&S2&S;&QFvS?%211+XPPP0%5221+TP0%8221+R`0%92S41%R8231%R92S78&R6rH%>2S;6%33217'A&S0(;%14T8T8R1R?rQ0%43T921rD%RE2R51rC%J231%K2R8RF%RI221%RK251%RL281q4TC1%?2TD1qX8TE1%A2TF1&RHrO%231RBS0z%S021S2&S7+8%22S51%RI3TO15%S:21?%S;261%S<291qXFU31%O2U41qX0U51%Q12U61%SB2A1rJrB%Q932M1&QCrK%231Q2Q0rQ4rQ3rQ2rQ1%TF1SI%TO8TN5432Q:S<1%TD23S=&QKr3%22Q>1'5p0UA1r4%TA2<1%TB2=;%SG3421&RE%12@S9%T92Q6T7+R0%RD2RC1%T82T:1%T>241%T>2Q=SNrN%RC2Q?1%T=2T11%TC241%T511%RF25R>%TE21F%TB2G7%TH221%T:11%U:2V9F%UD11rQ8%113%T>3V831p061p0<1p0C1pVLVH1rM%RI3U:D1'8&R5%RG32U41%T=1TG%UI2V>1%T@2V51%TA2QA2%TL3VJ21p061pW>91%TE2V8T2%V02VORM%U13VO21'RD&R:vRO%211&R=rQ5%26V;1VCQ8VAV9%74V<41Fp091p0=1p0H1p0K1p0QE1p0QH1p0QO1p0R31p0R51pWJW;1pR<W=1pRHW91rIrL%B6VKRB2SLQ51%G4VLD1RFp051p0RD1p0RH1p0RL1p0T01p0T51p0T71p0TD1p0TM1p0U31p0U:1p0U@1p0UD1p0UN1p0VJ1p0W>1p0WA1pQHWN1pX:XB1pX>XC1pWFXD1pX6XE1pRDX41pX4XG1pRFX61pW:X:1pW<X;1pWHX=1pR:X?1p6XK1pW4XI1pR0XK1pQ<XL1pQNXO1").
Proof. intros LB' FF LK cr Aw M model fx0 fx R0 pc0 R pd m sp r K.
intros HH AM PRE SDEF H1 RA H2 H10 H12 Hm SC1 SC2 SCD CONT DD ACC KONT.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & SPB & TOP & _).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB' FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H0 := ahid Aw model) in *. set (MV := mrestrict H0 M) in *.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL, FSIMG.
destruct SPB as (_ & _ & TOP1 & _).
assert (DST : (0 <= pd /\ (pd + m <= 0x7fff7000 \/ 0x10007fff8000 <= pd) /\ pd + m <= ahl_ceil ar /\ (pd + m <= 0x10000 \/ 0x691000 <= pd))
/\ L5A.avis H0 pd m /\ L5A.avis H0 (0x7fff8000 + pd / 8) ((pd + m - 1) / 8 - pd / 8 + 1)
/\ (forall i, 0 <= i < m -> aclientw L ar LB' FF 0 0 (pd + i))).
{ destruct CONT as [(q & A0 & Hin & X1 & X2)|(o' & sz' & AO & Hsz & Hsz8 & X1 & X2)].
- destruct (WB (q, A0) Hin) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & SA & _). cbn [fst snd] in *.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in B1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
split; [lia|]. split; [apply (VBLK q A0); [exact Hin| lia| lia]|]. split.
+ apply (VBSH q A0 _ _ Hin). intros i Hi. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB.
assert (q / 8 <= pd / 8) by (apply Z.div_le_mono; lia). assert ((pd + m - 1) / 8 <= (q + A0 - 1) / 8) by (apply Z.div_le_mono; lia). lia.
+ intros i Hi. apply (L5SAR.block_client L ar LB' FF 0 0 q A0); [exact Hin| lia].
- pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB' FF LK cr Aw M model o' sz' 0 0 HH AO Hsz Hsz8) as ((O1 & O2 & O3 & O4 & O5) & OBIG & _ & OVIS & _ & _ & _).
destruct AO as (f & Hf & F1 & F2 & F3). destruct (WF f Hf) as (Y1 & Y2 & _). unfold FS_BYTES in Y2.
split; [lia|]. split; [eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split.
+ apply VFSSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, FS_BYTES.
assert (ar_fs ar / 8 <= pd / 8) by (apply Z.div_le_mono; lia). assert ((pd + m - 1) / 8 <= (ar_fs ar + 11571200 - 1) / 8) by (apply Z.div_le_mono; lia). lia.
+ intros i Hi. apply (L5SAR.obj_client L ar LB' FF 0 0 o' sz'); [exists f; split; [exact Hf| lia]| lia]. }
destruct DST as ((D0 & D1 & D2 & D3) & DVIS & DSVIS & DCW).
assert (AP : XIA.app8 pd m) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND; lia).
assert (SVIS : L5A.avis H0 (sp - 2560) 2560) by (apply VIS; lia).
assert (WSV : L5.writable RSEGS MV (sp - 2560) 2560).
{ apply (proj2 (L5A.writable_vis H0 M (sp - 2560) 2560 SVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact SCD| lia| lia]. }
assert (WDV : L5.writable RSEGS MV pd m).
{ apply (proj2 (L5A.writable_vis H0 M pd m DVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact DD| lia| lia]. }
assert (CO : XIA.cells_ok RSEGS XIA.AS0_CELLS MV) by exact (cells_okV LB' FF LK cr Aw M model HH).
assert (SO : XIA.shadow_ok MV pd m).
{ apply shadow_okV; [intros x y Hx Hy E; exact (ahid_page Aw model x y Hx Hy E)| lia| lia| lia| exact ACC| exact DSVIS|].
apply (shadow_words_mapped M pd m SDEF ltac:(lia) AP). }
assert (Q1 : 0x7fff8000 + (pd + m - 1) / 8 + 8 <= sp - 2560).
{ assert ((pd + m - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
destruct (fill_msteps fx R MV pd m sp r H1 RA H2 H10 H12 ltac:(lia) AP ltac:(lia) ltac:(lia) Q1 ltac:(lia) WSV WDV CO SO)
as (R3 & M3v & MS & MG & FZ & DEF3 & KS & A10).
set (W := fun a => (pd <= a < pd + m) \/ (sp - 2560 <= a < sp)).
apply (L5SAR.apiece L ar C HI LYa HIok LB' FF LK cr Aw M model fx0 fx R0 pc0 R3 r M3v W K HH AM (msteps_trans _ _ _ _ PRE MS) MG).
{ intros a Ha NW. apply FZ; [exact Ha| intros X; apply NW; left; exact X| intros X; apply NW; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [replace a with (pd + (a - pd)) by lia; apply DCW; lia| lia].
- split; [|lia]. apply (L5SAR.stack_client L ar LB' FF 0 0 a); lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply (KONT R3 M1 model1 HH1 AM1 MRT1 HID1 MGM1).
- intros a Ha N1 N2. apply FR1; [exact Ha| intros [X|X]; [exact (N1 X)| exact (N2 X)]].
- rewrite <- VIS1 in DEF3. exact (proj1 (L5A.defined_vis H0 M1 pd m DVIS) DEF3).
- exact KS.
- exact A10.
Qed.
Lemma fill_stage : ltac2:(TCodec.tc2 tcn__PmARzKit "XA'7'<'D%2211%411&QH%611&Q?'T9yR0%211':y8%511%311p051'Q0'R?&Q3y5%221:&RC&QLvGr>r=r<r;r:r9&QMr8%211%;8:9876541&RG%1286'C'?&S5&R1r1%3221&S6&R0%2241%8241&QO%9217&QN%7291%=231%?261&B'@&T8r2%22Q?1%Q011(3%11Q>%73Q>31%911p0;1pXHQM1&R@&S9u1%211%>2QA1%52Q81r5%A2QN1%C3QN31&R7r6%211u2%<11%H2QK1%?2QD1%J2R7QA%L3R721u:%B11%N2R11%E2QK1%Q02R=QK%Q23R=21u<%H11%Q42R71%K2R21%Q73RB16+1%QH21R4&S:+2+K%3221%QM2R91%QO261&S2&S;&QFvS?%211+XPPP0%5221+TP0%8221+R`0%92RE1%R:231%R;2RH8&R6rD%>2RL6%33217'A&S0(;%14SGSGR2RArL%43SH21rC%RG2R61rB%J231%K2R9RH%RK221%RM251%RN281q4T21%?2T31qX8T41%A2T51&RHrK%231RCS2z%S221S4&S7+8%22S71%RK3T>15%S<21?%S=261%S>291qXFTB1%O2TC1qX0TD1%Q12TE1%SD2A1rFrA%Q932M1&QCrG%231Q2Q0rQ0rOrNrM%T51SK%T>8T=5432Q:S=1%T323S>&QKr3%22Q>1'5p0U01&QEr4%22=1%32><%SJ3521&RE%12AS7%T<2Q7T:+R0%RE2RD1%T;2T=1%TA241%TA2FT0%RC2GF%T?2T21%TE231%T711%RF2JR>%TG21F%TD2GL%TJ221%T<11%T;2UHE%U711rQ4%113%T@3UG31p061p0<1p0B1pVLV71%RH3U;Q8R@'8&R5%RF32U51%T=1TG%TI2UL1%T@2UF1rQ1%TB213%TN3V931p071pW>:1%TF2UKT2%U12V>QG%U33V>21'RD&RN&R:vRO%211&R=rQ2%2661V6QNV5V4%84741S7p0:1p0>1p0J1p0L1p0QE1p0QH1p0R01p0R41p0R61pWJVK1pR<VM1pRHVI1+^li@rIrH%C6GRDRH321%I4HE1RHp061p0RF1p0RJ1p0RN1p0T21p0T71p0T91p0TF1p0TO1p0U51p0U<1p0UC1p0UG1p0V11p0VN1p0W11pQHW>1pX:X21pX>X31pWFX41pX6X51pRDWD1pW:WH1pWHWJ1pR:WL1p6X81pW4X61pR0X81pQ<X91pQNX<1").
Proof. intros LB' FF LK cr Aw M model fx R pd m sp r K. intros HH AM. apply (fill_stage_pre LB' FF LK cr Aw M model fx fx R 0x77330 R pd m sp r K HH AM (mst_refl _ _)). Qed.
Lemma move_stage_pre : ltac2:(TCodec.tc2 tcn__PmARzKit "YF'R4'R2vLvS?r1&R:vRO%211vG%8576521'R3r2%211'7'<'D%2211%411&QH%611&Q?'T9yR0%211':y8%511%311p051'Q0'R?&Q3y5%221:'Q1%F11!pXH21&QLrBrAr@r?r>r=&QMr<%211%:8Q89876541&RG%1286r3(9%11C%311'Q>&RN&RA&T8r;%22Q61&Q=&QE%12GE%321G&RB%11:%:5HE731r:+^liD%<2Q@1%>5K3175%A3@51'@&R@&S9u1%211%D2Q>1%52D1r6%G2QK1%93QK31&R7r7%211u2%<11%N2QH1%?2Q=1r9%Q12R51%C3R531u4%C11%Q52QO1%F2QE1&QI%11S0%Q92R=1%K3R=41u:%K11%Q=2R71%N2QN1%Q?2RCQN%Q13RC21u;%Q111%QC2R=1%Q42R51%Q63RH16u<%Q611%QH2RB1%Q92R;1%Q;3RM1;'?&S5z%221R>&S:+2+K%3221%72RC1%9261&RIrI+R`0%34SO2RH1'A&S0(;%14SGSGSKT2rQ1%43SH21rE%D2SO1&S2rC%2241%32T3T:%I221%K261%L291q4T31%@2T41qX8T51%B2T61&R6rKrD%3321SB&QCrL%231C@'CrQ4%K3T?I1rG%Q;2TF1rF%H231%Q>21F%Q@241%QA271q4TH1%Q52TI1qX8TJ1%Q72TK1&RHrQ3%231U2U9%QI219qXFU01%Q=2U11qX0U21%Q?2U31%F291rN%O31CQ<rO%M31GE%Q=2QHHrH%R4221%Q@22K%R621QL%Q0231pXHU7U3&Q@%12<T=r4%SH21RK%T92U=?%SK3U=21%R?2R>V1&S6+R0%R?2R>1%32V51%RE251&QDrQ=rQ<%37V<V;21JR=V3&BrQ2%RK21TNrQ0%R8231%>2U11%S0241%711r8%TN2V2G%211rQ:%113%TC3V131p071p0@1p0E1pVLVA1&S;%12Q>S1%S=21VO%N2W0Q@%S@221%U<2V@VK%TC11(3%11V?%U13V?31%L11p071pVLVN1%RH3TNS7QH&QKrQ8%221U1rQ;%V221TOrQ@rQ?rQ>%V:1Q0%VB8W@432Q<Q;TN1'RD&R=rQ9%26V41V1SEUHU2%44V5WF1Q;p061p0<1p0?1p0C1p0E1p0Q31p0R01p0R51pWJW91pR<R91pRHW71rM%@6VBQHRF1QJT3%B4VCX41S9p041p0R@1p0RG1p0RJ1p0RM1p0SE1p0SI1p0SN1p0TB1p0TG1p0U21p0U81p0U>1p0UE1p0UN1p0V61p0V:1p0VE1p0W81p0W=1p0W@1pQHWL1pX:XC1pX>XD1pWDXE1pX@XF1pW8XG1pRDX61pX4XI1pRFX81pW:X<1pW<X=1pWHX?1pR:XA1p6XM1pW4XK1pR0XM1pQ<XN1pQNY11pQFY71pQBY;1pQDYE1").
Proof. intros IL ICok ILY LB' FF LK cr Aw M model fx0 fx R0 pc0 R dst src len sp r K.
intros HH AM K0 PRE H1 RA H2 H4 H10 H11 H12 Hlen STK DC DD DA SC SD SA OVL KONT.
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
destruct DC as (qd & Ad & Hind & D1 & D2).
destruct (WB (qd, Ad) Hind) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
assert (SRCB : 0 <= src /\ src + len <= ahl_ceil ar /\ app_rng ar src len /\ (forall i, 0 <= i < len -> aclient L ar LB' FF sp 2560 (src + i))).
{ destruct SC as [(qs & As & Hins & X1 & X2)|(o' & sz' & AO & X1 & X2)].
- destruct (WB (qs, As) Hins) as ((P0 & P1 & P2 & P3 & P4 & P5) & _). cbn [fst snd] in *.
split; [lia|]. split; [lia|]. split; [apply (L5SAR.app_rng_block L ar C HI HIok LB' FF LK cr Aw M _ qs As src len HH Hins X1 X2)|].
intros i Hi. apply (L5SAR.block_client L ar LB' FF sp 2560 qs As); [exact Hins| lia].
- pose proof AO as (f & Hf & F1 & F2 & F3). destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP, Y2. unfold FS_BYTES in FSCEIL.
split; [lia|]. split; [lia|]. split; [apply (L5SAR.app_rng_aobj L ar C HI HIok LB' FF LK cr Aw M _ o' sz' src len HH AO X1 X2)|].
intros i Hi. apply (L5SAR.obj_client L ar LB' FF sp 2560 o' sz'); [exact AO| lia]. }
destruct SRCB as (S0 & S1 & SAR & SCL).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB' FF LK cr Aw M model fx0 fx R0 pc0 R 0x77334 _ K HH AM PRE (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM : M1 = M).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1. pose proof AM1 as (Mh1 & MI1).
pose proof (aic_memmove_libc _ _ _ _ _ ICok) as MMV. unfold amemmove_libc_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
rewrite (aicl_memmove IL ILY), (L5A.aly_segs L C LYa), (L5A.aly_scr_mem L C LYa) in MMV.
destruct (AX2S.rdn_defined RSEGS M (Z.to_nat len) (Z_to_bv 64 src)) as (bs & RDN & LEN).
{ rewrite L5.unsigned_lit by lia. lia. }
{ intros j Hj. unfold AX2S.rd1. rewrite L5.unsigned_lit by lia. specialize (SD (Z.of_nat j) ltac:(lia)). destruct (M _); [discriminate| exfalso; exact (SD eq_refl)]. }
assert (U2 : bv_unsigned (getr R 2%bv) = sp).
{ rewrite L5K.rl2, H2. apply L5.unsigned_lit. lia. }
apply (MMV fx R M model1 LB' FF LK cr Aw dst src len bs K); clear MMV.
- split; [exact HH1|]. split; [exact Mh1|]. split; [exact MI1|].
split; [rewrite L5K.rl10; exact H10|]. split; [rewrite L5K.rl12; exact H12|]. split; [lia|].
split; [rewrite L5K.rl4; exact H4|].
split; [rewrite L5K.rl1, H1; apply L5K.ret_ok_lit; exact RA|].
split; [rewrite U2; pose proof (L5SAR.astack_ok_of_astk L ar C LYa M M sp 2560 0 2560 STK (fun x X => X) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact A16)) as AS0;
rewrite Z.sub_0_r in AS0; exact AS0|].
split; [exact DA|].
split; [intros i Hi; rewrite U2; apply (L5SAR.block_client L ar LB' FF sp 2560 qd Ad); [exact Hind| lia]|].
split; [intros i m Hi Hm; apply (L5C.writable_of_defined RSEGS M dst len DD); lia|].
split; [exact K0|]. apply (L5SAR.app_rng_block L ar C HI HIok LB' FF LK cr Aw M _ qd Ad dst len HH Hind D1 D2).
- rewrite L5K.rl11. exact H11.
- exact SA.
- lia.
- exact SAR.
- intros i Hi. right. rewrite U2. apply SCL. exact Hi.
- exact RDN.
- intros _. exact OVL.
- intros R' M' model' R10' RP BYTES PRES SDEF' RT MI' HH'. rewrite U2 in PRES, SDEF'. rewrite <- L5K.rl1 in H1. rewrite H1.
apply (KONT R' M' model' RP ltac:(rewrite <- L5K.rl10; exact R10') PRES SDEF').
+ intros i Hi. destruct (BYTES i Hi) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
+ exact (L5LZ.model_rt_trans model model1 model' MRT1 RT).
+ split; [rewrite (L5LZ.model_rt_halted _ _ RT); exact Mh1| exact MI'].
+ exact HH'.
Qed.
End Kit.
End PMARZK.
