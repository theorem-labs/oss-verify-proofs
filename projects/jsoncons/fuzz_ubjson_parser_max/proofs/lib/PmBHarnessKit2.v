(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core L5DefsAB0 L5CoreAB0 L5StepARB0 HeapIfaceAJx
L5KnA PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAb PmModelFactsA PmStepAB0 PmBHarnessKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarnessKit2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit2.PMHAK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit2.PMHAK2.K.Objs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ax"; "1app"; "1cons"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0F"]; ["0FFc"; "0FFx"; "0HI"; "0L"; "0LBc"; "0LBx"; "0LKx"; "0M"; "0M1"; "0M2"; "0Mx"; "4credit"; "5BIGSHADOW_HI"; "5S"; "5ar_sptop"; "5ff_addr"]; ["5ff_bytes"; "5ff_class"; "5fframe"; "5ri_inv"; "5shadow_zero"; "5vml"; "6agree_on"; "7defined"; "7range"; "7u32_at"; "7u64_at"; "8zeros_at"; ":oav"; "9hbase"; "9hec"; "9hf"]; ["9hfin"; "9hpar"; "9hsrc"; "9hvec"; "9pfoot"; "9wapart"; "9wfi"; ";ADDR_B"; "<CHUNK"; "<iosb_at"; "<iss_at"; "<p_b"; "<p_k"; "<p_src"; "<p_stk"; "<p_tb"]; ["<parser_at"; "<parser_own"; "<pst"; "<pstate"; "<sr_qc"; "<srcst"; "<strm"; "<vs_own"; "<vstr"; "<vstr_at"; "=agA"; "=agsh"; ">accA"; ">annA"; "?ahpres"; "@loaded_segments"]; ["AIn"; "Aincl"; "Badd"; "Ble"; "Blt"; "Bmodulo"; "Bmul"; "Bpow"; "Bsub"; "0Vx"; "0W1"; "0W2"; "0Wc"; "0Wp"; "0a"; "0ar"]; ["0b"; "0c"; "0crx"; "0f"; "0g"; "0j"; "0k"; "0n"; "0o"; "0ois"; "0op"; "0p"; "0ps"; "0r"; "0rdb"; "0rs"]; ["0s"; "0s'"; "0scrc"; "0shi"; "0slo"; "0sm"; "0spc"; "0src"; "0st"; "CZ_to_bv"; "Cbv"; "0stk"; "0str"; "0v"; "0vp"; "0vp'"]]).
Local Ltac lia := L5FastLia.plia.
Module PMHAK2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition hf (F : Z) : Prop := F mod 8 = 0 /\ 0 <= F /\ F + 1024 <= 2 ^ 47 /\ (BIGSHADOW_HI <= F \/ F + 1024 <= BIGSHADOW_LO).
Definition pfoot (F slo shi : Z) (Wp : Z -> Prop) : Prop :=
forall a, Wp a -> (F <= a < F + 1024) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 128) \/ (slo <= a < shi).
Definition wfi (F : Z) (Wc : list L5.range) : Prop :=
forall r, In r Wc -> (F <= fst r /\ fst r + snd r <= F + 1024) \/ (65536 <= fst r /\ fst r + snd r <= 0x693000).
Definition wapart (Wc : list L5.range) (o n : Z) : Prop := forall r, In r Wc -> fst r + snd r <= o \/ o + n <= fst r.
Lemma wfi_nil : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "8'>&QFr1(5&Q8%211%5241pQ071").
Proof. intros F. intros r []. Qed.
Lemma wfi_cons : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q8'>'8%1222'4&Q8%211'=':&RCr3&3r2%23<<1%5241&RB&9%13@@5%3251+QP0%52:1%<231%>281+RPP0%?21;+Vb\P0%A281%C231%E261&QFr4%221Cr5(2%13O4H%6231p051p091pUJQ01pVLQ41pQ0Q71").
Proof. intros F r Wc. intros H W r' [<-|Hr]; [exact H| exact (W r' Hr)]. Qed.
Lemma wfi_app : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "C'>'4&Q8%211&QFr3r2%3221r4%5213r5&1%13:47%9231p051p081pUH=1pUF>1pQ0B1").
Proof. intros F W1 W2. intros A B r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (A r Hr)| exact (B r Hr)]. Qed.
Lemma wapart_nil : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 ":'>&QE(5&Q8%211r2r1%63321pV@81pVB91").
Proof. intros o n. intros r []. Qed.
Lemma wapart_cons : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q3'8'>%2211'4&Q8%211'=&RC&RB&3r4%23::1&9%13<<3%6231r2%9221r1%:231%<218%>241&QEr3%23=18(2r6r5%33I21%731B6p061p0:1pV@N1pVBO1pUJL1pVLQ01").
Proof. intros r Wc o n. intros H W r' [<-|Hr]; [exact H| exact (W r' Hr)]. Qed.
Lemma wapart_app : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "F'4&Q8%211'>&QEr4r2r1%43321r3%63514&1r6r5%33=21%;31:6p061p091pV@?1pVB@1pUHB1pUFC1").
Proof. intros W1 W2 o n. intros A B r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (A r Hr)| exact (B r Hr)]. Qed.
Lemma u64_agA : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QA'SJyR0%211'6y8%511%311p051'>&R:r6r5r4r3%544321&RC%1253&RB+8%2271%32:9%6221z%821<%72>6&RG+2+R0%3221%>251&Q:&R?r;r7%44321Hr8%645413p031p091p0@1p0C1p0I1p0L1pWLQ31pUNQ41pV@Q51pVBQ61pQDQ81pQBQ91").
Proof. intros M1 M2 o n a v. intros (AG & _) H1 H2 H3 H4. apply (L5C.u64_at_agree RSEGS M1 M2 a v); [intros i Hi; apply AG; lia| lia| lia]. Qed.
Lemma u32_agA : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QA'SJyR0%211'6y8%511%311p051'>&R:r6r5r4r3%544321&RC%1253&RB+4%2271%32:9%6221z%821<%72>6&RG+2+R0%3221%>251&Q9&R?r;r7%44321Hr8%645413p031p091p0@1p0C1p0I1p0L1pWLQ31pUNQ41pV@Q51pVBQ61pQDQ81pQBQ91").
Proof. intros M1 M2 o n a v. intros (AG & _) H1 H2 H3 H4. apply (PMHAK.u32_agree M1 M2 a v); [intros i Hi; apply AG; lia| lia| lia]. Qed.
Lemma shz_agA : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q@'SJyR0%211'6y8%511%311p051'>&R:r6r5r4r3%544321&RC%1253&RB&RF+8%2217%4291%52<;%8221';&RE%12?7z%43D21%>22B&Q4r;r7%3321Gr8%53413p031p081p0:1p0@1p0H1p0K1pV:Q21pUNQ31pV@Q41pVBQ51pQDQ71pQBQ81").
Proof. intros M1 M2 o n a g.
intros (_ & SH) H1 H2 H3 H4 SZ j Hj. unfold byte_at in *. specialize (SZ j Hj).
rewrite (PMFA.S_granule a j H3 ltac:(lia)) in SZ |- *. rewrite (SH (a + 8 * j) ltac:(lia)). exact SZ.
Qed.
Lemma defined_agA : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q3'SJyR0%211'6y8%511%311p051'>&R:r6r5r4r3%544321&RC%1253&RB%1265%2298%5221&Q7r9%231<;%332>=p021p061p0;1p0>1pV>E1pUNF1pV@G1pVBH1pQDJ1pQBK1").
Proof. intros M1 M2 o n a k. intros (AG & _) H1 H2 D i Hi. rewrite AG by lia. apply D. exact Hi. Qed.
Lemma zeros_of_shz : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "G'SJyR0%211'6y8%511%311p051'>&Q4r3r2r1%43321&Q;r4&M%117%43317p061pV:<1pVB=1pQ@?1").
Proof. intros M o g. intros SZ i Hi. exact (SZ i Hi). Qed.
Definition hbase (F : Z) (M : word -> option byte) (s s' : PM.vstr) (sm : PM.strm) : Prop :=
PM.vstr_at RSEGS PMSPA.accA M (F + 32) s /\ PM.iss_at RSEGS PMB.AD PMSPA.accA M (F + 96) s' sm
/\ L5.u64_at RSEGS M (F + 432) (pa_vp_visitor PMB.AD) /\ shadow_zero M (F + 432) 1 /\ shadow_zero M (F + 96) 34.
Definition hpar (F : Z) (M : word -> option byte) (ps : PM.pst) : Prop :=
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M (F + 464) (F + 96) ps /\ L5.u64_at RSEGS M (F + 848) (F + 432).
Definition hec (F : Z) (M : word -> option byte) (v c : Z) : Prop :=
L5.u32_at RSEGS M (F + 992) v /\ L5.u64_at RSEGS M (F + 1000) c /\ shadow_zero M (F + 992) 2.
Lemma shz_frame : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "R6'SJyR0%211'6y8%511%311p051'>!p021':&RCzr1%3221&RD&RG+2+R0%3221%5271%;271&<r5r2%211%411';r7&SIr3%22O1%411r8%113%83N31p0:1p0@1pUNO1%H2J9%N2J1r6&RB&M%11E%321E%511%I11p081pV<Q:1r4%811%Q92Q81%;293%Q;21Q3&Q4r9%231@Q2%332NAp021p061p091p0=1p0I1pV:QI1pVBQJ1pULQI1pQDQM1pQBQN1").
Proof. intros M1 M2 Wp o g. intros FR W H0 H1 SZ j Hj. unfold byte_at. rewrite FR; [exact (SZ j Hj)| lia| exact (W j Hj)]. Qed.
Definition hsrc (F : Z) (M : word -> option byte) (src : PM.srcst) : Prop :=
PM.src_fields_at RSEGS PMSPA.accA M (F + 488) (F + 96) (F + 112) src /\ PM.nullis_at RSEGS PMB.AD PMSPA.accA M (F + 496).
Definition hvec (F : Z) (M : word -> option byte) (b k : Z) (stk : list PM.pstate) : Prop :=
PM.vec_at RSEGS PMSPA.accA PMSPA.annA M (F + 824) b k stk /\ L5.defined M (F + 824) 24 /\ PMSPA.accA M (F + 824) 24.
Lemma hdead_of_parser : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QB'SJyR0%211'6y8%511%311p051'>'R2&R0&R?&QG&R<&R=r3&RBr2+^@%3221+S0%5241r1%=8<;:98421':&QBr4&QM%11;%43>31&R9+i0%@2A1&QO%11A%55HF931&QC&QK%11E&QL%11G&QN%11I%75LA531%D291%E2@1p0G1pVJQ61pQ0Q81pQ@Q:1").
Proof. intros M F ps.
intros (P0 & D & C0 & P8 & P9 & P12 & P16 & P20 & NI & SRC & P320 & P328 & C320 & TB & VEC & _).
replace (F + 464 + 32) with (F + 496) in NI by lia. replace (F + 464 + 24) with (F + 488) in SRC by lia. replace (F + 96 + 16) with (F + 112) in SRC by lia.
replace (F + 464 + 336) with (F + 800) in TB by lia. replace (F + 464 + 360) with (F + 824) in VEC by lia.
split; [split; [exact SRC| exact NI]|]. split; [exact TB|]. split; [exact VEC|]. split.
- apply (L5.defined_sub M (F + 464) 384 (F + 824) 24 D); lia.
- intros x Hx. apply C320. lia.
Qed.
Lemma iosb_revptr : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QO'SJyR0%211'6y8%511%311p051'>&QI&R?&QG&R<r7r5r4r2r1%9887654321&Q:r6%24;816&Q6r9r8&RB+8%22>1+T@%746521&R;r:+TH%342:91&Q7%134<9&RCz%2217r;%?218&RG+2+R0%3221%9251r=r<%Q78Q6Q5Q421AIHp041p0<1p0@1p0C1p0H1p0Q11p0Q51pWBQ@1pVNQA1pX0QB1pWNQC1pVBQD1pQDQF1pQBQG1").
Proof. intros M1 M2 o vp vp' rdb st.
intros (H0 & H32 & H36 & H40 & H48 & Z & D & C & ST) U AG SH D8 Ho Ho'.
split; [exact U|]. split; [apply (PMHAK.u32_agree M1 M2 (o + 32) st); [intros i Hi; apply AG; lia| lia| lia| exact H32]|].
split; [apply (PMHAK.u32_agree M1 M2 (o + 36) 0); [intros i Hi; apply AG; lia| lia| lia| exact H36]|].
split; [apply (L5C.u64_at_agree RSEGS M1 M2 (o + 40) rdb); [intros i Hi; apply AG; lia| lia| lia| exact H40]|].
split; [apply (L5C.u64_at_agree RSEGS M1 M2 (o + 48) _); [intros i Hi; apply AG; lia| lia| lia| exact H48]|].
split; [apply (PMF.zeros_at_agree M1 M2); [intros i Hi; apply AG; lia| exact Z]|].
split; [intros i Hi; destruct (Z.lt_ge_cases i 8) as [Y|Y]; [apply (D8 i); lia| rewrite AG by lia; apply (D i Hi)]|].
split; [apply (PMFA.accA_agree M1 M2 o 152 SH C)| exact ST].
Qed.
Definition hfin (F : Z) (M : word -> option byte) (s : PM.vstr) (st : Z) : Prop :=
PM.vstr_at RSEGS PMSPA.accA M (F + 32) s /\ L5.u64_at RSEGS M (F + 120) (pa_classic_imp PMB.AD)
/\ PM.iosb_at RSEGS PMB.AD PMSPA.accA M (F + 216) 1253432 (F + 112) st.
Section K.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C scfg HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma blk_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "S<'4'8'>%2211%411&Q2%611&K'SJyR0%211'6y8%511%311p051&Q5!p0@1&Q3vBr@r?r>r=r<r;r:%9887654321&R@(7r9%24NN51rA%53O21%Q22Q0Q1+4%74Q3Q361r8%94Q4Q521&1%13Q48D%=3731&Q?%11A&RC&RH&NvRO%211+XPPP0%5221%721E&L%921K':zr1%=221&RD&RG+2+R0%3221%5271%:271&<r2%Q:11%311';&SIr3%22R01%Q?11%QA12%63QN21p081p0=1pUNR=1&QD%14QJQHQGQF&R:%14QHQDQBQNp031p061p0Q01p0Q31p0Q<1p0Q?1p0QH1p0QO1pQDR=1pQBR>1pULR<1pW8RM1pW:RN1pW0RO1pQ0S01pV4S11pVHS21pUDRE1pQFRG1p2S31pV6S11pQ>S31pQ4S41pQ<S71").
Proof. intros LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2.
intros HH Hin HF (F8 & F0 & F1 & FB) S1 S2 FR WP.
exact (PMHAK.blk_agA L ar C scfg HI HIok LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH Hin HF F8 F0 F1 FB S1 S2 FR WP).
Qed.
Lemma blk_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "RE'4'8'>%2211%411&Q2%611&K'SJyR0%211'6y8%511%311p051&Q5&Q8%B11&Q3vBrBrAr@r?r>r=r<%9887654321&R@(7r;%24NN51rC%53O21%Q22Q0Q1+4%74Q3Q361r:%94Q4Q521&1%13Q48D%=3731&Q?%11A&R>vCvROr9r8r7r6r5%8976F?54321%H4QDQDON%J3QD1L&QF%12Q19&R:%14;:Q6Q5p031p061p091p0C1p0F1p0O1p0Q61pQDQD1pQBQE1pUJQC1pW6R41pW>R51pQ2R21pQ:R51pW0R81pQ0R91pV4R:1pVHR;1pUDQN1pQFR01p2R<1pV6R:1pQ>R<1pQ4R=1pQ<R@1").
Proof. intros LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2.
intros HH Hin HF (F8 & F0 & F1 & FB) AH Hc WF.
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ p c HH Hin) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
pose proof (PFA (F, 4, rs) HF) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 4) with 1024 in PF.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG.
apply (PMHAK.agA_ahpres_blk L ar LBc FFc spc scrc Wc M1 M2 p c AH Hc); [lia| lia|].
intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
split; intros r Hr Hin'; unfold L5.in_rng in Hin'; destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.
Lemma ff_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "RD'4'8'>%2211%411&Q2%611&Q8%811'SJyR0%211'6y8%511%311p051&R>vCvROr;r:r9r8r7r6r5%:9987654321&R@%13H39&RC&RB&O%118+Q0%4221r4%7221%72<2&RH%81@&Q0&Q1%11C%311%>251+8%8221%B2:1&Q?%11J%E2LK%E2ML+QP0%G2Q01%I231&QFr>%22Q51&QEr?%231Q8Q7&R:%1436Q;Q:p031p071p0;1p0@1p0B1p0E1p0Q11p0Q:1p0Q=1pV@R71pVBR81pQ0R91pV8R71pQDQM1pQBQN1pUJR71pW6R>1pW>R?1pQ2R<1pQ:R?1").
Proof. intros LBc FFc spc scrc Wc M1 M2 f F o n.
intros AH Hf H1 H2 (F8 & F0 & F1 & FB) O1 O2 WF WA.
apply (PMHAK.agA_ahpres_ff L ar LBc FFc spc scrc Wc M1 M2 f o n AH Hf H1 H2); [lia| lia|].
intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
split; intros r Hr Hin'; unfold L5.in_rng in Hin'.
- destruct (WA r Hr) as [Y|Y]; lia.
- destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.
Lemma shz_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "RF'4'8'>%2211%411&Q2%611&Q8%811'SJyR0%211'6y8%511%311p051&R>vCvROr;r:r9r8r7r6r5%:9987654321&R@%13H39':';&O%118%33Q018&Q0&Q1%11<%311+QP0%93Q621%;271&Q?%11B&QF%12EI&RC%12HG&RB&RF+8%221K%42M1%52O>%8221&RE%12Q26z%K3QH21%=22Q5&Q4r?%231Q:Q9r<%4331Q<p031p071p091p0>1p0F1p0I1p0L1p0O1p0Q<1p0Q?1pV:R91pVBR:1pQ0R;1pV8R91pQDQO1pQBR01pUJR91pW6R@1pW>RA1pQ2R>1pQ:RA1").
Proof. intros LBc FFc spc scrc Wc M1 M2 f F o g.
intros (AK & _ & _) Hf (E1 & E2) (F8 & F0 & F1 & FB) WF H1 H2 H3 H4 SZ j Hj. unfold byte_at in *. specialize (SZ j Hj).
rewrite (PMFA.S_granule o j H3 ltac:(lia)) in SZ |- *.
pose proof (PMKB.S_in_shadow (o + 8 * j) ltac:(lia)) as SX.
rewrite AK; [exact SZ|]. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
- right; right; right; right; right; left. exists f. split; [exact Hf|]. rewrite E1, E2. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
- intros r Hr Hin. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX, FB. destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.
Section Objs.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 4, rs) (FFx ++ LKx).
Hypothesis HFF : hf F.
Variables (slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte).
Hypothesis S1 : ahl_ceil ar <= slo.
Hypothesis S2 : BIGSHADOW_HI <= slo.
Hypothesis FR : forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Hypothesis WP : pfoot F slo shi Wp.
Definition oav (o n : Z) : Prop := forall x, o <= x < o + n -> ~ Wp x /\ ~ Wp (HeapIfaceA.S x).
Lemma vstr_keep_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q:'>'R8&RA'8%1244&R7r1%211vE%73521&RCzr3%3221&RBr4+H%3221&RG+2+Q?%3221%<251&Q<r5%2219&R9&R?&R<vHr6%5543217vIr7%8576214p041p0;1p0?1p0I1p0N1pW2Q71pVBQ91").
Proof. intros o s.
intros INC H0 H1 OA VS. apply (PMFA.vstr_at_agreeA RSEGS M1 M2 o s); [lia| lia| apply (PMHAK.agA_frame M1 M2 Wp o 24 FR H0 H1 OA)| | exact VS].
intros c n p E. apply (blk_piece LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH); [apply INC; rewrite E; left; reflexivity| exact HF| exact HFF| exact S1| exact S2| exact FR| exact WP].
Qed.
Lemma iss_keep_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q='>'R8'R6&RA'8%1255&R7r2%211vE%73521&RCzr4%3221&RBr5+X@%3221&RG+2+Q?%3221%<251&Q<r6%2219&QJ&R?&QG&R<vHr7%67543218AvIr8%97876214;p041p0<1p0@1p0J1p0O1pW<Q81pWJQ:1pVBQ<1").
Proof. intros o str sm.
intros INC H0 H1 OA IS. apply (PMFA.iss_at_agreeA RSEGS PMB.AD M1 M2 o str sm); [lia| lia| apply (PMHAK.agA_frame M1 M2 Wp o 272 FR H0 H1 OA)| | exact IS].
intros c n p E. apply (blk_piece LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH); [apply INC; rewrite E; left; reflexivity| exact HF| exact HFF| exact S1| exact S2| exact FR| exact WP].
Qed.
Lemma parser_keep_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q='>'R2&RA'8%1244&R1r1%211vE%73521&RCzr4%3221&RBr5+\0%3221&RG+2+Q?%3221%<251&Q<r6%2219&R0&R?&QG&R<&R=vHr7%786543219BvIr8%:89876214<p041p0=1p0A1p0K1p0Q01pW2Q91pVDQ;1pVFQ<1").
Proof. intros op ois s.
intros INC H0 H1 OA PA. unfold PM.parser_own, PM.src_own, PM.vec_own in INC.
assert (IQ : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LBx) by (apply INC; left; reflexivity).
assert (IB : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LBx) by (apply INC; right; left; reflexivity).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
apply (PMFA.parser_at_agreeA RSEGS PMB.AD M1 M2 op ois s); [lia| lia| apply (PMHAK.agA_frame M1 M2 Wp op 384 FR H0 H1 OA)| lia| lia| | lia| lia| | | exact PA].
- apply (blk_piece LBx FFx LKx crx Ax Mx Vx _ _ F rs slo shi Wp M1 M2 HH IQ HF HFF S1 S2 FR WP).
- apply (blk_piece LBx FFx LKx crx Ax Mx Vx _ _ F rs slo shi Wp M1 M2 HH IB HF HFF S1 S2 FR WP).
- intros c n p E. apply (blk_piece LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH); [apply INC; right; right; rewrite E; left; reflexivity| exact HF| exact HFF| exact S1| exact S2| exact FR| exact WP].
Qed.
Lemma hbase_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q?'R8'R6&RA'8'>%2211&1&R7r2%211r3%411%63731vE%<3921&Q<&RBv?+Q0%3221+H%6221+S0%7261+X@%:221+]@%;2:1+8%>221&Q=vHr7r6r5%55B4321vIr8%85E2165p041p0;1p0@1p0E1p0M1pW<Q;1pW4Q=1pW2Q>1").
Proof. intros s s' sm.
intros INC O1 O2 O3 (VS & IS & V1 & V2 & V3). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG : PMFA.agA M1 M2 (F + 432) 8) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 432) 8 FR); [lia| lia| exact O3]).
assert (AGI : PMFA.agA M1 M2 (F + 96) 272) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 96) 272 FR); [lia| lia| exact O2]).
split; [|split; [|split; [|split]]].
- apply (vstr_keep_piece (F + 32) s); [intros x Hx; apply INC; apply in_or_app; right; exact Hx| lia| lia| exact O1| exact VS].
- apply (iss_keep_piece (F + 96) s' sm); [intros x Hx; apply INC; apply in_or_app; left; exact Hx| lia| lia| exact O2| exact IS].
- apply (u64_agA M1 M2 (F + 432) 8 (F + 432) _ AG); [lia| lia| lia| lia| exact V1].
- apply (shz_agA M1 M2 (F + 432) 8 (F + 432) 1 AG); [lia| lia| lia| lia| exact V2].
- apply (shz_agA M1 M2 (F + 96) 272 (F + 96) 34 AGI); [lia| lia| lia| lia| exact V3].
Qed.
Lemma hpar_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "L'R2&RA'8'>%2211&R1r1%211vE%83521&Q<&RBv?+^@%3221+\8%6221&QAvHr3%33821vIr4%63;21p041p091p0A1pVJK1").
Proof. intros ps.
intros INC O1 (PA & V1). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG : PMFA.agA M1 M2 (F + 464) 392) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 464) 392 FR); [lia| lia| exact O1]).
split.
- apply (parser_keep_piece (F + 464) (F + 96) ps); [exact INC| lia| lia| intros x Hx; apply O1; lia| exact PA].
- apply (u64_agA M1 M2 (F + 464) 392 (F + 848) _ AG); [lia| lia| lia| lia| exact V1].
Qed.
Lemma hec_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "D'>&Q<&RBv?+o0%3221+@%6221&Q>vHr3r2%449321vIr4%74<215p041p0:1pV4B1pWLC1").
Proof. intros v c.
intros O1 (E1 & E2 & E3). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG : PMFA.agA M1 M2 (F + 992) 16) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 992) 16 FR); [lia| lia| exact O1]).
split; [|split].
- apply (u32_agA M1 M2 (F + 992) 16 (F + 992) _ AG); [lia| lia| lia| lia| exact E1].
- apply (u64_agA M1 M2 (F + 992) 16 (F + 1000) _ AG); [lia| lia| lia| lia| exact E2].
- apply (shz_agA M1 M2 (F + 992) 16 (F + 992) 2 AG); [lia| lia| lia| lia| exact E3].
Qed.
Lemma hsrc_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "O'R5&R@'8'>%2211(7&R4r1%211&QH%547721vE%;3821&Q<&RBv?+_@%3221+Y0%6221&QBvHr3%33821vIr4%63;21p041p091p0A1pW@N1").
Proof. intros src.
intros IQ O1 (SF & NI). pose proof HFF as (F8 & F0 & F1 & FB).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
assert (AG : PMFA.agA M1 M2 (F + 496) 288) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 496) 288 FR); [lia| lia| exact O1]).
split.
- apply (PMFA.src_fields_at_agreeA RSEGS M1 M2 (F + 488) (F + 96) (F + 112) src); [lia| lia| lia| lia| | | exact SF].
+ replace (F + 488 + 240) with (F + 728) by lia. eapply PMFA.agA_sub; [exact AG| lia| lia].
+ exact (blk_piece LBx FFx LKx crx Ax Mx Vx _ _ F rs slo shi Wp M1 M2 HH IQ HF HFF S1 S2 FR WP).
- apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M1 M2 (F + 496)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact NI].
Qed.
Lemma hvec_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q8'>'4'R3%211&R@'8%1266(7r3&RF+Q0&RG+2r2%3221%6251%94@@81vE%>3<21&Q<&RBv?+iH%3221+H%6221&QCvHr5r4%459321FvIr6%75<2154p041p0:1p0B1pWHQ21pV>Q61pV2Q71").
Proof. intros b k stk.
intros IB O1 (VE & D & A). pose proof HFF as (F8 & F0 & F1 & FB).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
assert (AG : PMFA.agA M1 M2 (F + 824) 24) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 824) 24 FR); [lia| lia| exact O1]).
split; [|split].
- apply (PMFA.vec_at_agreeA RSEGS M1 M2 (F + 824) b k stk); [lia| lia| lia| lia| exact (proj1 AG)| | exact VE].
exact (blk_piece LBx FFx LKx crx Ax Mx Vx _ _ F rs slo shi Wp M1 M2 HH IB HF HFF S1 S2 FR WP).
- exact (defined_agA M1 M2 (F + 824) 24 (F + 824) 24 AG ltac:(lia) ltac:(lia) D).
- apply (PMFA.accA_agree M1 M2 (F + 824) 24 (proj2 AG) A).
Qed.
Lemma hfin_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q8'R8'>&RA'8%1233&R7r2%211vE%73521&Q<&RBv?+Q0%3221+H%6221+SH%7261+8%:221+VH%;2:1+TH%>221&Q@vHr6r5%44A321vIr7%74D215p041p0:1p0?1p0D1p0L1pWBQ51pW2Q71").
Proof. intros s st.
intros INC O1 O2 O3 (VS & LC & IO). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG2 : PMFA.agA M1 M2 (F + 120) 8) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 120) 8 FR); [lia| lia| exact O2]).
assert (AG3 : PMFA.agA M1 M2 (F + 216) 152) by (apply (PMHAK.agA_frame M1 M2 Wp (F + 216) 152 FR); [lia| lia| exact O3]).
split; [|split].
- apply (vstr_keep_piece (F + 32) s); [exact INC| lia| lia| exact O1| exact VS].
- apply (u64_agA M1 M2 (F + 120) 8 (F + 120) _ AG2); [lia| lia| lia| lia| exact LC].
- apply (PMFA.iosb_at_agreeA RSEGS PMB.AD M1 M2 (F + 216)); [lia| lia| exact AG3| exact IO].
Qed.
End Objs.
Section ObjsC.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 4, rs) (FFx ++ LKx).
Hypothesis HFF : hf F.
Variables (LBc : list (Z * Z)) (FFc : list fframe) (spc scrc : Z) (Wc : list L5.range) (M1 M2 : word -> option byte) (f : fframe).
Hypothesis AH : L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2.
Hypothesis WF : wfi F Wc.
Hypothesis Hf : In f FFc.
Hypothesis HfF : ff_addr f = F /\ ff_bytes (ff_class f) = 1024.
Lemma vstr_keep_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q@'>'R8&RA'8%1244&R7r1%211vE%73521r2%611vD%;3921&RC&RBv?+Q0%3221r4%6221r5+H%8221+oH%:291%<231&QEvRLr6%33218&R9&R?&R<vHr7%5543217vIr8%8576214p041p0;1p0@1p0G1p0O1p0Q41pW2Q=1pVBQ?1").
Proof. intros o s.
intros INC INCc H0 H1 OA VS. pose proof HFF as (F8 & F0 & F1 & FB).
apply (PMFA.vstr_at_agreeA RSEGS M1 M2 o s); [lia| lia| | | exact VS].
- apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F o 24 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact OA].
- intros c n p E. assert (X : In (p, c) LBx) by (apply INC; rewrite E; left; reflexivity).
assert (Xc : In (p, c) LBc) by (apply INCc; rewrite E; left; reflexivity).
exact (blk_callee LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2 HH X HF HFF AH Xc WF).
Qed.
Lemma iss_keep_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QC'>'R8'R6&RA'8%1255&R7r2%211vE%73521r3%611vD%;3921&RC&RBv?+Q0%3221r5%6221r6+X@%8221+oH%:291%<231&QEvRLr7%33218&QJ&R?&QG&R<vHr8%67543218@vIr9%97876214;p041p0<1p0A1p0H1p0Q01p0Q51pW<Q>1pWJQ@1pVBQB1").
Proof. intros o str sm.
intros INC INCc H0 H1 OA IS. pose proof HFF as (F8 & F0 & F1 & FB).
apply (PMFA.iss_at_agreeA RSEGS PMB.AD M1 M2 o str sm); [lia| lia| | | exact IS].
- apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F o 272 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact OA].
- intros c n p E. assert (X : In (p, c) LBx) by (apply INC; rewrite E; left; reflexivity).
assert (Xc : In (p, c) LBc) by (apply INCc; rewrite E; left; reflexivity).
exact (blk_callee LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2 HH X HF HFF AH Xc WF).
Qed.
Lemma parser_keep_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QC'>'R2&RA'8%1244&R1r1%211vE%73521r2%611vD%;3921&RC&RBv?+Q0%3221r5%6221r6+\0%8221+oH%:291%<231&QEvRLr7%33218&R0&R?&QG&R<&R=vHr8%786543219AvIr9%:89876214<p041p0=1p0B1p0I1p0Q11p0Q61pVJQ?1pVDQA1pVFQB1").
Proof. intros op ois ps.
intros INC INCc H0 H1 OA PA. pose proof HFF as (F8 & F0 & F1 & FB). unfold PM.parser_own, PM.src_own, PM.vec_own in INC, INCc.
assert (IQ : In (PM.sr_qc (PM.p_src ps), PM.CHUNK) LBx) by (apply INC; left; reflexivity).
assert (IB : In (PM.p_b ps, 32 * 2 ^ PM.p_k ps) LBx) by (apply INC; right; left; reflexivity).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
apply (PMFA.parser_at_agreeA RSEGS PMB.AD M1 M2 op ois ps); [lia| lia| | lia| lia| | lia| lia| | | exact PA].
- apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F op 384 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact OA].
- exact (blk_callee LBx FFx LKx crx Ax Mx Vx _ _ F rs LBc FFc spc scrc Wc M1 M2 HH IQ HF HFF AH (INCc _ (or_introl eq_refl)) WF).
- exact (blk_callee LBx FFx LKx crx Ax Mx Vx _ _ F rs LBc FFc spc scrc Wc M1 M2 HH IB HF HFF AH (INCc _ (or_intror (or_introl eq_refl))) WF).
- intros c n p E. assert (X : In (p, c) LBx) by (apply INC; right; right; rewrite E; left; reflexivity).
assert (Xc : In (p, c) LBc) by (apply INCc; right; right; rewrite E; left; reflexivity).
exact (blk_callee LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2 HH X HF HFF AH Xc WF).
Qed.
Lemma hbase_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "QF'R8'R6&RA'8'>%2211&1&R7r2%211r3%411%63731vE%<3921r4%911%;3<61vD%A3>21&QEvRL&RBv?+Q0%3221+H%73621+S0%7261+X@%;3:21+]@%;2:1+8%?3>21&Q=vHr8r7r6%55B4321vIr9%85E2165p041p0;1p0@1p0E1p0N1p0Q41pW<QB1pW4QD1pW2QE1").
Proof. intros s s' sm.
intros INC INCc O1 O2 O3 (VS & IS & V1 & V2 & V3). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG : PMFA.agA M1 M2 (F + 432) 8) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 432) 8 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O3]).
assert (AGS : PMFA.agsh M1 M2 (F + 96) 272).
{ intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. destruct AH as (AK & _ & _). apply AK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|].
split.
- right; right; right; right; right; left. exists f. split; [exact Hf|]. destruct HfF as (E1 & E2). rewrite E1, E2. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
- intros r Hr Hin. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX, FB. destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia. }
split; [|split; [|split; [|split]]].
- apply (vstr_keep_callee (F + 32) s); [intros x Hx; apply INC; apply in_or_app; right; exact Hx| intros x Hx; apply INCc; apply in_or_app; right; exact Hx| lia| lia| exact O1| exact VS].
- apply (iss_keep_callee (F + 96) s' sm); [intros x Hx; apply INC; apply in_or_app; left; exact Hx| intros x Hx; apply INCc; apply in_or_app; left; exact Hx| lia| lia| exact O2| exact IS].
- apply (u64_agA M1 M2 (F + 432) 8 (F + 432) _ AG); [lia| lia| lia| lia| exact V1].
- apply (shz_agA M1 M2 (F + 432) 8 (F + 432) 1 AG); [lia| lia| lia| lia| exact V2].
- intros j Hj. unfold byte_at in *. specialize (V3 j Hj). rewrite (PMFA.S_granule (F + 96) j ltac:(lia) ltac:(lia)) in V3 |- *.
rewrite (AGS (F + 96 + 8 * j) ltac:(lia)). exact V3.
Qed.
Lemma hpar_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q2'R2&RA'8'>%2211&R1r1%211vE%83521r2%611vD%<3921&QEvRL&RBv?+^@%3221+\8%73621&QAvHr4%33821vIr5%63;21p041p091p0B1p0G1pVJQ11").
Proof. intros ps.
intros INC INCc O1 (PA & V1). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG : PMFA.agA M1 M2 (F + 464) 392) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 464) 392 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O1]).
split.
- apply (parser_keep_callee (F + 464) (F + 96) ps); [exact INC| exact INCc| lia| lia| intros r Hr; destruct (O1 r Hr); lia| exact PA].
- apply (u64_agA M1 M2 (F + 464) 392 (F + 848) _ AG); [lia| lia| lia| lia| exact V1].
Qed.
Lemma hec_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "E'>&QEvRL&RBv?+o0%3221+@%73621&Q>vHr3r2%449321vIr4%74<215p041p0:1pV4C1pWLD1").
Proof. intros v c.
intros O1 (E1 & E2 & E3). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG : PMFA.agA M1 M2 (F + 992) 16) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 992) 16 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O1]).
split; [|split].
- apply (u32_agA M1 M2 (F + 992) 16 (F + 992) _ AG); [lia| lia| lia| lia| exact E1].
- apply (u64_agA M1 M2 (F + 992) 16 (F + 1000) _ AG); [lia| lia| lia| lia| exact E2].
- apply (shz_agA M1 M2 (F + 992) 16 (F + 992) 2 AG); [lia| lia| lia| lia| exact E3].
Qed.
Lemma hsrc_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q6'R5&R@'8'>%2211(7&R4r1%211&QH%547721vE%;3821r2%811%:4<<16vD%@3=21&QEvRL&RBv?+_@%3221+Y0%73621&QBvHr4%33821vIr5%63;21p041p091p0B1p0H1pW@Q51").
Proof. intros src.
intros IQ IQc O1 (SF & NI). pose proof HFF as (F8 & F0 & F1 & FB).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
assert (AG : PMFA.agA M1 M2 (F + 496) 288) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 496) 288 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O1]).
split.
- apply (PMFA.src_fields_at_agreeA RSEGS M1 M2 (F + 488) (F + 96) (F + 112) src); [lia| lia| lia| lia| | | exact SF].
+ replace (F + 488 + 240) with (F + 728) by lia. eapply PMFA.agA_sub; [exact AG| lia| lia].
+ exact (blk_callee LBx FFx LKx crx Ax Mx Vx _ _ F rs LBc FFc spc scrc Wc M1 M2 HH IQ HF HFF AH IQc WF).
- apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M1 M2 (F + 496)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact NI].
Qed.
Lemma hvec_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q@'>'4'R3%211&R@'8%1266(7r3&RF+Q0&RG+2r2%3221%6251%94@@81vE%>3<21r4%928<%<2;1%?4FF31vD%D3B21&QEvRL&RBv?+iH%3221+H%73621&QCvHr6r5%459321BvIr7%75<2154p041p0:1p0C1p0J1pWHQ:1pV>Q>1pV2Q?1").
Proof. intros b k stk.
intros IB IBc O1 (VE & D & A). pose proof HFF as (F8 & F0 & F1 & FB).
destruct (PMHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
assert (AG : PMFA.agA M1 M2 (F + 824) 24) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 824) 24 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O1]).
split; [|split].
- apply (PMFA.vec_at_agreeA RSEGS M1 M2 (F + 824) b k stk); [lia| lia| lia| lia| exact (proj1 AG)| | exact VE].
exact (blk_callee LBx FFx LKx crx Ax Mx Vx _ _ F rs LBc FFc spc scrc Wc M1 M2 HH IB HF HFF AH IBc WF).
- exact (defined_agA M1 M2 (F + 824) 24 (F + 824) 24 AG ltac:(lia) ltac:(lia) D).
- apply (PMFA.accA_agree M1 M2 (F + 824) 24 (proj2 AG) A).
Qed.
Lemma hfin_callee : ltac2:(TCodec.tc2 tcn__PmBHarnessKit2 "Q>'R8'>&RA'8%1233&R7r2%211vE%73521r3%611vD%;3921&QEvRL&RBv?+Q0%3221+H%73621+SH%7261+8%;3:21+VH%;2:1+TH%?3>21&Q@vHr7r6%44A321vIr8%74D215p041p0:1p0?1p0D1p0M1p0Q21pWBQ;1pW2Q=1").
Proof. intros s st.
intros INC INCc O1 O2 O3 (VS & LC & IO). pose proof HFF as (F8 & F0 & F1 & FB).
assert (AG2 : PMFA.agA M1 M2 (F + 120) 8) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 120) 8 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O2]).
assert (AG3 : PMFA.agA M1 M2 (F + 216) 152) by (apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F (F + 216) 152 AH Hf); [lia| lia| exact HFF| lia| lia| exact WF| exact O3]).
split; [|split].
- apply (vstr_keep_callee (F + 32) s); [exact INC| exact INCc| lia| lia| exact O1| exact VS].
- apply (u64_agA M1 M2 (F + 120) 8 (F + 120) _ AG2); [lia| lia| lia| lia| exact LC].
- apply (PMFA.iosb_at_agreeA RSEGS PMB.AD M1 M2 (F + 216)); [lia| lia| exact AG3| exact IO].
Qed.
End ObjsC.
End K.
End PMHAK2.
