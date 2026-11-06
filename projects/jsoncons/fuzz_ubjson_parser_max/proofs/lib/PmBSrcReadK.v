(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmSpecsA PmSpecsAb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrcReadK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "1None"; "1S"; "1Some"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3Z"; "0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "4Model"; "4event"; "5bvmap"; "0M"; "0M'"; "0MV"; "0Mx"; "0R"; "0R'"]; ["6credit"; "6regs_preserved"; "7aacc"; "7aclient"; "7aclientw"; "7app_rng"; "7fframe"; "7hl_tp"; "7model_rt"; "7ri_inv"; "7vml_of"; "9defined"; "9ra_ok"; "8SCFG"; ":cfg"; ";FPState"]; [";getr"; ";rdn"; "<srealizes"; "=ahpres"; "=amodel_ok"; "=astk"; ">loaded_segments"; "0SCFG_P"; "?add"; "?le"; "?lt"; "?of_nat"; "?pow"; "0a"; "0ar"; "0b"]; ["0bs"; "0cr"; "0dst"; "0fx"; "0fx'"; "0i"; "0model"; "0model'"; "0n"; "0r"; "0sp'"; "0src"; "@Z_to_bv"; "@bv"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBSRK.
Import L5A. Import L5CA. Import L5SAR.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Lemma rdn_cons1R : ltac2:(TCodec.tc2 tcn__PmBSrcReadK "QJ'R=yR0%211'8y8%511%311p051'@'6'5%116&QIzr4%3221'<%>16&QA&QFr6&R<r5%22F1u1%746521(3(4(7%11H%33I@1%52D1%@3?71r7&QH+1%22@1%@2Q41%D4C51Hr3%>2M1%I3H31r8%F2Q::(2%11G%L4K431%D3Q:KQ1%F2Q51%Q13Q031p091p0C1p0Q51pT2Q:1pTBQ=1pT0QB1pSLQ@1pQJQB1").
Proof. intros MV a b n bs.
intros Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app RSEGS MV 1%nat n _ _ _ H1).
replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma rdn_of_defR : ltac2:(TCodec.tc2 tcn__PmBSrcReadK "R0'R=yR0%211'8y8%511%311p051'6'@&QIzr1%3221&QHr2&QKr3%211%5241&QL+2+QO%3221%>251';&QJr5%<11%32A1%52A1&>'<r7&R<%E28D%22Q31%411(1%11Q2%83Q231%:11p0<1pT<Q21'='5%11Q9%Q<11&QA&QF%@2QAGr6%443C21(3%128Q:%G3831qT2:1%=2;1p0?1p0Q31p0Q?1pSLQD1pTBQF1pQLQH1").
Proof. intros Mx n a.
revert a. induction n as [|n IH]; intros a Ha Hn Hd.
- exists []. reflexivity.
- destruct (Mx (Z_to_bv 64 a)) as [b|] eqn:Eb; [|exfalso; apply (Hd 0 ltac:(lia)); rewrite Z.add_0_r; exact Eb].
destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hr).
{ intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hd. lia. }
exists (b :: bs). apply (rdn_cons1R Mx a b n bs Ha); [cbn [rdn]; rewrite Eb; reflexivity | exact Hr].
Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma memcpy_call : ltac2:(TCodec.tc2 tcn__PmBSrcReadK "WH'Q?&Iy5'R=yR0%211%5241'8y8%611%311p061'G'5'H%211!pTN21':'@%2211%811&Q6%:11&Q0&Q9vBr:r9r8r7r6r=&Q:r<%211%;8:9876541&QD%1286(7%11J%911'<&Q@rA&R<&QKu1%211%42Q?1%7261%62Q?E%:3Q?21&Q<%11IrCu2%;11%=2QH1%@241%?2QHQ1%C3QH21rDu4%B11%D2QO1%G241&Q7vD%211%I2R21%M3R251rEu:%L11%N2R91%Q1241%Q33R81ArFu;%Q211%Q42R?1%Q7241%Q93R>1GrGu<%Q811%Q:2RE1%Q=241%Q?3RD1M';&QIzr;%3221+`P0%5231%7231&QEvQNrHr@+R`0%544321&Q2rIr?%3321R;r1%B2A1&QJ%1235%F231&Q4&QHrBr2%3221%57QBC=BQH@1p071pT<S51&Q;rK%231R?A%Q12Q09%;2R6RA&QL+2+Q?%3221%Q7251&Q5%13Q1R6ArO%N31R8R?%Q<2Q;QO%F2QJR0%Q>218%73Q7QFQL%M2OQ7%QB2O1&Q3rQ2rQ1rMrJ%Q021N%67R?Q@543Q=1p081pT<T21rQ4%N31Q>QC'?%Q72OQ@%QO219%Q92:QB%R121Q2%5231&Q1rQ;r3%3221%Q932CM&QCrQ9rQ8(4(9rQ0%24TFTFK1%T31TF%53TG21rQ<r4%;9S:R;:9HR8321&Q8%1243rQ7r5%T>221rQ:%TD1TF%TM8TL:G2BATH1'QB&QF&Q=vQG%211&Q>%165U2U1<U0TOrQ>%847421p0:1p0>1p0B1p0E1p0Q21p0Q41pT@UJ1pQHUL1pR0V21pT:V91+^m`<rQ6%@6DQ8Q72K1rQ5%G4FC21p061p0QC1p0QJ1p0QM1p0R91p0R;1p0R>1p0R@1p0RC1p0RF1p0RM1p0RO1p0S31p0SA1p0SF1p0SM1p0T61p0T=1p0TD1p0TK1p0U61p0U>1p0UA1p0UM1p0V11p0V41pTBVF1pTHVG1pT6VH1pTDVI1pTFVJ1p2VI1pT4VG1pQ>VI1pQ4VJ1pQ<VM1pQ8W21pT>W81pQFW:1pQNW@1pT8WG1").
Proof. intros fx R M model K LB FF LK cr Aw sp' r dst src n.
intros HH AM HK G1 RA G2 G4 G10 G11 G12 Hn ASTK ACD CLD DDEF D0 D1 APD ACS S0 S1 APS CLS SDEF0 NOV KONT.
pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as HF.
unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in HF. rewrite (aly_segs L C LYa), (aly_scr_mem L C LYa), (aly_memcpy L C LYa) in HF.
pose proof ASTK as (A16 & SLO & SHI & SPT & SD & SU).
assert (U2 : bv_unsigned (getr R 2%bv) = sp') by (rewrite L5K.rl2, G2; apply L5.unsigned_lit; clear - SLO SHI SPT; lia).
destruct (rdn_of_defR M (Z.to_nat n) src S0 ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN).
{ intros i Hi. rewrite Z2Nat.id in Hi by lia. apply SDEF0. lia. }
unfold PMSPA.cfg.
eapply (HF fx R M model LB FF LK cr Aw dst src n bs K); clear HF.
- split. exact HH. split. exact (proj1 AM). split. exact (proj2 AM).
split. rewrite L5K.rl10. exact G10. split. rewrite L5K.rl12. exact G12. split. lia.
split. rewrite L5K.rl4. exact G4.
split. rewrite L5K.rl1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
split. { rewrite U2. pose proof (astack_ok_of_astk L ar C LYa M M sp' 2560 0 2560 ASTK (mem_grows_refl M)) as X.
replace (sp' - 0) with sp' in X by (clear; lia). apply X; [clear; lia| clear; lia| clear; lia| replace (sp' - 0) with sp' by (clear; lia); exact A16]. }
split. exact ACD.
split. { intros i Hi. rewrite U2. apply CLD. exact Hi. }
split. { intros i m0 Hi Hm. apply (L5C.writable_of_defined RSEGS M dst n DDEF D0 ltac:(clear - D1; lia)). exact Hi. exact Hm. }
split. exact HK. exact APD.
- rewrite L5K.rl11. exact G11.
- exact ACS.
- split; [exact S0| exact S1].
- exact APS.
- intros i Hi. right. rewrite U2. apply CLS. exact Hi.
- exact RDN.
- intros _. exact NOV.
- intros R' M' model' mR10 RP BYTES PRES SDEF RT2 MI2 HH2. rewrite U2 in PRES, SDEF. rewrite L5K.rl1, G1 in *.
apply (KONT fx R' M' model' RP).
+ intros i Hi. destruct (BYTES i Hi) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
+ split; [|split].
* intros a (Ha & Hc & Ho). apply PRES; [exact Ha| exact Hc|]. intros X. apply (Ho (dst, n)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X].
* intros i Hi. apply SDEF. clear - Hi; lia.
* intros a Ha Hc D. destruct (L5SAR.rng_dec a dst (dst + n)) as [X|X].
-- destruct (BYTES (a - dst) ltac:(clear - X; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (dst + (a - dst)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
-- rewrite (PRES a Ha Hc X). exact D.
+ exact RT2.
+ split; [rewrite (L5LZ.model_rt_halted _ _ RT2); exact (proj1 AM)| exact MI2].
+ exact HH2.
Qed.
End WithIface.
End SCFG_1.
End PMBSRK.
