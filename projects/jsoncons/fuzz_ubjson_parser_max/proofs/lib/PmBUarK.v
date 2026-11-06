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
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBUarK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBUarK.PMBUK.SCFG_1.WithIface.CTX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreSpecsAB0.L5CSA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A1"; "0Ac"; "0BX"; "0BX1"; "0BXa"; "1None"; "1app"; "1cons"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"]; ["3Z"; "0D"; "0F"; "0FF"; "0G"; "0HI"; "0K"; "0L"; "0LB"; "0LK1"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M9v"]; ["0Mc"; "0Mf"; "0R9"; "0Rc"; "6mrestrict"; "7msteps"; "8credit"; "9SB"; "9aclient"; "9aclientw"; "9ahid"; "9cell_is"; "9ff_bytes"; "9fframe"; "9model_rt"; "9ri_inv"]; ["9vml_of"; ";defined"; ";img_clear"; ";in_rng"; ";outside"; ";range"; ";u32_at"; ";u64_at"; ";u8_at"; ";writable"; ":SCFG"; "<avis"; "=Wret"; "=WretX"; "=binv"; "=gctx"]; [">FPState"; ">mkst"; ">seg_rom"; "?TSet"; "@srealizes"; "Amem_grows"; "Bahpres"; "Bamodel_ok"; "Ccfg"; "Dloaded_segments"; "0SCFG_P"; "0SCR"; "0SCRc"; "EIn"; "Eincl"; "Fadd"]; ["Fdiv"; "Fle"; "Flt"; "Fpow"; "Fsub"; "0W"; "0W1"; "0Wc"; "0Wp"; "0Wx"; "0a"; "0ar"; "0cr1"; "0crc"; "0fl"; "0fx"]; ["0fx9"; "0k"; "0model"; "0model1"; "0modelc"; "0modelf"; "0ocell"; "0own"; "0pc"; "0r"; "0rr"; "0scr"; "0sp"; "0spc"; "GZ_to_bv"; "Gbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMBUK.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import L5CBR. Import L5ADHR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Local Abbreviation statics_vis := (L5ADHR.statics_vis L ar C HI LY HIok).
Section CTX.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
(sp SCR : Z)
(spc olo ohi : Z)
(ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
(F fl : Z) (k : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit) (BX0 : list (Z * Z)).
Local Notation B := (ff_bytes k).
Local Notation FF' := ((F, k, spc + 32) :: FF).
Record gctx : Prop := GCTX {
g_k : In k [0; 1; 2; 3; 4];
g_SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47;
g_SLO : ahl_ceil ar + 4096 + SCR <= sp;
g_SHI : sp <= ar_sptop ar;
g_SPC : 0 <= spc /\ sp - SCR <= spc /\ spc <= olo /\ olo <= ohi /\ ohi <= sp /\ 0 <= SCR /\ sp <= 2 ^ 47;
g_OCR : forall a, ocell a -> olo <= a < ohi;
g_OWN : forall M1 M1', own M1 -> (forall a, ocell a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own M1';
g_FS1 : ar_fs ar <= F;
g_FS2 : F + B <= ar_fs ar + FS_BYTES;
g_FCEIL : F + B <= ahl_ceil ar;
g_LKI2 : incl LK2 LK;
g_FLP : ar_fs ar <= fl < ar_fs ar + FS_BYTES;
g_FLNC : ~ aclient L ar LB FF' 0 0 fl;
g_HH2 : ri_inv HI (BX0 ++ LB) FF' LK2 cr2 A M2 (vml_of model2);
g_FLC : cell_is RSEGS M2 (F + B - 8) 8 fl;
g_FR : 4096 <= F /\ F + B <= 2 ^ 47 /\ 6893568 <= F /\ 64 <= B <= 1024;
g_F8 : F / 8 * 8 = F /\ (F + B - 1) / 8 = F / 8 + B / 8 - 1 /\ B / 8 * 8 = B;
g_FBIG : 2147446784 + 17592186048512 <= F \/ F + B <= 2147446784;
g_F32 : F mod 32 = 0;
g_FLA : F + B <= fl \/ fl + 1 <= F;
g_FLR : 4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ 6893568 <= fl /\ fl + 1 <= ahl_ceil ar;
g_FLBIG : 2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784;
g_NCF : forall a : Z, F <= a < F + B \/ S F <= a <= S (F + B - 1) -> ~ aclient L ar LB FF sp SCR a;
g_NCS : forall a : Z, spc <= a < sp -> ~ aclient L ar LB FF sp SCR a
}.
Ltac open_gctx G :=
destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
Definition binv (W : list L5.range) (BX : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of modelc) /\ amodel_ok Ac modelc /\ model_rt model modelc /\ incl A Ac /\ incl LKc LK /\
astk ar Mc sp SCR /\ ek L ar LB FF sp SCR W M Mc /\ dk L ar LB FF sp SCR M Mc /\ own Mc /\ L5.defined Mc (F / 8 + SB) (B / 8).
Lemma binv_model : ltac2:(TCodec.tc2 tcn__PmBUarK "R5'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6&QNr8r7r6r5r4r3r2%877654321&Q?vE&6vH%23K<1(7%O2MN(:vBvS1%34Q2Q221&R?vS=+Q0%3221%84Q6Q751vC%<3;21&Q@%11E%D8C@3IHGK1&R7%12JI&Q>%12Q0Lr<r;r:%Q57321Q1Q4Q3Q2p051p081p0;1p0Q11pV8Q>1p4QH1pULQ=1pQFQ?1pV:QB1pR2QD1p6QM1pU<R21").
Proof. intros W BX Mc modelc LKc crc Ac model1.
intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1. unfold binv.
split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5. split. exact B6. split. exact B7. split. exact B8. split. exact B9. exact B10.
Qed.
Lemma binv_piece : ltac2:(TCodec.tc2 tcn__PmBUarK "T:'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6!p0@1&QNr:r9r8r7r6r5r4%877654321&Q?vE&6vH%23M<1(7%Q12OQ0(:vBvS1%34Q4Q421&R?vS=+Q0%3221%84Q8Q951vC%<3;21&Q@r3%211%E8DA4JIHG1&R7%12KI&Q>%12Q1L&R5r<%221Q1'<&RAzr1%3221&RB&RC+2+R0%3221%5271%;271&>r2%QA11%311'=r;&S>%12R6M%311r@%113%73R531p091p0>1pUFRA1%QN1H'?%L2Q>@vS<%J2B1%Q0231vS6%11E%G11%Q4241%Q42QJH&Q<%11QK%QJ2QM1%Q42L1%Q:251&R@+8%22R21&Q7%R1221%Q?21Q3%62:5%R4231%Q>2Q61%QD241%I2;1%J2B1p0L1pUFS?1rAr=%S172Q6S0RO1QMQ:p041p0Q31p0QO1p0R31p0R61p0R91p0S01pUBS:1pV8S@1pQNSB1p4SK1pULS@1pQFSB1pV:SE1pR2SG1p6T01pU<T51pQ:T91").
Proof. intros G W BX Mc modelc LKc crc Ac M1 model1 Wp.
open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 MG FRM WP.
unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
split. eapply astk_grows. exact B6. exact MG.
split. { eapply ek_trans. exact B7. apply (ek_piece L ar LB FF sp SCR W Mc M1 Wp FRM). intros a Ha Hc _ X. destruct (WP a X) as [Y|[Y|Y]].
- apply (NCS a). exact (proj1 Y). exact Hc.
- apply (NCF a). left; exact Y. exact Hc.
- apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - Y. unfold SB in Y |- *. lia. exact Hc. }
split. { eapply dk_trans. exact B8. apply dk_grows. exact MG. }
split. { apply (OWNAG Mc M1 B9). intros a Ha. apply FRM. pose proof (OCR a Ha). clear - H SPC SLO. lia.
intros X. destruct (WP a X) as [Y|[Y|Y]]. exact (proj2 Y Ha). pose proof (OCR a Ha). clear - H Y SPC SLO FCEIL. lia.
pose proof (OCR a Ha). clear - H Y SPC SLO SPT FR F8. unfold SB in Y. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia. }
eapply L5.defined_grows. exact MG. exact B10.
Qed.
Lemma binv_mem : ltac2:(TCodec.tc2 tcn__PmBUarK "U3'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6!p0@1&QNr;r:r9r8r7r6r5%877654321&Q?vE&6vH%23M<1(7%Q12OQ0(:vBvS1%34Q4Q421&R?vS=+Q0%3221%84Q8Q951vC%<3;21&Q@r4%211%E8DA4JIHG1&R7%12KI&Q>%12Q1L'<&RAzr1%3221&RB&RC+2+R0%3221%5271%;271&Q8vGvRKr@%Q83R31Q7r2%67542KQ0Q@1&>r3%QE11%311'=r<&S>%12R:Q1%311rA%113%73R931p091p0>1p0F1pUFRF1&RD%12QBR2%Q421Q2%Q12Q3QD%Q7221%?2RHG%R;11(5%11RG%E3RG31%J11p071pUFS31%R@1Q=%I19%K3RM17%Q011p041pUFS91'?%RH1QD%Q511%3221pUFS>1%RM1QH%R;2R>R9%QL21Q<&Q<%11R@%R?2RB1+8%O221%QN2QB1%R4271p0:1pUFSJ1vS<vR;%Q6221%Q72RHS;%R:221%R;2R:S>rFrEr?r>rB%SE754321QFR3p071p091p0?1p0L1p0Q21p0Q91p0QG1p0RK1p0RN1p0S11p0SH1pVHTB1pQ4T31pV8T91pQNT;1p4TD1pULT91pQFT;1pV:T>1pR2T@1p6TI1pU<TN1pQ:U21").
Proof. intros G W BX Mc modelc LKc crc Ac M1 model1 D scr.
open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 PRES SDEF DDEF DDEC DIN HS HS0.
assert (PRES' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF spc scr a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha Hc ND. apply PRES. exact Ha. apply aclient_cons. apply aclient_appb. exact Hc. exact ND. }
unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
split. { apply (astk_after_eq L ar C HI HIok (BX ++ LB) FF' LKc crc Ac Mc Mc M1 _ sp _ spc scr B1 B6 (mem_grows_refl Mc)).
- intros a Ha Hs Hns. apply PRES. exact Ha. apply stack_client. exact Hs. exact Hns. intros X. apply DIN in X. clear - X Hs FR FCEIL; lia.
- exact SDEF.
- exact HS.
- clear - SPC; lia.
- clear - SPC; lia. }
split. { eapply ek_trans. exact B7. apply (ek_mem L ar LB FF sp SCR spc scr D W Mc M1 PRES').
- exact HS.
- clear - SPC; lia.
- intros a Hc _ X. apply DIN in X. apply (NCF a). left; clear - X FR; lia. exact Hc. }
split. { eapply dk_trans. exact B8. apply (dk_mem L ar LB FF sp SCR spc scr D Mc M1 PRES' SDEF DDEF DDEC).
- exact HS.
- clear - SPC; lia. }
split. { apply (OWNAG Mc M1 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply PRES. clear - OC SPC SLO; lia. apply stack_client. clear - OC SPC SLO SHI SPT; lia. clear - OC SPC HS0; lia.
intros X. apply DIN in X. clear - X OC SPC SLO FCEIL. lia. }
intros i Hi. rewrite PRES. apply B10. exact Hi.
- clear - Hi FR F8. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
- apply (fframe_shadow_client L ar (BX ++ LB) FF' spc scr F k (spc + 32)). left; reflexivity. unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Hi. lia.
- intros Y. apply DIN in Y. clear - Y Hi FR F8 FBIG. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
Qed.
Lemma binv_callee : ltac2:(TCodec.tc2 tcn__PmBUarK "TK'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6&QNrAr?r<r;r:r9r8%877654321&R6vGvRK&6vH%23L<1(7%Q02NO(:vBvS1%34Q3Q321&R?vS=+Q0%3221%84Q7Q851vC%<3;21r3r2r=%F9EDA49321H&Q?vEr7r6r5&Q@%11O%786I<543Q11&R7%126Q3&Q>%12Q9Q6&R>%13QK?Q6r@%33QBQ;1&RAz%221Q<&RDvS<vR;%3221%42Q1QB%8221&R=%13R<MQG&QC%12Q0O'<&>vS6%11Q4%311&R@+8%22QB1&Q7%QA221%G21Q;&RB&Q<%11QG%9218%QG261%52QA1%A271%A11%C2?1p0E1p0H1pUFS21pVFS61&Q8r1%27R=R<R:QMQ3Q21&QDrL%221QMr>%421R0p031p071pUFS>1%827:rN%:21R5p031pUFSC1rIrCrB%S87?321S7QJS6p051p0;1p0G1p0QD1p0QK1p0QO1p0R21p0R51p0R81p0R;1p0RD1p0S<1pU@T61pTJT51p2T41pUJSI1pQDSK1pV8SN1pQNT01p4T91pULSN1pQFT01pV:T31pR2T51p8T>1p:T?1p6T@1pU>TE1pU<TF1pQ:TJ1").
Proof. intros G W W1 BX BXa BX1 Mc modelc LKc crc Ac M1 model1 LK1 cr1 A1 SCRc Wc.
open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) AH HH1 AM1 RT1 IA1 ILK1 HS0 HS WAV WOUT WW.
unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1.
split. { intros x Hx. apply IA1. apply B4. exact Hx. } split. { intros x Hx. apply B5. apply ILK1. exact Hx. }
split. { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ (BXa ++ LB) FF' Mc Mc M1 sp SCR spc SCRc Wc B1 B6 (mem_grows_refl Mc) AH).
- exact HS.
- clear - SPC; lia.
- clear - SPC; lia. }
split. { eapply ek_trans. { apply (ek_W L ar LB FF sp SCR W1 W M Mc B7). exact WW. }
apply (ek_callee L ar LB BXa FF [(F, k, spc + 32)] sp SCR spc SCRc W1 Wc Mc M1 AH).
- exact HS.
- clear - SPC; lia.
- exact WOUT. }
split. { eapply dk_trans. exact B8. apply (dk_callee L ar LB BXa FF [(F, k, spc + 32)] sp SCR spc SCRc Wc Mc M1 AH).
- exact HS.
- clear - SPC; lia. }
split. { apply (OWNAG Mc M1 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply (proj1 AH). split. clear - OC SPC SLO; lia.
split. apply stack_client. clear - OC SPC SLO SHI SPT; lia. clear - OC SPC HS0; lia.
intros rr Hr X. exact (proj1 (WAV rr a Hr X) Ha). }
intros i Hi. apply (proj2 (proj2 AH)).
- clear - Hi FR F8. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
- apply (fframe_shadow_client L ar (BXa ++ LB) FF' spc SCRc F k (spc + 32)). left; reflexivity. unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Hi. lia.
- apply B10. exact Hi.
Qed.
Lemma vis_facts : ltac2:(TCodec.tc2 tcn__PmBUarK "S>'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6&QNr7r6r5r4r3r2r1%877654321'<&QI&R9&Q4&Q:%128;%321=vS=&RDvS<%2213%:49541&QB+QUdP0+QVhP0%33921&QG+QWbaH+QoooPP0%34A=21&QF+QWbb0+1%34EA21+QVhm@+QTjo8%:4HD21%K241%L291%M2>1%N2C1vS7%11J&QAvB&Q<vS1%211%53Q041%Q64Q5Q152&R?&R@+8%2291&Q7%5221%5294%Q>4Q=Q921%82>;%Q9217vRN%Q34QAQ=21%QC4QBQ>2N%QE221%QF271%QG2@1%QH2B1&Q;u8%25QIR2:19&QK%13QH;Q7%23QILI%33QJQHQE%43QKCB%R1221%R2241%R3261%R4291%R52=1%R62Q61%R72Q91p0R91p4RO1pULRD1pQFRF1pV:RI1pR2RK1p6S41pU<S91pQ:S=1").
Proof. intros G W BX Mc modelc LKc crc Ac.
open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS8 & VIMG8 & VFS8 & _ & _ & VFSSH8 & _).
pose proof (statics_vis (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (IMGC8 & CSB8 & CUAR8).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as ST. rewrite (aly_segs L C LY) in ST.
pose proof (statics_facts L C Mc LY ST) as (_ & _ & _ & RMS & _).
set (H8 := ahid Ac modelc) in *. set (MV8 := mrestrict H8 Mc) in *.
assert (SV8 : avis H8 spc (sp - spc)). { apply (VIS8 spc (sp - spc)). clear - SPC SLO; lia. clear - SPC; lia. }
assert (FV8 : avis H8 F B) by (apply (VFS8 F B FS1 FS2)).
assert (SHV8 : avis H8 (F / 8 + SB) (B / 8)).
{ apply (VFSSH8 (F / 8 + SB) (B / 8)). intros i Hi. unfold in_shadow_of, S.
pose proof (Z.div_le_mono (ar_fs ar) F 8 ltac:(clear; lia) FS1) as X1. pose proof (Z.div_le_mono (F + B - 1) (ar_fs ar + FS_BYTES - 1) 8 ltac:(clear; lia) ltac:(clear - FS2; lia)) as X2.
destruct F8 as (_ & X3 & _). clear - Hi X1 X2 X3. lia. }
assert (WSv : L5.writable RSEGS MV8 spc (sp - spc)).
{ apply (proj2 (writable_vis H8 Mc spc (sp - spc) SV8 ltac:(clear - SPC; lia) ltac:(clear - SPC; lia))).
eapply (astk_writable ar Mc sp). exact B6. clear - SPC; lia. clear; lia. clear - SPC; lia. }
assert (OWN8v : own MV8). { apply (OWNAG Mc MV8 B9). intros a Ha. pose proof (OCR a Ha) as OC. apply mrestrict_visible. replace a with (spc + (a - spc)) by (clear; lia). apply SV8. clear - OC SPC; lia. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & WF8 & _).
assert (FDEF8 : L5.defined MV8 F B). { apply (proj2 (defined_vis H8 Mc F B FV8)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF8 _ (or_introl eq_refl))))))). }
assert (FW8 : L5.writable RSEGS MV8 F B). { apply (L5C.writable_of_defined RSEGS). exact FDEF8. clear - FR; lia. clear - FR; lia. }
assert (FSHW8 : L5.writable RSEGS MV8 (F / 8 + SB) (B / 8)).
{ apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H8 Mc _ _ SHV8)). exact B10.
clear - FR. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
clear - FR F8. unfold SB. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H. lia. }
pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ modelc F k _ _ fl HH2 B1 (or_introl eq_refl) (or_introl eq_refl) Hk FLC) as [FLC8 FL8].
pose proof (fl_writable L ar C HI LY HIok _ FF' LKc _ Ac Mc _ fl B1 FLP) as [FLD8 FLW8].
pose proof (fl_vis L ar C HI LY HIok _ FF' LKc _ Ac Mc modelc fl B1 FLP) as FLV8.
assert (FLW8v : L5.writable RSEGS MV8 fl 1). { apply (proj2 (writable_vis H8 Mc fl 1 FLV8 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW8. }
assert (RMSv : L5.u64_at RSEGS MV8 1270704 1207272). { apply (proj2 (u64_at_vis H8 Mc 1270704 1207272 (VIMG8 1270704 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact RMS. }
split. { split. exact WSv. split. exact IMGC8. split. exact CSB8. split. exact CUAR8. exact RMSv. }
split. exact OWN8v.
split. { split. exact FDEF8. split. exact FW8. split. exact FSHW8. split. exact FL8. exact FLW8v. }
split. exact FLC8. split. exact FLV8. split. exact FV8. split. exact SV8. exact SHV8.
Qed.
Definition Wret (a : Z) : Prop := (F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + B / 8) \/ a = fl.
Lemma retire_core : ltac2:(TCodec.tc2 tcn__PmBUarK "U1'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6'R0&Ly5%221=&R3&QNr?r>r=r<r;r:r9%877654321'Q5&R9&R1r7&S>r6%22O1&Q4&Q:%12<?%321A&R2%11;%;5?:731r8r5r4%=2Q:1r3%A554217%D3C71&R5%>2JM%@21O%3218'<&RAzr1%3221&RB&RC+2+R0%3221%5271%;271&>&QLr2%211%411'=%Q72R4I%N11rB%Q62QF1rC%Q93215%73R551p091p0?1pUFRA1&QHvRN%24QFQB1L%Q91=rG%11?%A3R?31p0C1p0I1pUFRK1&R6vGvRKvHvCvS<vR;vM%89765432>1QE&Q>vS2%221QH&R7%12MQL&Q?vE&6rI%23S=1?rFrErD&Q@%11R7%:896D543RB1'R4&QJvR:%211&R8r@%25Q?1S6RKRI%74RN41S5p091p0E1p0H1p0L1p0Q61pV<SG1pR4SI1%;5S>S<S;QHQJ%@4S7=1S5p031p0QC1p0QG1p0RD1p0RI1p0S?1pQ>SI1pR0T31pVDT>1pR6SM1pVBT@1pR8SO1pV2T31pV0T41p4TB1pULT71pQFT91pV:T<1pR2T>1p6TG1pU<TL1pQ:U01").
Proof. intros G W BX Mc modelc LKc crc Ac fx fx9 Rc pc R9 r M9v K.
intros BI wMS MG9 wFZ wFL0 KF.
destruct (vis_facts G W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (FLC8 & FLV8 & _)).
pose proof G as G'. open_gctx G'. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
assert (FLNC8 : ~ aclient L ar (BX ++ LB) FF' 0 0 fl).
{ apply (not_client_bx L ar FF' fl BX LB). apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LB B1 eq_refl). exact FLP. exact FLBIG. exact FLNC. }
apply (apiece_retire L ar C HI LY HIok (BX ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 r M9v Wret F k (spc + 32) fl K B1 B2).
{ exact FLC8. }
{ exact FLNC8. }
{ exact FLV8. }
{ clear - FLR; lia. }
{ exact wMS. }
{ exact MG9. }
{ exact wFZ. }
{ intros a Ha Wa. unfold Wret in Wa. destruct Wa as [[Wa|Wa]|Wa].
- right. apply (fframe_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity. clear - Wa FR; lia.
- right. apply (fframe_shadow_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity.
unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Wa. unfold SB in *. lia.
- left; exact Wa. }
{ intros a. unfold Wret. repeat match goal with X : _ |- _ => clear X end.
destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + ff_bytes k / 8)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
{ exact wFL0. }
intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
assert (ASTK9 : astk ar M9 sp SCR). { eapply astk_grows. exact B6. exact MGM9. }
apply (KF M9 model9).
- exact FRM9.
- apply ahpres_of.
+ eapply ek_trans. exact B7.
intros a (Ha & Hc & Ho). apply FRM9. exact Ha. unfold Wret. intros [[X|X]|X].
* apply (NCF a). left; clear - X FR; lia. exact Hc.
* apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - X. unfold SB in X |- *. lia. exact Hc.
* subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
+ eapply astk_defined. exact ASTK9. clear - SPC; lia. clear; lia.
+ eapply dk_trans. exact B8. apply dk_grows. exact MGM9.
- eapply L5LZ.model_rt_trans. exact B3. exact RT9.
- exact AM9.
- exact HH9.
Qed.
Lemma binv_pieceW : ltac2:(TCodec.tc2 tcn__PmBUarK "T?'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6!p0@1&QNr:r9r8r7r6r5r4%877654321&Q?vE&6vH%23M<1(7%Q12OQ0(:vBvS1%34Q4Q421&R?vS=+Q0%3221%84Q8Q951vC%<3;21&Q@r3%211%E8DA4JIHG1&R7%12KI&Q>%12Q1L&R5r<%221Q1'<&RAzr1%3221&RB&RC+2+R0%3221%5271%;271&>r2%QA11%311'=r;&S>%12R6M%311r@%113%73R531p091p0>1pUFRA1%QN1HvS6%11@%B11'?%O2QACvS<%M2E1%Q3231%Q32QIG&Q<%11QJ%QI2QL1%Q32K1%Q9251&R@+8%22R11&Q7%R0221%Q>21Q2%62:5%R3231%Q=2Q51%QC241&QDrB%221Q9%Q;11%I251%J2@1%K2G1%QK2M1p0Q11pUFSD1rAr=%S672Q;S5S41R2Q?p041p0Q81p0R41p0R81p0R;1p0R>1p0S51pUBS?1pV8SE1pQNSG1p4T01pULSE1pQFSG1pV:SJ1pR2SL1p6T51pU<T:1pQ:T>1").
Proof. intros G W BX Mc modelc LKc crc Ac M1 model1 Wp.
open_gctx G. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 MG FRM WP.
unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
split. eapply astk_grows. exact B6. exact MG.
split. { eapply ek_trans. exact B7. intros a (Ha & Hc & Ho). apply FRM. exact Ha. intros X. destruct (WP a X) as (_ & [Y|[Y|[Y|Y]]]).
- apply (NCS a). exact Y. exact Hc.
- apply (NCF a). left; exact Y. exact Hc.
- apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - Y. unfold SB in Y |- *. lia. exact Hc.
- exact (Y Ho). }
split. { eapply dk_trans. exact B8. apply dk_grows. exact MG. }
split. { apply (OWNAG Mc M1 B9). intros a Ha. apply FRM. pose proof (OCR a Ha). clear - H SPC SLO. lia.
intros X. exact (proj1 (WP a X) Ha). }
eapply L5.defined_grows. exact MG. exact B10.
Qed.
Definition WretX (Wx : Z -> Prop) (a : Z) : Prop := Wret a \/ Wx a.
Lemma retire_coreW : ltac2:(TCodec.tc2 tcn__PmBUarK "V?'QO'8&QE%211';'@%2211%611'S?yR0%211'9y8%511%311p051'K&Q=%A11&Q6!p0@1'R0&Ly5%221?&R3&QNr@r?r>r=r<r;r:%877654321r1%411'<&Q9vGvRK&6rBvH%33Q721(7%Q;2Q9Q:(:vBvS1%34Q>Q>21&R?vS=+Q0%3221%84QBQC51vC%<3;21zr2%F7ED@3221&>&QDrC%2215%411%M261p0O1pUFR01'?%Q71Q3%:11%3221pUFR51'Q5&R9&R1r9&S>r8%22R81&Q4&Q:%12QEQHrA%4221&R2%11<%<5QH;831r7r6%=2RC1r5%A5QL4216%D3C61&R5%>2R3<%@21QG%3218&RA%12Q:R1&RB&RC+2+R0%3221%52R71%R6271&QM%12RBQB%QA11'=r3%Q32S91%RA11rE%Q22R:1rF%Q53215%83S:51p0:1p0>1pUFSF1&QHvRN%24QBQ>1R3rD%C21R4%R311%Q51@rJ%11B%E3SG31p051p0K1pUFT31rH%Q:21I%QH2G2r4%QK221%N3SO1S?&R6vS<vR;rLvM%59S<S;S8RK4321QG&Q>vS2%221QJ&R7%12@QN&Q?vErN%SC3TG1SArKrI&Q@%11R7%8875S94O3RB1'R4&QJvR:%211&R8rG%251Q:S9RKRI%74RN41REp091p0C1p0F1p0J1p0Q11p0Q61p0Q91pV<U21pR4U41%=5THTFTEQNR0%B4S9?1S7p031p0QI1p0QM1p0RF1p0RK1p0SA1p0SG1p0TJ1pQ>U41pR0U@1pVDUK1pR6U81pVBUM1pR8U:1pV2U>1pV0U?1pUDUA1p4V01pULUE1pQFUG1pV:UJ1pR2UL1p6V51pU<V:1pQ:V>1").
Proof. intros G W BX Mc modelc LKc crc Ac Wx fx fx9 Rc pc R9 r M9v K.
intros BI WX WXD wMS MG9 wFZ wFL0 KF.
destruct (vis_facts G W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (FLC8 & FLV8 & _)).
pose proof G as G'. open_gctx G'. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
assert (FLNC8 : ~ aclient L ar (BX ++ LB) FF' 0 0 fl).
{ apply (not_client_bx L ar FF' fl BX LB). apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LB B1 eq_refl). exact FLP. exact FLBIG. exact FLNC. }
apply (apiece_retire L ar C HI LY HIok (BX ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 r M9v (WretX Wx) F k (spc + 32) fl K B1 B2).
{ exact FLC8. }
{ exact FLNC8. }
{ exact FLV8. }
{ clear - FLR; lia. }
{ exact wMS. }
{ exact MG9. }
{ exact wFZ. }
{ intros a Ha Wa. unfold WretX, Wret in Wa. destruct Wa as [[[Wa|Wa]|Wa]|Wa].
- right. apply (fframe_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity. clear - Wa FR; lia.
- right. apply (fframe_shadow_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity.
unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Wa. unfold SB in *. lia.
- left; exact Wa.
- right. exact (proj1 (WX a Wa)). }
{ intros a. unfold WretX, Wret. destruct (WXD a) as [X|X]; [left; right; exact X|].
destruct (rng_dec a F (F + 8)); [left; left; left; left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + ff_bytes k / 8)); [left; left; left; right; tauto|].
destruct (Z.eq_dec a fl); [left; left; right; exact e|]. right. intros [[[Y|Y]|Y]|Y]; tauto. }
{ exact wFL0. }
intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
assert (ASTK9 : astk ar M9 sp SCR). { eapply astk_grows. exact B6. exact MGM9. }
apply (KF M9 model9).
- exact FRM9.
- exact MGM9.
- exact VIS9.
- apply ahpres_of.
+ eapply ek_trans. exact B7.
intros a (Ha & Hc & Ho). apply FRM9. exact Ha. unfold WretX, Wret. intros [[[X|X]|X]|X].
* apply (NCF a). left; clear - X FR; lia. exact Hc.
* apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - X. unfold SB in X |- *. lia. exact Hc.
* subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
* exact (proj2 (WX a X) Ho).
+ eapply astk_defined. exact ASTK9. clear - SPC; lia. clear; lia.
+ eapply dk_trans. exact B8. apply dk_grows. exact MGM9.
- eapply L5LZ.model_rt_trans. exact B3. exact RT9.
- exact AM9.
- exact HH9.
Qed.
End CTX.
End WithIface.
End SCFG_1.
End PMBUK.
