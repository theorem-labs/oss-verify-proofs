(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmAUarK.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAUarKS () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAUarK.PMAUK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAUarKS.PMAUKS.SCFG_1.WithIface.CTX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreSpecsA.L5CSA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0Ac"; "0BX"; "0BX0"; "1app"; "1cons"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0F"]; ["0FF"; "0G"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "0LK2"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M9v"; "0Mc"]; ["0Mf"; "0R9"; "0Rc"; "6mrestrict"; "7msteps"; "8credit"; "9SB"; "9aclient"; "9aclientw"; "9ahid"; "9ff_bytes"; "9fframe"; "9model_rt"; "9ri_inv"; "9vml_of"; ";outside"]; [";range"; ";u8_at"; ":SCFG"; "<binv"; "<gctx"; "=WretY"; ">FPState"; ">mkst"; ">seg_rom"; "?TSet"; "@srealizes"; "Amem_grows"; "Bahpres"; "Bamodel_ok"; "Ccfg"; "Dloaded_segments"]; ["0SCFG_P"; "0SCR"; "Eadd"; "Ediv"; "Ele"; "Elt"; "Epow"; "Esub"; "0W"; "0Wp"; "0Wx"; "0Wy"; "0a"; "0ar"; "0cr2"; "0crc"]; ["0fl"; "0fx"; "0fx9"; "0k"; "0model"; "0model1"; "0model2"; "0modelc"; "0modelf"; "0ocell"; "0ohi"; "0olo"; "0own"; "0pc"; "0r"; "0sp"]; ["0spc"; "FZ_to_bv"; "Fbv"]]).
Local Ltac lia := L5FastLia.plia.
Module PMAUKS.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import L5CBR. Import L5ADHR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Section CTX.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
(sp SCR : Z) (spc olo ohi : Z) (ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
(F fl : Z) (k : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit) (BX0 : list (Z * Z)).
Local Notation B := (ff_bytes k).
Local Notation FF' := ((F, k, spc + 32) :: FF).
Local Notation gctx := (PMAUK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0).
Local Notation binv := (PMAUK.binv L ar HI M model LB FF LK A sp SCR spc own F k).
Local Notation Wret := (PMAUK.Wret F fl k).
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAUarKS "U>'QDvDvR=vBvEv@vFv0vROvR1vS0vRKvRJvRIvRLv?vR@vRCvGvMvRFvR>v3%GFFEDCBA@?>=<;:987654321'6&Q@%211'9'>%2211%611'S2yR0%211'7y8%511%311p051'I&Q;%A11&Q5!p0@1&QCvKvRDr;r:r9r8r7r6r5%:FQFQEQD98QCQBQAQ@Q?Q>Q=Q9Q8Q67654321&Q=&4%13M:QF(5%Q12OQ0(8%14Q2Q2Q?Q=&R2+Q0%22QG1%54Q5Q641%8371QN&Q>r4%211%?8R4=4DCBA1&QM%12EC&Q<%12KF&QKr=%221K':&R4zr1%3221&R5&R6+2+R0%3221%5271%;271&<r2%Q;11%311';r<&S1r3%22R31%411rA%113%83R231p0:1p0?1pTJR>1%QH1I&Q7%17S<S;S9S8S5S4A%C11%S21C%E11%Q2231p071pTJRG1%R31Q2'=%R51J%Q72S=K%Q42LS@%Q:221%Q:2S;N&Q:%11S;%QN2S>1%Q:2Q21%Q@251&R3+8%22SC1&Q6%R5221%QE21Q9%62:5%R8231%QD2Q<1%QJ241&Q?rD%221Q@%QB11%I251%J2@1%K2G1%R22Q11%M2L1p0O1pTJSH1rCrBr?r>%S<FTHTGTFS;S:TETDTCTBTAT@T?T;T:T843QIS921R<p061p0Q81p0QB1p0R?1p0RC1p0RF1p0RI1p0S:1pTHSF1pTDSG1pU<SM1pQJSO1p4T81pU0SM1pQBSO1pU@T21pR0T41p6T=1pTBTB1pQ4TF1")) (only parsing).
Variables (G : gctx).
Variable W : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable BX : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable Mc : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable modelc : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable LKc : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable crc : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable Ac : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable model1 : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variables (Wp Wy : Z -> Prop).
Lemma binv_pieceS : ltac:(sec_stmt2 constr:(SECT) 12%nat 0%nat).
Proof.
destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) HH1 AM1 RT1 MG FRM NCY WP.
unfold PMAUK.binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
split. eapply astk_grows. exact B6. exact MG.
split. { eapply ek_trans. exact B7. intros a (Ha & Hc & Ho). apply FRM. exact Ha. intros X. destruct (WP a X) as [Y|(_ & [Y|[Y|[Y|Y]]])].
- exact (proj1 (NCY a Y) Hc).
- apply (NCS a). exact Y. exact Hc.
- apply (NCF a). left; exact Y. exact Hc.
- apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - Y. unfold SB in Y |- *. lia. exact Hc.
- exact (Y Ho). }
split. { eapply dk_trans. exact B8. apply dk_grows. exact MG. }
split. { apply (OWNAG Mc M1 B9). intros a Ha. apply FRM. pose proof (OCR a Ha). clear - H SPC SLO. lia.
intros X. destruct (WP a X) as [Y|Y]; [exact (proj2 (NCY a Y) Ha)| exact (proj1 Y Ha)]. }
eapply L5.defined_grows. exact MG. exact B10.
Qed.
End S.
Definition WretY (Wx Wy : Z -> Prop) (a : Z) : Prop := Wret a \/ Wx a \/ Wy a.
Lemma retire_coreS : ltac2:(TCodec.tc2 tcn__PmAUarKS "W?'QDvDvR=vBvEv@vFv0vROvR1vS0vRKvRJvRIvRLv?vR@vRCvGvMvRFvR>v3%GFFEDCBA@?>=<;:987654321'6&Q@%211'9'>%2211%611'S2yR0%211'7y8%511%311p051'I&Q;%A11&Q5!p0@1'QF&Jy5%221?&QI&QCvKvRDrAr@r?r>r=r<r;%:FQKQJQI98QHQGQFQEQDQCQBQ>Q=Q;7654321r1%411':&Q8&4rC%23Q61QO(5%Q:2Q8Q9(8%14Q;Q;QHQF&R2+Q0%22R01%54Q>Q?41%8371R7zr2%?7R>R=<3221&<&Q?rD%2215%411%F261p0H1pTJQK1'=%Q01L%:11%3221pTJR01&R4&R7%12RGRF%321B&R5%12DRJ%Q4231&Q7%17S4S3S1S0RMRLG%F11%Q8241p0?1pTJR=1%QB1Q=%K11%D221pTJRA1'Q4&QO&QG&S1r:%22RC1&Q3&Q9%12R0QD%321Q5&QH%11:%:5R1QO731r9r8%<2RM1r7%?5R54216%B3A61&QK%=2R=Q@rE%@221%4219%Q92QIR9&R6+2+R0%3221%Q:2R>1%R=261&QErB%23R=1R1%R011';r3%Q22SC1%RJ11rH%Q12C1rI%Q43215%83SD51p0:1p0?1pTJT01&QA%14Q?Q<T>RArGrF%D321RC%RB11r5%11ArM%11C%F3T231p061p0M1pTJT>1rK%Q;21J%QH2H2r4%QK221%O3T:1SI&QLrO%29UBUAU?U>U;U:1T0@&Q<%12T1B&QMr6%22=1&Q=rQ1%SJ3TN1UGrNrL&Q>%11R1%78UM5UK4K3R41'QJ&QBvR0%211&QN%15Q?Q6R3R;R:%64RH31T5p081p0A1p0E1p0H1p0L1p0Q11p0Q41pUBU81pR2U:1%<5R3TKTJQJQL%A4S3>1TGp031p0QF1p0QI1p0RA1p0RG1p0S;1p0S@1p0SN1p0T41p0U01pQ8U<1pQNUH1pUNV31pR4U@1pULV51pR6UB1pU6UF1pU4UG1pTHUI1pTFUJ1p4V91pU0UN1pQBV01pU@V31pR0V51p6V>1pTBVC1pQ4VG1").
Proof. intros G W BX Mc modelc LKc crc Ac Wx Wy fx fx9 Rc pc R9 r M9v K.
intros BI WX WXD WY WYD wMS MG9 wFZ wFL0 KF.
destruct (PMAUK.vis_facts L ar C HI LY HIok M model LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 G W BX Mc modelc LKc crc Ac BI)
as (_ & _ & _ & (FLC8 & FLV8 & _)).
pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
assert (FLNC8 : ~ aclient L ar (BX ++ LB) FF' 0 0 fl).
{ apply (not_client_bx L ar FF' fl BX LB). apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ BX LB B1 eq_refl). exact FLP. exact FLBIG. exact FLNC. }
apply (apiece_retire L ar C HI LY HIok (BX ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 r M9v (WretY Wx Wy) F k (spc + 32) fl K B1 B2).
{ exact FLC8. }
{ exact FLNC8. }
{ exact FLV8. }
{ clear - FLR; lia. }
{ exact wMS. }
{ exact MG9. }
{ exact wFZ. }
{ intros a Ha Wa. unfold WretY, PMAUK.Wret in Wa. destruct Wa as [[[Wa|Wa]|Wa]|[Wa|Wa]].
- right. apply (fframe_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity. clear - Wa FR; lia.
- right. apply (fframe_shadow_client L ar (BX ++ LB) _ 0 0 F k (spc + 32)). left; reflexivity.
unfold in_shadow_of, S. rewrite (proj1 (proj2 F8)). clear - Wa. unfold SB in *. lia.
- left; exact Wa.
- right. exact (proj1 (WX a Wa)).
- right. destruct (WY a Wa) as (Y1 & _). unfold aclientw, aclient_g. right; left. split; [clear - Y1 SLO SPC; lia| intros Z; clear - Z; lia]. }
{ intros a. unfold WretY, PMAUK.Wret. destruct (WXD a) as [X|X]; [left; right; left; exact X|]. destruct (WYD a) as [Y|Y]; [left; right; right; exact Y|].
destruct (rng_dec a F (F + 8)); [left; left; left; left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + ff_bytes k / 8)); [left; left; left; right; tauto|].
destruct (Z.eq_dec a fl); [left; left; right; exact e|]. right. intros [[[Z|Z]|Z]|[Z|Z]]; tauto. }
{ exact wFL0. }
intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
assert (ASTK9 : astk ar M9 sp SCR). { eapply astk_grows. exact B6. exact MGM9. }
apply (KF M9 model9).
- exact FRM9.
- exact MGM9.
- exact VIS9.
- apply ahpres_of.
+ eapply ek_trans. exact B7.
intros a (Ha & Hc & Ho). apply FRM9. exact Ha. unfold WretY, PMAUK.Wret. intros [[[X|X]|X]|[X|X]].
* apply (NCF a). left; clear - X FR; lia. exact Hc.
* apply (NCF a). right. unfold S. rewrite (proj1 (proj2 F8)). clear - X. unfold SB in X |- *. lia. exact Hc.
* subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
* exact (proj2 (WX a X) Ho).
* exact (proj2 (WY a X) Hc).
+ eapply astk_defined. exact ASTK9. clear - SPC; lia. clear; lia.
+ eapply dk_trans. exact B8. apply dk_grows. exact MGM9.
- eapply L5LZ.model_rt_trans. exact B3. exact RT9.
- exact AM9.
- exact HH9.
Qed.
End CTX.
End WithIface.
End SCFG_1.
End PMAUKS.
