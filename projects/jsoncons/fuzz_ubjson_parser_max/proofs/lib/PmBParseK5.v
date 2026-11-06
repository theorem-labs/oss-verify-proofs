(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBParseD PmBParseK PmBParseK4 PmBParseX PmBParseP2 PmBParseP4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "1bool"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"]; ["0LBX"; "0LK"; "0LK1"; "0LK2"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0R"; "0R1"; "0R2"; "6credit"; "7fframe"; "8SCFG"; "9aframe"]; ["9alinv"; "9apctx"; "9lmem"; "9lregs"; ":ADDR_B"; ";inv"; ";p_more"; ";pst"; ";strm"; ";vstr"; "<cfg"; "<ec_at"; "<o_ec"; "<o_p"; "=FPState"; ">TSet"]; ["?srealizes"; "@loaded_segments"; "0SCFG_P"; "Ale"; "0ar"; "0c"; "0cat"; "0cr"; "0cr1"; "0e"; "0e1"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0model"]; ["0model1"; "0model1'"; "0model2"; "0r"; "0s"; "0s1"; "0sm"; "0sm1"; "0sp"; "Bbv"; "0str"; "0v"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK5.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Ltac lf_open LF := unfold PMBLPK.lfacts in LF;
destruct LF as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & LSv & ? & ? & ? & ? & ? & ?);
destruct LSv as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
Ltac lr_open LR := unfold PMBLPD.lregs in LR; destruct LR as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma head_m0 : ltac2:(TCodec.tc2 tcn__PmBParseK5 "T4&Q?&Ey5'R9yR0%211%5241'4y8%611%311p061'D'3'5':%2211%411&M%611&L'Q7'Q9'Q8'2'Q>&Q1vQBv?vQDv=rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrB%FEEDCBA@?>=<;:987654321&OrAr@r?r>%5BJIHGFEDCBA@?;74321&Q3rQ3r=&Q=&Q4%221D&Q<%123F%8676I31A&Q2rQ4r<r;r:r9r8r7r6%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&Q;&QA%?2AQ6r5%453I261'7&Q6%11>z%43R421'Q@&N%11QK&Q:+edcH%26>Q:Q71Q6Q5rQ8%74@521p091p0?1p0E1p0Q01p0Q:1p0QA1pS<RC1pTHRD1pSBR@1pSFR=1pT@R?1pT<RB1p4RG1pQ6RF1pT2RN1pQ@S01pQFS61pSLRD1pT6S21pQBS41pQ8RM1pSJS21pHS31pSDRK1pT>RM1pTFRO1pT:S11pS>S81pSHS91pT8S:1pTBS;1pS@S71p2S;1pQ4S:1pJS;1pQ2S>1pT0SD1pQ>SF1pQDSL1pNT31").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c.
intros CTX G LR LM EC1 MO1.
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof (PMBLPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 CTX G LM) as (HM8 & _).
rewrite MO1 in HM8.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
lf_open LF. lr_open LR.
cfeed P (PMBLPP2.blpHm_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP2.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad278 0xad9a4 M2v K G LM MS2 FRZ2).
intros model1' LM'.
apply (PMBLPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v c CTX G); [| exact LM'| exact EC1].
apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP2.KS_blpHm LR0 KS2). PMBLPK4.ksinc.
Qed.
Lemma join_ok : ltac2:(TCodec.tc2 tcn__PmBParseK5 "U1&Q?&Ey5'R9yR0%211%5241'4y8%611%311p061'D'3'5':%2211%411&M%611&L'Q7'Q9'Q8'2'Q>&Q1vQBv?vQDv=rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Or?r>r=r<%5BJIHGFEDCBA@?;74321&Q3rQ1r;&Q=&Q4%221D&Q<%123F%8676I31A&Q2rQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321'9'8'6&QC+1r2%3221+R0%5231%7231&Q;&QA%I2KQBr1%453Q5291%=261qS<R;1%@2R<1qTHR=1%B2R>1%Q12Q3QHz%<5;Q;21QI&Q5%11N&Q0rQ6rQ5rQ4rQ3%5LR<R;R:4321Q7Q@R9R8R7R5R4R3R2R1R0QOIQFAQDQCQ?Q6Q5Q4'Q@&N%11R@&Q:r3+edcH%36JQ721R0Q0rQ8%84L621p0:1pT4S71pQHS>1pSNRL1%Q:2D1%Q;2G1%Q>2K1+efT@%>6Q5R8R71R6R5%B4Q6@1Fp041p0QD1p0QO1p0R91p0R@1pSBS=1pSFS:1pT@S<1pT<S?1p4SD1pQ6SC1pT2SK1pQ@SM1pQFT31pSLSA1pT6SO1pQBT11pQ8SJ1pSJSO1pHT01pSDSH1pT>SJ1pTFSL1pT:SN1pS>T51pSHT61pT8T71pTBT81pS@T41p2T81pQ4T71pJT81pQ2T;1pT0TA1pQ>TC1pQDTI1pNU01").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 288 + 32) :: FF) fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
destruct JX as [(v & c & Hv & EC1)|(EC1 & INV1 & IHX)].
- pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb v c HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
assert (Hv' : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
lf_open LF. lr_open LR.
cfeed P (PMBLPP4.blpJe_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 56%nat => v | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad890 0xad9a4 M2v K G LM MS2 FRZ2).
intros model1' LM'.
apply (PMBLPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v c CTX G); [| exact LM'| exact EC1].
apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpJe LR0 KS2). PMBLPK4.ksinc.
- pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb 0 cat HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
pose proof (PMBLPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 CTX G LM) as (_ & HD9 & _).
pose proof INV1 as (_ & ID1 & _). rewrite ID1 in HD9.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
lf_open LF. lr_open LR.
cfeed P (PMBLPP4.blpJ0_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad890 0xad278 M2v K G LM MS2 FRZ2).
intros model1' LM'.
apply (IHX fx2 R2 model1'). split; [| split; [exact INV1| split; [exact EC1| exact LM']]].
apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpJ0 LR0 KS2). PMBLPK4.ksinc.
Qed.
End WithHeap.
End PMBLPK5.
