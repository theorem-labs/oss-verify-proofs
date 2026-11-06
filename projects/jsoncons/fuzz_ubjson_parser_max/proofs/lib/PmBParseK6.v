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
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBParseD PmBParseK PmBParseK4 PmBParseK5 PmBParseX PmBParseP3 PmBParseP4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseK6.PMBLPK6.WithHeap."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "1bool"; "1list"; "1option"; "1prod"; "2Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"]; ["3Model"; "4bvmap"; "0M"; "0M1"; "0M2"; "0R"; "0R1"; "5credit"; "6fframe"; "7SCFG"; "8aframe"; "8apctx"; "8lmem"; "8lregs"; "9epost"; "9jpost"]; [":ADDR_B"; ";pst"; ";strm"; ";vstr"; "<cfg"; "<o_ec"; "<o_p"; "=FPState"; ">TSet"; "?srealizes"; "@loaded_segments"; "0SCFG_P"; "0ar"; "0cat"; "0cr"; "0cr1"]; ["0e"; "0e1"; "0fb"; "0fl"; "0fx1"; "0model"; "0model1"; "0model2"; "0r"; "0s"; "0s1"; "0sm"; "0sm1"; "0sp"; "Abv"; "0str"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK6.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Definition jpost (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) (F : Z)
(M1 : word -> option byte) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
(exists v c, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c)
\/ (PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) 0 cat /\ PM.inv s1 /\
(forall (fx2 : FPState) R2 model1', PMBLPD.alinv L ar HI R M model LBX FF LK Aw cr sp fb cat s str sm e F R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xad278 M1 model1') K)).
Definition epost (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
(cr : credit) (sp fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) (F : Z)
(M1 : word -> option byte) (LK1 : list fframe) (Aw1 : list (Z * Z)) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
(exists v c, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c /\ PM.p_more s1 = 0)
\/ (PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) 0 cat /\ PM.inv s1 /\
(forall (fx2 : FPState) R2 model1', PMBLPD.alinv L ar HI R M model LBX FF LK Aw cr sp fb cat s str sm e F R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xad278 M1 model1') K)).
Lemma after_CR0 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+edh4%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP3.blpCR0_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP3.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad304 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP3.KS_blpCR0 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CR2 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+eeR@%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP3.blpCR2_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP3.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad450 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP3.KS_blpCR2 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CR6 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+eee@%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP3.blpCR6_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP3.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad6b0 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP3.KS_blpCR6 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CR10 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+eeg8%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpCR10_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad6e8 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpCR10 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CR3 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+efT4%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpCR3_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad884 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpCR3 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CV4 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+edl8%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpCV4_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad388 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpCV4 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CV8 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+eeiH%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpCV8_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad738 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpCV8 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CE3 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+eeU<%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpCE3_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad4ac 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpCE3 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_CE9 : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&OrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+edo4%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpCE9_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad3e4 0xad890 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpCE9 LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPK5.join_ok L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 CTX G LR2 LM' JX).
Qed.
Lemma after_end_N : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&NrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+ee[D%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X & _)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 CTX G LM) as (_ & HD9 & _ & _ & [DN|DN]); rewrite DN in HD9.
- pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpN0_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad574 0xad278 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpN0 LR0 KS2); PMBLPK4.ksinc).
destruct JX as [(v2 & c2 & _ & EC2 & MO2)|(EC2 & INV2 & IHX)].
+ exact (PMBLPK5.head_m0 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v2 c2 CTX G LR2 LM' EC2 MO2).
+ apply (IHX fx2 R2 model1'). split; [exact LR2| split; [exact INV2| split; [exact EC2| exact LM']]].
- destruct JX as [(v2 & c2 & Hv2 & EC2 & MO2)|(EC2 & INV2 & IHX)]; [| exfalso; destruct INV2 as (_ & X & _); rewrite X in DN; discriminate].
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpNd_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad574 0xad9a4 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpNd LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v2 c2 CTX G LR2 LM' EC2).
Qed.
Lemma after_end_M : ltac2:(TCodec.tc2 tcn__PmBParseK6 "SL&Q8&Ay5'QNyR0%211%5241'4y8%611%311p061'@'3'5'6%2211%411&H%611&G'Q1'Q3'Q2'2'Q7&KvQ;v;vQ<v9rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@%FEEDCBA@?>=<;:987654321&Jr?r>r=r<%5BJIHGFEDCBA@?;74321&MrQ1r;&Q6&Q0%221D&Q5%123F%8676I31A&LrQ2r:r9r8r7r6r5r4%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321&NrQ4rQ3%3H21<EQ>Q=Q<Q;Q:Q9Q7Q6Q5Q4Q3Q2Q1H;:9876'Q9&Q:&I%11QF&Q4+eek0%265Q2Q11Q0OrQ5%847521p0:1p0?1p0J1p0Q41p0Q;1pS0R81pS4R51pSJR71pSFR:1p4R?1pNR>1pS>RF1pQ8RH1pQ>RN1pS:R<1pS@RJ1pQ:RL1pQ0RE1pS8RJ1p@RK1pS2RC1pSHRE1pT0RG1pSDRI1pRLS01pS6S11pSBS21pSLS31pRNRO1p2S31pLS21pBS31pJS61pS<S<1pQ6S>1pQ<SD1pFSK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros CTX G LR LM JX.
assert (ECX : exists v c, PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMB.AD fb) v c) by (destruct JX as [(v & c & _ & X & _)|(X & _)]; [exists v, c; exact X| exists 0, cat; exact X]).
destruct ECX as (v & c & EC1).
pose proof (PMBLPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 CTX G LM) as (_ & HD9 & _ & _ & [DN|DN]); rewrite DN in HD9.
- pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpM0_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad760 0xad278 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpM0 LR0 KS2); PMBLPK4.ksinc).
destruct JX as [(v2 & c2 & _ & EC2 & MO2)|(EC2 & INV2 & IHX)].
+ exact (PMBLPK5.head_m0 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v2 c2 CTX G LR2 LM' EC2 MO2).
+ apply (IHX fx2 R2 model1'). split; [exact LR2| split; [exact INV2| split; [exact EC2| exact LM']]].
- destruct JX as [(v2 & c2 & Hv2 & EC2 & MO2)|(EC2 & INV2 & IHX)]; [| exfalso; destruct INV2 as (_ & X & _); rewrite X in DN; discriminate].
pose proof (PMBLPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof LR as LR0.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMBLPK5.lf_open LF. PMBLPK5.lr_open LR.
cfeed P (PMBLPP4.blpMd_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP4.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMBLPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xad760 0xad9a4 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMBLPD.lregs R R2 sp op oec F) by (apply (PMBLPK4.lregs_ks R R1 R2 sp op oec F PMBLPP4.KS_blpMd LR0 KS2); PMBLPK4.ksinc).
exact (PMBLPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v2 c2 CTX G LR2 LM' EC2).
Qed.
End WithHeap.
End PMBLPK6.
