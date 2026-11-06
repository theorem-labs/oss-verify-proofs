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
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBReset1 PmBParseD PmBParseK PmBParseK2 PmBParseK3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"]; ["3Z"; "0E"; "0F"; "0FF"; "0HI"; "0K"; "0KS"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "4Model"; "5bvmap"; "0M"; "0M1"]; ["0M1'"; "0M1v'"; "0M2"; "0R"; "0R1"; "0R1'"; "0R2"; "6mrestrict"; "7msteps"; "8credit"; "8regs_preserved"; "9ahid"; "9fframe"; "9model_rt"; "9ri_inv"; "9vml_of"]; [";u64_at"; ";u8_at"; ":SCFG"; "<aframe"; "<apctx"; "<lmem"; "<lregs"; "=ADDR_B"; ">PST"; ">p_done"; ">p_more"; ">parser_own"; ">pst"; ">pstate"; ">pstate_at"; ">srcst"]; [">strm"; ">vstr"; "?cfg"; "?ec_at"; "?o_ec"; "?o_p"; "@FPState"; "@getr"; "@mkst"; "@seg_rom"; "ATSet"; "Bsrealizes"; "Cmem_grows"; "Damodel_ok"; "Ecs_all"; "Floaded_segments"]; ["0SCFG_P"; "GIn"; "Hadd"; "Hle"; "Hlt"; "Hmul"; "Hof_nat"; "Hpow"; "Hsub"; "0a"; "0ar"; "0c"; "0cat"; "0cr"; "0cr1"; "0dn1"]; ["0dp1"; "0e"; "0e1"; "0fb"; "0fl"; "0fx"; "0fx'"; "0mo1"; "0model"; "0model1"; "0model1'"; "0model2"; "0n"; "0oec"; "0off"; "0op"]; ["0pc"; "0pc'"; "0pre"; "0r"; "0s"; "0s1"; "0sm"; "0sm1"; "0sp"; "0src1"; "IZ_to_bv"; "Ibv"; "0str"; "0tb1"; "0tg1"; "0top"]; ["0top'"; "0v"; "0vb1"; "0vk1"; "0x"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK4.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK4 "QE&My5'SKyR0%211%5241'@'6'7%211&QFr8r7r5r4r3r2%76654321&RAr1%23<15'=&R7r9&SJ&RF%11:%32J1%6251r:%8213%:3K31p0<1pX:I1&R>%A3K@1%B3LDGp021pX:N1r;r6%O62BNM1Lp041p0:1p0K1pQ>Q41pQ6Q81pVLQ91pW0Q:1pQ4Q;1pR>Q=1pR:Q>1pR8Q?1")) (only parsing).
Variable R : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable R1 : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable R2 : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable op : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable oec : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variables (KS : list nat).
Lemma lregs_ks : ltac:(sec_stmt2 constr:(SECT) 8%nat 0%nat).
Proof.
intros (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & X3 & X4) KS1 IN.
assert (G : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply KS1, IN, Hx).
unfold PMBLPD.lregs.
rewrite (G 2%nat) by inl. rewrite (G 8%nat) by inl. rewrite (G 9%nat) by inl. rewrite (G 18%nat) by inl. rewrite (G 19%nat) by inl.
rewrite (G 20%nat) by inl. rewrite (G 21%nat) by inl. rewrite (G 22%nat) by inl. rewrite (G 23%nat) by inl. rewrite (G 24%nat) by inl.
rewrite (G 25%nat) by inl. rewrite (G 26%nat) by inl. rewrite (G 27%nat) by inl. rewrite (G 3%nat) by inl. rewrite (G 4%nat) by inl.
repeat split; assumption.
Qed.
End S.
Ltac ksinc := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold L5SAR.cs_all in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Lemma lregs_pres : ltac2:(TCodec.tc2 tcn__PmBParseK4 "M&My5'SKyR0%211%5241'@&QFr7r6r4r3r2r1%76654321&Q:%1287r9r5%<62;:198p041p071pQ6@1pVLA1pW0B1pQ4C1pR>E1pR:F1pR8G1").
Proof. intros R R1 R2 E op oec F.
intros LR RP. apply (lregs_ks R R1 R2 E op oec F L5SAR.cs_all LR); [| intros x Hx; exact Hx].
intros x Hx. exact (L5SAR.cs_of_preserved R1 R2 x RP Hx).
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma step_ro : ltac2:(TCodec.tc2 tcn__PmBParseK4 "SI&My5'SKyR0%211%5241'9y8%611%311p061'L'6';'@%2211%411&Q<%611&Q9'QL'R1'R0'3&QCvGvRJvDrLrKrJrIrHrGrFrErDrBr>r=r<r;r:%CBBA@?>=<;:987654321&QErMrCrAr@r?r9r8r7r6r5r4r3%=JQ0ON<MLKJIHGFE;D:98?7654321&Q>&2&QK%119%33Q?1Q1(4%QC2QAQB(:+1%24QEQEC1&RB&RH+Y0%22Q51+Q0%5221%94QKQL71%<3;1Q=&Q?%11E%D8QC@3LGKQ51&R=%12NI&Q=%12Q:LrQ1rQ0rOrN%Q;JQNQMQL4321Q:QKQJQIQHQGQFQEQDQCQ9QAQ2Q?Q>Q=Q5Q4Q3p061p091p0<1p0Q21p0QA1pVFRB1pUNR;1pV6R81pW@R:1pW<R=1p4RB1pQFRA1pVDRI1pR0RK1pVHRK1pR6RM1pQHRF1pV:RK1pQ6RL1pV4RD1pW>RF1pWJRH1pW:RJ1pV8S11pWBS21pULRN1p2S21pQDS11pQ8S21pQBS51pVBS;1pQNS=1pR8SC1").
Proof. intros R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 model1'.
intros G (BI & RP & LS & ST & EE & CK) HH1 AM1 RT1. split; [|exact (conj RP (conj LS (conj ST (conj EE CK))))].
apply (PMBLPK.binv_pieceB L ar C HI HIok R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 _ _ M1 model1 LK1 cr1 Aw1 M1 model1' (fun _ => False) G BI HH1 AM1 RT1 (mem_grows_refl M1));
[intros a _ _; reflexivity| intros a []].
Qed.
Lemma ro_run : ltac2:(TCodec.tc2 tcn__PmBParseK4 "TN&My5'SKyR0%211%5241'9y8%611%311p061'L'6';'@%2211%411&Q<%611&Q9'QL'R1'R0'3'R6&R:&QCvGvRJvDrQ3rQ2rQ1rQ0rOrNrMrLrKrIrErDrCrBrA%CBBA@?>=<;:987654321&QErQ4rJrHrGrFr@r?r>r=r<r;r:%=JQ0ON<MLKJIHGFE;D:98?7654321'Q8&R?&R8r8&SJr6%22QO1&Q7&Q;%12@I%321K&R9%11;%;5?:731r9r7r5%=2R:1r4%A554217%D3C71'<&RCzr1%3221&RD&RG+2+R0%3221%5271%;271'=r2%O2RL1%E11%M2QFQH%O31QJ3%63RJ31p081pUDRG1rQ8rQ7rQ6rQ5%QLJR?R>R=4321QKR<R;R:R9R8R7R6R5R4QJR2FR0QOQNQFQEQD'R;&QBvR@%211&R2%16QCQIQGQ6QMB%64QD31Q6p081pVFS81%56QGQMQKQ:R<R;%:4QH71QDp031p0B1p0Q81p0QN1p0R=1pQ<S21pR4SB1pW4S?1pW2S@1pR<SJ1pR:SK1pV>S91pV<S:1pUNS@1pV6S=1pW@S?1pW<SB1p4SG1pQFSF1pVDSN1pR0T01pVHT01pR6T21pQHSK1pV:T01pQ6T11pV4SI1pW>SK1pWJSM1pW:SO1pV8T61pWBT71pULT31p2T71pQDT61pQ8T71pQBT:1pVBT@1pQNTB1pR8TH1").
Proof. intros R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx fx' R1 R1' pc pc' M1v' K.
intros G LM MS FZ KX.
pose proof LM as (BI & _). pose proof BI as (HH1 & AM1 & _).
assert (EV : M1v' = mrestrict (ahid Aw1 model1) M1) by (apply L5SAR.mem_eq_of_agree; exact FZ). subst M1v'.
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 fx fx' R1 pc R1' pc' _ K HH1 AM1 MS (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M1' model1' HH1' AM1' MRT1' HID1' VIS1' MGM1' FR1'.
assert (E1 : M1' = M1) by (apply L5SAR.mem_eq_of_agree; exact FR1'). subst M1'.
exact (KX model1' (step_ro R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 model1' G LM HH1' AM1' MRT1')).
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK4 "XE&R:&My5'SKyR0%211%5241'9y8%611%311p061'L'6';'@%2211%411&Q<%611&Q9'QL'R1'R0'3'QO'QM%>11'R6&QDvR@vGvRJvDrQCrQBrQArQ@rQ?rQ>rQ=rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3%FEEDCBA@?>=<;:987654321&QCrQ2rQ1rQ0rO%5BJIHGFEDCBA@?;74321&QErQDrNrMrL(QHrKrJrIrHrGrFrErD&2rC(4rB(8%11QC%43QD31%73QE61%A9@?>=<;:91r@r?r>%JJQEQDQCIQBQAQ@Q?Q>Q=Q<Q;Q9Q7Q6Q5Q4Q3LHGF4321'Q8&R?&R8r<r:&SJr8%22RH1&Q7&Q;%12Q2Q7%321Q9&R9%11<%<5;:731r;r9r7%=2S31r6%B554217%E3D71&R<%>2Q@QE%@21QG%3218'<&RCzr1%3221&RD&RG+2+R0%3221%5271%;271&>&RB&RE+Q0&RF&5%12S7QN%311%6251%82R31%921QJr2%G221rA%=241%F241%L241%A11'=r3%QE2T;1%Q<11%QC2RLS0%QE31S23%63T931p081p0K1pUDT71%Q72Q6?%Q42Q7@%M2R@R>%Q:21L&QN%L2T2RK%N11%Q12Q01%Q32S11%54R:R81RM&R3&R4&QG%221T1%45R?SG1R=R1rQOrQNrQMrQLrQKrQJrQIrQHrQGrQE%S63TFSBS3%S93TGSE1%SC9T3T2T1T0SMSLSKSJ1%SIJTDTCTB=<;:987654TAT@T?T>T=Q=R1T6T51SCSBSA%QD2TJSN%QF11%QI2QH1%QK2T51%QL21SH%R921QC%QN22SI%R72QE1%R=231%R211%RF1Q?%TH1Q@%QC3UF21p041p0R81pUDUD1r4%Q32Q2G%Q55S@21QNSE'R;&QB%11U;&R2r5%26SFT9T7T518rR3%74SH521p091p0=1p0N1pVFV61pR2V81%:6SNT>T;R<U8U7%>4SO<1Q?p031p0QB1p0QH1p0QO1p0R21p0R41p0R61p0S?1p0SD1p0T;1p0U71p0U>1pUHVC1pX4VD1pR4VI1pW4VF1pW2VG1pR<W11pR:W21pV>V=1pV<V>1pVJVL1pVNVM1pUNVI1pV6VF1pW@VH1pX2VF1pX0VG1pW6VG1pX8W41pX6W51pWNW61pWLW01pWDVN1pV2W91pV0W:1pV@W;1p4W:1pQFW91pVDWA1pR0WC1pVHWC1pR6WE1pQHW>1pV:WC1pQ6WD1pV4W<1pW>W>1pWJW@1pW:WB1pUJWI1pV8WJ1pW8WK1pWBWL1pULWH1p2WL1pQDWK1pQ8WL1pQBWO1pVBX51pQNX71pR8X=1pQ<XD1")) (only parsing).
Variable K : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable LBX : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SECT) 10%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SECT) 11%nat 0%nat).
Variable cat : ltac:(sec_ty2 constr:(SECT) 12%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 13%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 14%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 15%nat 0%nat).
Variable e : ltac:(sec_ty2 constr:(SECT) 16%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SECT) 17%nat 0%nat).
Variable fl : ltac:(sec_ty2 constr:(SECT) 18%nat 0%nat).
Variable LK2 : ltac:(sec_ty2 constr:(SECT) 19%nat 0%nat).
Variable M2 : ltac:(sec_ty2 constr:(SECT) 20%nat 0%nat).
Variable model2 : ltac:(sec_ty2 constr:(SECT) 21%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SECT) 22%nat 0%nat).
Variable model1 : ltac:(sec_ty2 constr:(SECT) 23%nat 0%nat).
Variable LK1 : ltac:(sec_ty2 constr:(SECT) 24%nat 0%nat).
Variable Aw1 : ltac:(sec_ty2 constr:(SECT) 25%nat 0%nat).
Variable mo1 : ltac:(sec_ty2 constr:(SECT) 26%nat 0%nat).
Variable dn1 : ltac:(sec_ty2 constr:(SECT) 27%nat 0%nat).
Variable dp1 : ltac:(sec_ty2 constr:(SECT) 28%nat 0%nat).
Variable src1 : ltac:(sec_ty2 constr:(SECT) 29%nat 0%nat).
Variable tb1 : ltac:(sec_ty2 constr:(SECT) 30%nat 0%nat).
Variable tg1 : ltac:(sec_ty2 constr:(SECT) 31%nat 0%nat).
Variable vb1 : ltac:(sec_ty2 constr:(SECT) 32%nat 0%nat).
Variable vk1 : ltac:(sec_ty2 constr:(SECT) 33%nat 0%nat).
Variable pre : ltac:(sec_ty2 constr:(SECT) 34%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SECT) 35%nat 0%nat).
Variable top' : ltac:(sec_ty2 constr:(SECT) 36%nat 0%nat).
Variable sm1 : ltac:(sec_ty2 constr:(SECT) 37%nat 0%nat).
Variable e1 : ltac:(sec_ty2 constr:(SECT) 38%nat 0%nat).
Variable cr1 : ltac:(sec_ty2 constr:(SECT) 39%nat 0%nat).
Variables (off n : Z).
Variables (fx fx' : FPState).
Variable R1 : ltac:(sec_ty2 constr:(SECT) 44%nat 0%nat).
Variable R1' : ltac:(sec_ty2 constr:(SECT) 45%nat 0%nat).
Variables (pc pc' : Z).
Variable M1v' : ltac:(sec_ty2 constr:(SECT) 48%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 49%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 50%nat 0%nat).
Lemma top_run : ltac:(sec_stmt2 constr:(SECT) 51%nat 0%nat).
Proof.
intros CTX G LM MS MG FZ Hoff Hn Hon PTv EC1 KX.
pose proof LM as (BI & RP1 & _). pose proof BI as (HH1 & AM1 & _).
set (s1 := PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [top])) in *.
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
destruct RP1 as (PA1 & _).
pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _). cbn [s1 PM.p_b PM.p_k PM.p_stk] in PVEC.
pose proof PVEC as (_ & _ & _ & Hk & Hlen & Hal & _).
rewrite length_app in Hlen. cbn [length] in Hlen. rewrite Nat2Z.inj_add in Hlen. cbn [Z.of_nat Pos.of_succ_nat] in Hlen.
assert (VIN : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1; apply in_or_app; left; unfold s1, PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _).
destruct (WB1 _ VIN) as ((B0 & BI0 & B16 & _ & B4 & BAPP) & _). cbn [fst snd] in B0, BI0, B16, B4, BAPP.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI0.
pose proof (PM.pow2_pos vk1 ltac:(lia)) as P2K.
assert (TB : vb1 <= T /\ T + 32 <= vb1 + 32 * 2 ^ vk1) by (unfold T; clear - Hlen; lia).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP. cbv zeta in VP. destruct VP as (_ & _ & _ & _ & VB & _).
assert (TV : L5A.avis (ahid Aw1 model1) T 32) by (apply (VB vb1 (32 * 2 ^ vk1) T 32 VIN); clear - TB; lia).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB1 _ LK1 cr1 Aw1 M1 model1 fx fx' R1 pc R1' pc' M1v' (fun a => T + off <= a < T + off + n) K HH1 AM1 MS MG).
{ intros a Ha Nw. exact (FZ a Ha Nw). }
{ intros a Ha Wa. split.
- unfold aclientw, aclient_g. left. exists (vb1, 32 * 2 ^ vk1). split; [exact VIN| cbn [fst snd]; clear - Wa TB Hoff Hon; lia].
- clear - Wa TB BI0 Hoff Hon. lia. }
intros M1' model1' HH1' AM1' MRT1' HID1' VIS1' MGM1' FR1' VV1'.
assert (T0 : 0 <= T /\ T + 32 <= 2 ^ 64) by (unfold app_mem in BAPP; destruct BAPP as (_ & _ & BA3); clear - TB B0 BA3; lia).
assert (PT' : PM.pstate_at RSEGS M1' T top').
{ rewrite <- VIS1' in PTv. destruct PTv as (PT0 & PT8 & PT16 & PT24). split; [|split; [|split]].
- apply (proj1 (L5A.u32_at_vis _ M1' T _ ltac:(eapply L5A.avis_sub; [exact TV| clear - T0; lia| clear - T0; lia]) ltac:(clear - T0; lia) ltac:(clear - T0; lia))). exact PT0.
- apply (proj1 (L5A.u64_at_vis _ M1' (T + 8) _ ltac:(eapply L5A.avis_sub; [exact TV| clear - T0; lia| clear - T0; lia]) ltac:(clear - T0; lia) ltac:(clear - T0; lia))). exact PT8.
- apply (proj1 (L5A.u8_at_vis _ M1' (T + 16) _ ltac:(eapply L5A.avis_sub; [exact TV| clear - T0; lia| clear - T0; lia]) ltac:(clear - T0; lia) ltac:(clear - T0; lia))). exact PT16.
- apply (proj1 (L5A.u64_at_vis _ M1' (T + 24) _ ltac:(eapply L5A.avis_sub; [exact TV| clear - T0; lia| clear - T0; lia]) ltac:(clear - T0; lia) ltac:(clear - T0; lia))). exact PT24. }
apply (KX M1' model1'); [| exact FR1'|].
2: { pose proof CTX as (_ & _ & _ & _ & _ & _ & FOK & _). pose proof FOK as ((rs & Hfb) & Fal).
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
assert (EKp : L5SAR.ek L ar LB1 FF' 0 0 [(T + off, n)] M1 M1').
{ apply (L5SAR.ek_piece L ar LB1 FF' 0 0 [(T + off, n)] M1 M1' (fun a => T + off <= a < T + off + n) FR1').
intros a Ha _ O X. apply (O (T + off, n)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X]. }
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
assert (WSp : PMKB.wapp [(T + off, n)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct BAPP as (_ & [X|X] & _); [left| right]; clear - X TB Hon Hoff; lia| apply PMKB.wapp_nil]. }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct (WB1 _ VIN) as (_ & _ & _ & _ & _ & BFA & _). cbn [fst snd] in BFA.
pose proof (BFA (fb, 4, rs) (in_or_app FF' LK1 (fb, 4, rs) (or_introl (or_intror Hfb)))) as Z2. cbn [ff_addr ff_class fst snd] in Z2. change (ff_bytes 4) with 1024 in Z2.
assert (Eoec : PMSPA.o_ec PMB.AD fb = fb + 992) by reflexivity.
apply (PMKB.ec_keepA RSEGS L ar LB1 FF' 0 0 _ M1 M1' EKp WSp FRB1 _ v c); [| | exact EC1].
- exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. rewrite Eoec. clear; lia.
- intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite Eoec in Hi. clear - Hi Z2 TB Hoff Hon. lia. }
exact (PMBLPK3.step_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2
M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre top top' sm1 e1 cr1 M1' model1' off n CTX G LM HH1' AM1' MRT1' MGM1' FR1' Hoff Hn Hon PT').
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK4 "T9&R:&My5'SKyR0%211%5241'9y8%611%311p061'L'6';'@%2211%411&Q<%611&Q9'QL'R1'R0'3&QDvR@vGvRJvDrNrMrLrKrJrIrHrGrFrErDrCrBrAr@r?r>%FEEDCBA@?>=<;:987654321&QCr=r<r;r:%5BJIHGFEDCBA@?;74321&QErOr9r8r7r6r5r4r3%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321'<&QA&R?&Q7&Q;%12<A%321C&RB&R5&QG%221Q4+8%5221&QJ%11D%>4=931+9%:271&QI%11I%C4B>31&Q@+Z8%@2=1+`PPP0%44GC21'?'=z%23R>?1+1%43R@A1%6231%63RB>5%73RC?4%9221%Q4241%Q52<1%Q62B1%Q72H1p0Q91p0QD1p0QK1pUNRG1pV6RD1pW@RF1pW<RI1p4RN1pQFRM1pVDS51pR0S71pVHS71pR6S91pQHS21pV:S71pQ6S81pV4S01pW>S21pWJS41pW:S61pUJS=1pV8S>1pW8S?1pWBS@1pULS<1p2S@1pQDS?1pQ8S@1pQBSC1pVBSI1pQNSK1pR8T11pQ<T81")) (only parsing).
Variable K : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable LBX : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SECT) 10%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SECT) 11%nat 0%nat).
Variable cat : ltac:(sec_ty2 constr:(SECT) 12%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 13%nat 0%nat).
Variable str : ltac:(sec_ty2 constr:(SECT) 14%nat 0%nat).
Variable sm : ltac:(sec_ty2 constr:(SECT) 15%nat 0%nat).
Variable e : ltac:(sec_ty2 constr:(SECT) 16%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SECT) 17%nat 0%nat).
Variable fl : ltac:(sec_ty2 constr:(SECT) 18%nat 0%nat).
Variable LK2 : ltac:(sec_ty2 constr:(SECT) 19%nat 0%nat).
Variable M2 : ltac:(sec_ty2 constr:(SECT) 20%nat 0%nat).
Variable model2 : ltac:(sec_ty2 constr:(SECT) 21%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SECT) 22%nat 0%nat).
Variable model1 : ltac:(sec_ty2 constr:(SECT) 23%nat 0%nat).
Variable LK1 : ltac:(sec_ty2 constr:(SECT) 24%nat 0%nat).
Variable Aw1 : ltac:(sec_ty2 constr:(SECT) 25%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SECT) 26%nat 0%nat).
Variable sm1 : ltac:(sec_ty2 constr:(SECT) 27%nat 0%nat).
Variable e1 : ltac:(sec_ty2 constr:(SECT) 28%nat 0%nat).
Variable cr1 : ltac:(sec_ty2 constr:(SECT) 29%nat 0%nat).
Lemma hfacts_of : ltac:(sec_stmt2 constr:(SECT) 30%nat 0%nat).
Proof.
intros CTX G LM.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 288 + 32) :: FF) fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
destruct RP1 as (PA1 & _).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof PA1 as (_ & _ & _ & P8 & P9 & _ & _ & _ & _ & _ & _ & P328 & _ & _ & _ & PM01 & PD01 & _).
set (op := PMSPA.o_p PMB.AD fb) in *.
split; [apply (proj2 (L5A.u8_at_vis _ M1 (op + 8) _ ltac:(apply OVIS; lia) ltac:(lia) ltac:(lia))); exact P8|].
split; [apply (proj2 (L5A.u8_at_vis _ M1 (op + 9) _ ltac:(apply OVIS; lia) ltac:(lia) ltac:(lia))); exact P9|].
split; [apply (proj2 (L5A.u64_at_vis _ M1 (op + 328) _ ltac:(apply OVIS; lia) ltac:(lia) ltac:(lia))); exact P328|].
exact (conj PM01 PD01).
Qed.
End S.
End WithHeap.
End PMBLPK4.
