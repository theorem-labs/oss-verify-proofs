(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmParKit PmAParseD PmAParseK PmAParseK4 PmAParseK5 PmAParseK6 PmAParseK7 PmAParseK8 PmAParseK9 PmAParseP1 PmAParseP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseA1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"]; ["0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "3Model"; "4bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0R"; "0R1"; "0R2"; "5credit"; "6fframe"]; ["7SCFG"; "8aframe"; "8alinv"; "8apctx"; "9PS"; "9PST"; "9pst"; "9pstate"; "9srcst"; "9strm"; "9vstr"; ":lp_mu"; ";cfg"; "<read_value_spec"; "<rtv_spec"; "=FPState"]; [">TSet"; "?srealizes"; "@loaded_segments"; "0SCFG_P"; "Alt"; "0ar"; "0cat"; "0cr"; "0cr1"; "0cr2"; "0dn1"; "0dp1"; "0e"; "0e1"; "0e2"; "0fb"]; ["0fl"; "0fx1"; "0fx2"; "0mo1"; "0model"; "0model1"; "0model2"; "0model2'"; "0pre"; "0r"; "0s"; "0s2"; "0sm"; "0sm1"; "0sm2"; "0sp"]; ["0src1"; "Bbv"; "0str"; "0tb1"; "0tg1"; "0ti"; "0tl"; "0tt"; "0vb1"; "0vk1"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPA1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma arm_H0 : ltac2:(TCodec.tc2 tcn__PmAParseA1 "UL&Q@&Fy5'RAyR0%211%5241'8y8%611%311p061'E'6'9':%2211%411&O%611&N'Q6'Q:'Q9'4'Q?'Q8'Q7%?11&Q>vQCv?vQEv=%544321&Q3rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q1rKrJrIrH%5BLKJGFEDCBA@?;74321&Q2rQ=rGrFrErDrC(Q5rBrAr@r?r>r=r<r;&3r:(5(Q4zr9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321rQHrQGrQFrQErQDrQCrQBrQArQ@rQ>r3r2r1%Q?LR<R;R:=<;:987654Q>R7R6R5R4R3JIHA@?321&QD&Q;%12CB%Q04OQ?Q>Q=%Q23RE1J%Q53RFQB1%Q?9R0QOQNQKQJQIQHQD1%621Q?%8261'QA&QB&Q0%11RJ&Q<+e`m0%265QAQ@1Q>Q:rQK%847521p0:1p0D1pSDS<1pSNS91pTNS;1pTHS>1p6SC1pQ:SB1pT@SJ1pQFSL1pQLT21pT6S@1%A6DRBRA@R@R<%F4EC1Q5p031p0Q@1p0RC1p0RJ1p0S>1pSBSM1pSLSJ1pTLSL1pU<T51pU@T61pU>T71pTBSK1pUDT91pUBT:1pU:T;1pU8T51pU2T21pSHT>1pSFT?1pT8T@1p4T?1pQ6T>1pT<TF1pQBTH1pQJTN1pT4T<1pT>TJ1pQDTL1pQ8TE1pT2TJ1pHTK1pSJTC1pTJTE1pU6TG1pTFTI1pS>U01pT0U11pTDU21pU0U31pS@TO1p2U31pQ4U21pJU31pQ2U61pT:U<1pQ@U>1pQHUD1pNUK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 0 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 0 tl tt ti])) sm1 e1 cr1 pre (PM.PS 0 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 0 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 0 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMALPP1.alpH0_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _ & _ & EW).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV Mav T 0 tl tt ti 1 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 0 tl tt ti) (PM.PS 1 tl tt ti) sm1 e1 cr1 0 4
fx1 fxa R1 Ra 0xac3a0 0xad164 Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH0 LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 1 tl tt ti)]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (PMALPK8.pstate_ok_mode 0 1 tl tt ti TOK); PMALPK8.miff| cbn [PM.ps_mode]; PMALPK8.miff]. }
unfold PMA.rtv_spec, PMSPA.rtv_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad164 9 705556 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 1 tl tt ti)])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 0 tl tt ti])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [exact E10| split; [exact E11| exact E12]].
- exact INVa.
- exact ECa.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_CR0 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 PP2 U0 STP. destruct PP2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _).
exact (PMALPK9.mu_strict (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 0 tl tt ti])) sm1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 1 tl tt ti)])) s2 sm2 SH1 SH2 U0 eq_refl UV).
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H6 : ltac2:(TCodec.tc2 tcn__PmAParseA1 "UL&Q@&Fy5'RAyR0%211%5241'8y8%611%311p061'E'6'9':%2211%411&O%611&N'Q6'Q:'Q9'4'Q?'Q8'Q7%?11&Q>vQCv?vQEv=%544321&Q3rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q1rKrJrIrH%5BLKJGFEDCBA@?;74321&Q2rQ=rGrFrErDrC(Q5rBrAr@r?r>r=r<r;&3r:(5(Q4+6r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321rQHrQGrQFrQErQDrQCrQBrQArQ@rQ>r3r2r1%Q?LR<R;R:=<;:987654Q>R7R6R5R4R3JIHA@?321&QD&Q;%12CB%Q04OQ?Q>Q=%Q23RE1J%Q53RFQB1%Q?9R0QOQNQKQJQIQHQD1%621Q?%8261'QA&QB&Q0%11RJ&Q<+e`m0%265QAQ@1Q>Q:rQK%847521p0:1p0D1pSDS<1pSNS91pTNS;1pTHS>1p6SC1pQ:SB1pT@SJ1pQFSL1pQLT21pT6S@1%A6DRBRA@R@R<%F4EC1Q5p031p0Q@1p0RC1p0RJ1p0S>1pSBSM1pSLSJ1pTLSL1pU<T51pU@T61pU>T71pTBSK1pUDT91pUBT:1pU:T;1pU8T51pU2T21pSHT>1pSFT?1pT8T@1p4T?1pQ6T>1pT<TF1pQBTH1pQJTN1pT4T<1pT>TJ1pQDTL1pQ8TE1pT2TJ1pHTK1pSJTC1pTJTE1pU6TG1pTFTI1pS>U01pT0U11pTDU21pU0U31pS@TO1p2U31pQ4U21pJU31pQ2U61pT:U<1pQ@U>1pQHUD1pNUK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 6 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 6 tl tt ti])) sm1 e1 cr1 pre (PM.PS 6 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 6 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 6 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMALPP2.alpH6_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP2.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _ & _ & EW).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV Mav T 6 tl tt ti 5 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 6 tl tt ti) (PM.PS 5 tl tt ti) sm1 e1 cr1 0 4
fx1 fxa R1 Ra 0xac3a0 0xad164 Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP2.KS_alpH6 LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt ti)]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (PMALPK8.pstate_ok_mode 6 5 tl tt ti TOK); PMALPK8.miff| cbn [PM.ps_mode]; PMALPK8.miff]. }
unfold PMA.rtv_spec, PMSPA.rtv_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad164 9 706464 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt ti)])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 6 tl tt ti])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [exact E10| split; [exact E11| exact E12]].
- exact INVa.
- exact ECa.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_CR6 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 PP2 U0 STP. destruct PP2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _).
exact (PMALPK9.mu_strict (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 6 tl tt ti])) sm1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt ti)])) s2 sm2 SH1 SH2 U0 eq_refl UV).
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H10 : ltac2:(TCodec.tc2 tcn__PmAParseA1 "UL&Q@&Fy5'RAyR0%211%5241'8y8%611%311p061'E'6'9':%2211%411&O%611&N'Q6'Q:'Q9'4'Q?'Q8'Q7%?11&Q>vQCv?vQEv=%544321&Q3rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q1rKrJrIrH%5BLKJGFEDCBA@?;74321&Q2rQ=rGrFrErDrC(Q5rBrAr@r?r>r=r<r;&3r:(5(Q4+:r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321rQHrQGrQFrQErQDrQCrQBrQArQ@rQ>r3r2r1%Q?LR<R;R:=<;:987654Q>R7R6R5R4R3JIHA@?321&QD&Q;%12CB%Q04OQ?Q>Q=%Q23RE1J%Q53RFQB1%Q?9R0QOQNQKQJQIQHQD1%621Q?%8261'QA&QB&Q0%11RJ&Q<+e`m0%265QAQ@1Q>Q:rQK%847521p0:1p0D1pSDS<1pSNS91pTNS;1pTHS>1p6SC1pQ:SB1pT@SJ1pQFSL1pQLT21pT6S@1%A6DRBRA@R@R<%F4EC1Q5p031p0Q@1p0RC1p0RJ1p0S>1pSBSM1pSLSJ1pTLSL1pU<T51pU@T61pU>T71pTBSK1pUDT91pUBT:1pU:T;1pU8T51pU2T21pSHT>1pSFT?1pT8T@1p4T?1pQ6T>1pT<TF1pQBTH1pQJTN1pT4T<1pT>TJ1pQDTL1pQ8TE1pT2TJ1pHTK1pSJTC1pTJTE1pU6TG1pTFTI1pS>U01pT0U11pTDU21pU0U31pS@TO1p2U31pQ4U21pJU31pQ2U61pT:U<1pQ@U>1pQHUD1pNUK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 10 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 10 tl tt ti])) sm1 e1 cr1 pre (PM.PS 10 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 10 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 10 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMALPP2.alpH10_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP2.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _ & _ & EW).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV Mav T 10 tl tt ti 9 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 10 tl tt ti) (PM.PS 9 tl tt ti) sm1 e1 cr1 0 4
fx1 fxa R1 Ra 0xac3a0 0xad164 Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP2.KS_alpH10 LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 tl tt ti)]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (PMALPK8.pstate_ok_mode 10 9 tl tt ti TOK); PMALPK8.miff| cbn [PM.ps_mode]; PMALPK8.miff]. }
unfold PMA.rtv_spec, PMSPA.rtv_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad164 9 706520 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 tl tt ti)])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 10 tl tt ti])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [exact E10| split; [exact E11| exact E12]].
- exact INVa.
- exact ECa.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_CR10 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 PP2 U0 STP. destruct PP2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _).
exact (PMALPK9.mu_strict (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 10 tl tt ti])) sm1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 tl tt ti)])) s2 sm2 SH1 SH2 U0 eq_refl UV).
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H8 : ltac2:(TCodec.tc2 tcn__PmAParseA1 "UL&Q@&Fy5'RAyR0%211%5241'8y8%611%311p061'E'6'9':%2211%411&O%611&N'Q6'Q:'Q9'4'Q?'Q8'Q7%?11&Q=vQCv?vQEv=%544321&Q3rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q1rKrJrIrH%5BLKJGFEDCBA@?;74321&Q2rQ=rGrFrErDrC(Q5rBrAr@r?r>r=r<r;&3r:(5(Q4+8r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321rQHrQGrQFrQErQDrQCrQBrQArQ@rQ>r3r2r1%Q?LR<R;R:=<;:987654Q>R7R6R5R4R3JIHA@?321&QD&Q;%12CB%Q04OQ?Q>Q=%Q23RE1J%Q53RFQB1%Q?9R0QOQNQKQJQIQHQD1%621Q?%8261'QA&QB&Q0%11RJ&Q<+e`m0%265QAQ@1Q>Q:rQK%847521p0:1p0D1pSDS<1pSNS91pTNS;1pTHS>1p6SC1pQ:SB1pT@SJ1pQFSL1pQLT21pT6S@1%A6DRBRA@R@R<%F4EC1Q5p031p0Q@1p0RC1p0RJ1p0S>1pSBSM1pSLSJ1pTLSL1pU<T51pU@T61pU>T71pTBSK1pUDT91pUBT:1pU:T;1pU8T51pU2T21pSHT>1pSFT?1pT8T@1p4T?1pQ6T>1pT<TF1pQBTH1pQJTN1pT4T<1pT>TJ1pQDTL1pQ8TE1pT2TJ1pHTK1pSJTC1pTJTE1pU6TG1pTFTI1pS>U01pT0U11pTDU21pU0U31pS@TO1p2U31pQ4U21pJU31pQ2U61pT:U<1pQ@U>1pQHUD1pNUK1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 8 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 8 tl tt ti])) sm1 e1 cr1 pre (PM.PS 8 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 8 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 8 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (RT : 0 <= tt <= 255) by (clear - TOK; destruct TOK as (X & _); cbn [PM.ps_type] in X; lia). assert (RT' : 0 <= tt < 2 ^ 64) by (clear - RT; lia).
cfeed P (PMALPP2.alpH8_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 53%nat => tt | _ => 0 end)) ltac:(first [assumption | unfold PMALPP2.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & E13 & _ & EW).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV Mav T 8 tl tt ti 7 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 8 tl tt ti) (PM.PS 7 tl tt ti) sm1 e1 cr1 0 4
fx1 fxa R1 Ra 0xac3a0 0xad5dc Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP2.KS_alpH8 LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt ti)]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (PMALPK8.pstate_ok_mode 8 7 tl tt ti TOK); PMALPK8.miff| cbn [PM.ps_mode]; PMALPK8.miff]. }
unfold PMA.read_value_spec, PMSPA.read_value_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad5dc 8 706600 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt ti)])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 8 tl tt ti])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [exact E10| split; [exact E11| split; [exact E13| exists tt; split; [clear - RT; lia| exact E12]]]].
- exact INVa.
- exact ECa.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_CV8 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 PP2 U0 STP. pose proof INV2 as (_ & _ & _ & SH2 & _). destruct STP as (_ & _ & _ & _ & U32). cbn [PM.p_src] in U32.
exact (PMALPK9.mu_pushv_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 8 tl tt ti) (PM.PS 7 tl tt ti) sm1 s2 sm2 SH1 SH2 ltac:(unfold PMPK2.lp_w, PM.mode_flag; cbn [PM.ps_mode PM.ps_len PM.ps_idx]; cbn; clear; lia) U0 U32 PP2).
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H2a : ltac2:(TCodec.tc2 tcn__PmAParseA1 "UO&Q@&Fy5'RAyR0%211%5241'8y8%611%311p061'E'6'9':%2211%411&O%611&N'Q6'Q:'Q9'4'Q?'Q8'Q7%?11&Q>vQCv?vQEv=%544321&Q3rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q1rKrJrIrH%5BLKJGFEDCBA@?;74321&Q2rQ=rGrFrErDrC(Q5rBrAr@r?r>r=r<r;&3r:(5(Q4+2r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321&QD%12=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&Q;%12ED%Q24Q1QBQAQ@%Q43RG1L%Q73RHQE1%QA9R3R2R1R0QMQLQKQJ1%621QC%H261'QA&QB&Q0%11RL&Q<+e`m0%265QCQB1Q@Q<rQL%847521p0:1p0C1pSDS>1pSNS;1pTNS=1pTHS@1p6SE1pQ:SD1pT@SL1pQFSN1pQLT41pT6SB1%A6DRERD@RCRB%F4EC1Q5p031p0Q@1p0QC1p0RF1p0RM1p0SA1pSBT01pSLSM1pTLSO1pU<T81pU@T91pU>T:1pTBSN1pUDT<1pUBT=1pU:T>1pU8T81pU2T51pSHTA1pSFTB1pT8TC1p4TB1pQ6TA1pT<TI1pQBTK1pQJU11pT4T?1pT>TM1pQDTO1pQ8TH1pT2TM1pHTN1pSJTF1pTJTH1pU6TJ1pTFTL1pS>U31pT0U41pTDU51pU0U61pS@U21p2U61pQ4U51pJU61pQ2U91pT:U?1pQ@UA1pQHUG1pNUN1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HLT IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt ti])) sm1 e1 cr1 pre (PM.PS 2 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 2 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TL8' : L5.u64_at RSEGS MV (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact PT8).
assert (RD : 1 <= tl - ti <= 16777216) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI : 0 <= ti <= 16777215) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RD' : 0 <= tl - ti < 2 ^ 64) by (clear - RD; lia). assert (RI' : 0 <= ti < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP1.alpH2a_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => ti | 54%nat => tl - ti | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _ & _ & EW).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 2 tl tt ti (ti + 1) PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 2 tl tt ti) (PM.PS 2 tl tt (ti + 1)) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac3a0 0xad164 Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH2a LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 2 tl tt (ti + 1))]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia| cbn [PM.ps_mode]; split; intros X; exact X]. }
unfold PMA.rtv_spec, PMSPA.rtv_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad164 9 705876 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 2 tl tt (ti + 1))])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt ti])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [exact E10| split; [exact E11| exact E12]].
- exact INVa.
- exact ECa.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_CR2 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 PP2 U0 STP. destruct PP2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _).
exact (PMALPK9.mu_strict (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt ti])) sm1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 2 tl tt (ti + 1))])) s2 sm2 SH1 SH2 U0 eq_refl UV).
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H4a : ltac2:(TCodec.tc2 tcn__PmAParseA1 "UO&Q@&Fy5'RAyR0%211%5241'8y8%611%311p061'E'6'9':%2211%411&O%611&N'Q6'Q:'Q9'4'Q?'Q8'Q7%?11&Q=vQCv?vQEv=%544321&Q3rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q1rKrJrIrH%5BLKJGFEDCBA@?;74321&Q2rQ=rGrFrErDrC(Q5rBrAr@r?r>r=r<r;&3r:(5(Q4+4r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321&QD%12=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&Q;%12ED%Q24Q1QBQAQ@%Q43RG1L%Q73RHQE1%QA9R3R2R1R0QMQLQKQJ1%621QC%H261'QA&QB&Q0%11RL&Q<+e`m0%265QCQB1Q@Q<rQL%847521p0:1p0C1pSDS>1pSNS;1pTNS=1pTHS@1p6SE1pQ:SD1pT@SL1pQFSN1pQLT41pT6SB1%A6DRERD@RCRB%F4EC1Q5p031p0Q@1p0QC1p0RF1p0RM1p0SA1pSBT01pSLSM1pTLSO1pU<T81pU@T91pU>T:1pTBSN1pUDT<1pUBT=1pU:T>1pU8T81pU2T51pSHTA1pSFTB1pT8TC1p4TB1pQ6TA1pT<TI1pQBTK1pQJU11pT4T?1pT>TM1pQDTO1pQ8TH1pT2TM1pHTN1pSJTF1pTJTH1pU6TJ1pTFTL1pS>U31pT0U41pTDU51pU0U61pS@U21p2U61pQ4U51pJU61pQ2U91pT:U?1pQ@UA1pQHUG1pNUN1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HLT IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt ti])) sm1 e1 cr1 pre (PM.PS 4 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 4 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TL8' : L5.u64_at RSEGS MV (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact PT8).
assert (RD : 1 <= tl - ti <= 16777216) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI : 0 <= ti <= 16777215) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RD' : 0 <= tl - ti < 2 ^ 64) by (clear - RD; lia). assert (RI' : 0 <= ti < 2 ^ 64) by (clear - RI; lia).
assert (RT : 0 <= tt <= 255) by (clear - TOK; destruct TOK as (X & _); cbn [PM.ps_type] in X; lia). assert (RT' : 0 <= tt < 2 ^ 64) by (clear - RT; lia).
cfeed P (PMALPP1.alpH4a_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => ti | 54%nat => tl - ti | 53%nat => tt | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & E13 & _ & EW).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 4 tl tt ti (ti + 1) PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 4 tl tt ti) (PM.PS 4 tl tt (ti + 1)) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac3a0 0xad5dc Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH4a LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 4 tl tt (ti + 1))]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia| cbn [PM.ps_mode]; split; intros X; exact X]. }
unfold PMA.read_value_spec, PMSPA.read_value_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad5dc 8 705688 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 4 tl tt (ti + 1))])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt ti])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [exact E10| split; [exact E11| split; [exact E13| exists tt; split; [clear - RT; lia| exact E12]]]].
- exact INVa.
- exact ECa.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_CV4 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 PP2 U0 STP. pose proof INV2 as (_ & _ & _ & SH2 & _). destruct STP as (_ & _ & _ & _ & U32). cbn [PM.p_src] in U32.
exact (PMALPK9.mu_pushv_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 4 tl tt ti) (PM.PS 4 tl tt (ti + 1)) sm1 s2 sm2 SH1 SH2 ltac:(unfold PMPK2.lp_w, PM.mode_flag; cbn [PM.ps_mode PM.ps_len PM.ps_idx]; cbn; clear; lia) U0 U32 PP2).
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
End WithHeap.
End PMALPA1.
