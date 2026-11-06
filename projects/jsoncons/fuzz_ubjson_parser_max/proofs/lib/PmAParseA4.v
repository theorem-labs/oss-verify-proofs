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
PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmParKit PmAParseD PmAParseK PmAParseK3 PmAParseK4 PmAParseK5 PmAParseK6 PmAParseK7 PmAParseK8 PmAParseK9 PmAParseK10 PmAParseP1 PmAParseP2 PmAParseP3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseA4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3le"; "4Z"; "0F"; "0FF"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "5Model"; "6bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0R"; "0R1"]; ["0R2"; "7credit"; "8fframe"; "9SCFG"; ":aframe"; ":alinv"; ":apctx"; ":lmem"; ":lregs"; ";ADDR_A"; "<PS"; "<PST"; "<inv"; "<p_src"; "<pst"; "<pstate"]; ["<sr_rem"; "<srcst"; "<strm"; "<unread"; "<vstr"; "=lp_mu"; ">cfg"; ">ec_at"; ">o_ec"; ">o_p"; "?end_object_spec"; "?ignore_spec"; "?make_ec_spec"; "?peek_spec"; "?read_key_spec"; "@FPState"]; ["@getr"; "ATSet"; "Bsrealizes"; "Cloaded_segments"; "0SCFG_P"; "Dle"; "Dlt"; "Dof_nat"; "0ar"; "0cat"; "0cr"; "0cr1"; "0cr2"; "0dn1"; "0dp1"; "0e"]; ["0e1"; "0e2"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0mo1"; "0model"; "0model1"; "0model2"; "0model2'"; "0pre"; "0r"; "0s"; "0s1"; "0s2"]; ["0sm"; "0sm1"; "0sm2"; "0sp"; "0src1"; "EZ_to_bv"; "Ebv"; "0str"; "0tb1"; "0tg1"; "0ti"; "0tl"; "0tt"; "0vb1"; "0vk1"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPA4.
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
Lemma p9_eof : ltac2:(TCodec.tc2 tcn__PmAParseA4 "T;&R1&Iy5'S6yR0%211%5241'9y8%611%311p061'H'7':'=%2211%411&Q2%611&Q1'Q>'QD'QB'4'QO&QLvR4vBvR8v@%544321&Q6rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrA%BEGFEDA@?>=<;:987654321&Q4r@r?r>r=%5BLKJGFEDCBA@?;74321&Q8rQ2r<&QI&Q9%221D&QH%123F%8676I31A&Q7rQ3r;r:r9r8r7r6r5%9JQ?Q>Q=8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321';&R0&S5&R7u:%211%42R@1%62M1+X0%72RA1%:3RA31&QG&R3%J2LQBz%453Q521QC'R2&Q3%11R3&QF+eaUH%269Q@Q=1Q<Q;rQ7%74;521p091p0?1p0K1p0Q61p0Q@1p0QG1p0R;1pTHRG1pU2RD1pV4RF1pUNRI1p4RN1pQ<RM1pUBS51pQHS71pR0S=1pU:RK1pUDS91pQJS;1pQ>S41pU8S91pNS:1pU0S21pV2S41pV@S61pULS81pTDS?1pU6S@1pUJSA1pV8SB1pTFS>1p2SB1pQ:SA1pQ0SB1pQ8SE1pU@SK1pQFSM1pQNT31pQ4T:1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1.
intros MKE CTX G LR LM A10 EC1.
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
cfeed P (PMALPP3.alpP9e_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & Z1 & Z10 & Z11).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xac4b8 0xae974 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMALPD.lregs R R2 sp op oec F) by (apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP3.KS_alpP9e LR0 KS2); PMALPK4.ksinc).
exact (PMALPK8.mkec_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 1 0 cat MKE CTX G LR2 LM' Z1 Z10 Z11 ltac:(clear; lia) EC1).
Qed.
Lemma p9_close : ltac2:(TCodec.tc2 tcn__PmAParseA4 "WE&R1&Iy5'S6yR0%211%5241'9y8%611%311p061'H'7':'=%2211%411&Q2%611&Q1'Q>'QD'QB'4'QO'QA'Q?%?11&QKvR4vBvR8v@%544321&QJ%146543&Q6rQ=rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrM%BEIHGFA@?>=<;:987654321&Q4rLrKrJrI%5BNMLGFEDCBA@?;74321&Q8rQ>rH&QI&Q9%221D&QH%123F%8676I31A&Q7rQ?rGrFrE(Q;rDrCrBrAr@r?r>r=&3r<(5(Q:+9r;r:r9%544321(8%11R4%93R531%<3R6;1%F9EDCBA@?>1r8r7r6%OJR7R6R5NQ7R0QOQNQMQLQKQJQHQFQEQDQCQBQ6MLK4321';&R0&S5&R7u:%211%42S;1%62QC1+SM%72S<1%:3S<31&QG&R3%Q@2QBR8z%453QK21R9&Q<%Q04OQ5Q4Q2%Q23RN1J%Q53ROQ81%Q?9QBQAQ@Q>Q=Q<Q;Q:1%511&R5+1&Q@%11QE%4231'<u2&6%Q=4Q<QDQCQB%Q?3S;1Q7%QB3S<QG1%42S=1%7261&Q5rQOrQNrQMrQLrQKrQJrQIrQHrQGrQErQDrQCrQBrQArQ@r5r4r3r2r1%ELT0SOSNDCBA@?>=<;:9876RGR3QLQKQJ54321&R6&QC&Q=%119%3219%42SDS9%6221'R2&Q3%11T;&QF+e`m0%26QIRFRB1RAR@rR2%74QK521p091p0A1pTJTM1pU4TJ1pV6TL1pV0TO1p6U41pQ@U31pUFU;1pQLU=1pR2UC1pU<U11+eaUH%B6R9T:T91T8T7%F4R:D1Q:p041p0QF1p0QO1p0R51p0R<1p0RB1p0RN1p0SO1p0T91p0T@1p0U41p0U71pTHUF1pU2UC1pV4UE1pVFUN1pVJUO1pVHV01pUHUD1pVNV21pVLV31pVDV41pVBUN1pV:UK1pTNV71pTLV81pU>V91p4V81pQ<V71pUBV?1pQHVA1pR0VG1pU:V51pUDVC1pQJVE1pQ>V>1pU8VC1pNVD1pU0V<1pV2V>1pV@V@1pULVB1pTDVI1pU6VJ1pUJVK1pV8VL1pTFVH1p2VL1pQ:VK1pQ0VL1pQ8VO1pU@W51pQFW71pQNW=1pQ4WD1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros IG EA CTX G LR LM A10 EC1 INV1 REM1 L2 IH.
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
cfeed P (PMALPP3.alpP9c_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & Z1 & Z10 & Z11).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 fx1 fx2 R1 R2 0xac4b8 0xaea50 M2v K G LM MS2 FRZ2).
intros model1' LM'.
assert (LR2 : PMALPD.lregs R R2 sp op oec F) by (apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP3.KS_alpP9c LR0 KS2); PMALPK4.ksinc).
pose proof LR2 as (Y2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y3 & Y4).
unfold PMA.ignore_spec, PMSPA.ignore_spec in IG.
apply (PMALPK10.src_call L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaea50 _ _ fx2 R2 M1 model1' LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 0xac4d8 0 cat IG CTX G LM' Z1 ltac:(split; [clear; lia| reflexivity]) Y2 Y3 Y4 Z10 Z11 EC1).
intros fx3 R3 M3 model3 LK3 Aw3 src3 sm3 RP3 RES3 LM3 EC3.
pose proof (PMALPK4.lregs_pres R R2 R3 sp _ _ F LR2 RP3) as LR3.
destruct RES3 as (_ & C1). cbn [PM.p_src] in C1. specialize (C1 REM1). unfold PMSPA.consumed in C1.
set (s3 := PMSPA.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) src3) in *.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 e1 cr1 0 cat CTX G LM3 EC3) as LF.
pose proof LR3 as LR0'.
set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR3.
cfeed P (PMALPP3.alpI9_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & W1 & W10 & W11 & W12).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 e1 cr1 fx3 fx4 R3 R4 0xac4d8 0xaefb0 M4v K G LM3 MS4 FRZ4).
intros model3' LM3'.
assert (LR4 : PMALPD.lregs R R4 sp op oec F) by (apply (PMALPK4.lregs_ks R R3 R4 sp op oec F PMALPP3.KS_alpI9 LR0' KS4); PMALPK4.ksinc).
unfold PMA.end_object_spec, PMSPA.end_object_spec, PMSPA.run_spec in EA.
apply (PMALPK9.vcall_j L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaefb0 1 0xac4e8 _ _ fx4 R4 M3 model3' LK3 Aw3 s3 sm3 e1 cr1
(fun s5 sm5 => PM.unread (PM.p_src s5) sm5 < PM.unread src1 sm1) EA CTX G LM3' ltac:(clear; lia) LR4 W1 ltac:(split; [clear; lia| reflexivity])).
- split; [split; [exact W10| split; [exact W11| exact W12]]| exact L2].
- exact INV1.
- exact EC3.
- intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 e5 cr5 LR5 LM5 JP5.
exact (PMALPK6.after_CE9 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx5 R5 M5 model5 LK5 Aw5 s5 sm5 e5 cr5 CTX G LR5 LM5 JP5).
- intros R5 s5 sm5 INV5 (_ & UE) U0 STP. rewrite UE. unfold s3, PMSPA.with_src. cbn [PM.p_src]. clear - C1. lia.
- intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 e5 cr5 LI5 Q5. exact (IH fx5 R5 M5 model5 LK5 Aw5 s5 sm5 e5 cr5 LI5 Q5).
Qed.
Lemma p9_val K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 (fx1 : FPState) R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1 (cv : Z) :
PMA.read_key_spec L ar HI ->
PMALPD.apctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat s str sm e ->
PMALPD.aframe L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
PMALPD.lregs R R1 sp (PMSPA.o_p PMA.AD fb) (PMSPA.o_ec PMA.AD fb) F ->
PMALPD.lmem L ar HI R M model LBX FF LK Aw cr sp fb s str sm e F M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 ->
getr R1 (reg 10) = Z_to_bv 64 cv -> 0 <= cv <= 255 -> cv <> 125 -> PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMA.AD fb) 0 cat -> PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) -> ti < 16777216 -> 0 <= ti ->
(forall (fx2 : FPState) R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2,
PMALPD.alinv L ar HI R M model LBX FF LK Aw cr sp fb cat s str sm e F R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 -> PM.unread (PM.p_src s2) sm2 < PM.unread src1 sm1 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xac3a0 M2' model2') K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xac4b8 M1 model1) K.
Proof.
intros CALL CTX G LR LM A10 Hc Hne EC1 INV1 HLT HI0 IH.
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 pre _ CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & HMX & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof INV1 as (_ & _ & _ & SH1 & _). cbn [PM.p_stk] in SH1.
destruct (PMPK2.top_of_shape pre (PM.PS 9 tl tt ti) SH1) as (TOK & _).
assert (RI : 0 <= ti <= 16777215) by (clear - HLT HI0; lia). assert (RI' : 0 <= ti < 2 ^ 64) by (clear - RI; lia).
assert (Hc' : 0 <= cv < 2 ^ 64) by (clear - Hc; lia).
destruct (Z_le_gt_dec cv 124) as [CH|CH].
{
assert (KR : 0 <= cv <= 124) by (clear - Hc Hne CH; lia).
cfeed P (PMALPP3.alpP9l_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | 39%nat => ti | 55%nat => cv | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & EW).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 9 tl tt ti (ti + 1) PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 9 tl tt ti) (PM.PS 9 tl tt (ti + 1)) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac4b8 0xaec6c Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP3.KS_alpP9l LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt (ti + 1)]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [| cbn [PM.ps_mode]; split; intros X; exact X].
clear - TOK HLT HI0; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia. }
pose proof LRa as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
unfold PMA.read_key_spec, PMSPA.read_key_spec, PMSPA.run_spec in CALL.
apply (PMALPK3.alp_call_run L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaec6c 7 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt (ti + 1)])) sm1 e1 cr1 0xac8a8
CALL CTX G LMa ltac:(clear; lia) ERA ltac:(split; [clear; lia| reflexivity]) X2 X3 X4 ltac:(split; [exact E10| split; [exact E11| exact E12]]) INVa ECa).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 LM2.
pose proof (PMALPK4.lregs_pres R Ra R2 sp _ _ F LRa RP2) as LR2.
destruct POST2 as (RPR2 & STP2 & _ & [(v & Hv & ECv & _)|(EC2 & INV2 & PK & UK)]).
- exact (PMALPK8.after_keye_9 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 v _ CTX G LR2 LM2 Hv ECv).
- destruct s2 as [mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 stk2]. cbn [PM.p_stk] in PK. subst stk2.
apply (PMALPK8.after_key0_9 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 pre tl tt (ti + 1) sm2 e2 cr2 CTX G LR2 LM2 EC2 INV2).
intros fx3 R3 M3 model3 LI3. apply (IH fx3 R3 M3 model3 LK2' Aw2 _ sm2 e2 cr2 LI3). cbn [PM.p_src] in UK |- *. exact UK.
}
{
assert (KR : 126 <= cv <= 255) by (clear - Hc Hne CH; lia).
cfeed P (PMALPP3.alpP9h_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | 39%nat => ti | 55%nat => cv | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & EW).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 9 tl tt ti (ti + 1) PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 9 tl tt ti) (PM.PS 9 tl tt (ti + 1)) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac4b8 0xaec6c Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP3.KS_alpP9h LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt (ti + 1)]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [| cbn [PM.ps_mode]; split; intros X; exact X].
clear - TOK HLT HI0; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia. }
pose proof LRa as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
unfold PMA.read_key_spec, PMSPA.read_key_spec, PMSPA.run_spec in CALL.
apply (PMALPK3.alp_call_run L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaec6c 7 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt (ti + 1)])) sm1 e1 cr1 0xac8a8
CALL CTX G LMa ltac:(clear; lia) ERA ltac:(split; [clear; lia| reflexivity]) X2 X3 X4 ltac:(split; [exact E10| split; [exact E11| exact E12]]) INVa ECa).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 LM2.
pose proof (PMALPK4.lregs_pres R Ra R2 sp _ _ F LRa RP2) as LR2.
destruct POST2 as (RPR2 & STP2 & _ & [(v & Hv & ECv & _)|(EC2 & INV2 & PK & UK)]).
- exact (PMALPK8.after_keye_9 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 v _ CTX G LR2 LM2 Hv ECv).
- destruct s2 as [mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 stk2]. cbn [PM.p_stk] in PK. subst stk2.
apply (PMALPK8.after_key0_9 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 pre tl tt (ti + 1) sm2 e2 cr2 CTX G LR2 LM2 EC2 INV2).
intros fx3 R3 M3 model3 LI3. apply (IH fx3 R3 M3 model3 LK2' Aw2 _ sm2 e2 cr2 LI3). cbn [PM.p_src] in UK |- *. exact UK.
}
Qed.
Lemma p9_valx K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 (fx1 : FPState) R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt sm1 e1 cr1 (cv : Z) :
PMA.make_ec_spec L ar HI ->
PMALPD.apctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat s str sm e ->
PMALPD.aframe L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
PMALPD.lregs R R1 sp (PMSPA.o_p PMA.AD fb) (PMSPA.o_ec PMA.AD fb) F ->
PMALPD.lmem L ar HI R M model LBX FF LK Aw cr sp fb s str sm e F M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt 16777216])) sm1 e1 cr1 ->
getr R1 (reg 10) = Z_to_bv 64 cv -> 0 <= cv <= 255 -> cv <> 125 -> PMSPA.ec_at RSEGS M1 (PMSPA.o_ec PMA.AD fb) 0 cat ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xac4b8 M1 model1) K.
Proof.
intros MKE CTX G LR LM A10 Hc Hne EC1.
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt 16777216])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt 16777216])) sm1 e1 cr1 pre _ CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt 16777216])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & HMX & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (Hc' : 0 <= cv < 2 ^ 64) by (clear - Hc; lia).
destruct (Z_le_gt_dec cv 124) as [CH|CH].
{
assert (KR : 0 <= cv <= 124) by (clear - Hc Hne CH; lia).
cfeed P (PMALPP3.alpP9lx_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | 55%nat => cv | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & _ & EW).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 9 tl tt 16777216 16777217 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 9 tl tt 16777216) (PM.PS 9 tl tt 16777217) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac4b8 0xae974 Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP3.KS_alpP9lx LR0 KSa); PMALPK4.ksinc).
exact (PMALPK8.mkec_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fxa Ra Ma modela LK1 Aw1 _ sm1 e1 cr1 13 0 cat MKE CTX G LRa LMa ERA E10 E11 ltac:(clear; lia) ECa).
}
{
assert (KR : 126 <= cv <= 255) by (clear - Hc Hne CH; lia).
cfeed P (PMALPP3.alpP9hx_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | 55%nat => cv | _ => 0 end)) ltac:(first [assumption | unfold PMALPP3.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & _ & EW).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 9 tl tt 16777216 16777217 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 9 tl tt 16777216) (PM.PS 9 tl tt 16777217) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac4b8 0xae974 Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP3.KS_alpP9hx LR0 KSa); PMALPK4.ksinc).
exact (PMALPK8.mkec_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fxa Ra Ma modela LK1 Aw1 _ sm1 e1 cr1 13 0 cat MKE CTX G LRa LMa ERA E10 E11 ltac:(clear; lia) ECa).
}
Qed.
Lemma arm_H9 : ltac2:(TCodec.tc2 tcn__PmAParseA4 "V<&R1&Iy5'S6yR0%211%5241'9y8%611%311p061'H'7':'=%2211%411&Q2%611&Q1'Q>'QD'QB'4'QO'QA'Q?%?11&QMvR4vBvR8v@%544321&QK%146543&QJ%148765&QN%14:987&QL%14<;:9&Q6rQ@rQ?rQ>rQ=rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0%BEONMLA@?>=<;:987654321&Q4rOrNrMrL%5BQ4Q3Q2GFEDCBA@?;74321&Q5rQArKrJrIrHrG(Q;rFrErDrCrBrAr@r?&3r>(5(Q:+9r=r<r;%544321(8%11R3%93R431%<3R5;1%F9EDCBA@?>1r:r9r8%Q1LR6R5R4Q0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321rQLrQKrQJrQIrQHrQGrQFrQErQDrQBr7r6r5r4r3r2r1%QCLRHRGRFA@?>=<;:98QBR;R:R9R8R7DC7654321&R6&QE%1287%Q44Q3QCQBQA%Q63S11N%Q93S2QF1%QC9R4R3R2QOQNQMQLQH1%621QC%8261'R2&R3&Q3%11S6&QF+e`m0%265Q=Q<1Q5Q4rQO%847521p0:1p0D1pTJSH1pU4SE1pV6SG1pV0SJ1p6SO1pQ@SN1pUFT61pQLT81pR2T>1pU<SL1%A6DRFRE@RDR@%F4EC1Q9p031p0QD1p0RG1p0RN1p0SB1p0SE1p0SH1p0SK1p0SN1pTHT=1pU2T:1pV4T<1pVFTE1pVJTF1pVHTG1pUHT;1pVNTI1pVLTJ1pVDTK1pVBTE1pV:TB1pTNTN1pTLTO1pU>U01p4TO1pQ<TN1pUBU61pQHU81pR0U>1pU:TL1pUDU:1pQJU<1pQ>U51pU8U:1pNU;1pU0U31pV2U51pV@U71pULU91pTDU@1pU6UA1pUJUB1pV8UC1pTFU?1p2UC1pQ:UB1pQ0UC1pQ8UF1pU@UL1pQFUN1pQNV41pQ4V;1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros PK IG EA CALL MKE CTX G LI IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 pre _ CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & HMX & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 9 tl tt ti) SH1) as (TOK & TPOS).
assert (NB : ~ PM.mode_bottom 9) by (unfold PM.mode_bottom; clear; lia).
assert (L2 : (2 <= length (pre ++ [PM.PS 9 tl tt ti]))%nat).
{ destruct TPOS as [(_ & X)|(X & _)]; [exfalso; exact (NB X)|]. destruct pre as [|p0 pre0]; [exfalso; apply X; reflexivity|]. cbn [length app]. rewrite length_app. cbn [length]. clear; lia. }
assert (TI : 0 <= ti <= 16777216) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
cfeed P (PMALPP2.alpH9_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | _ => 0 end)) ltac:(first [assumption | unfold PMALPP2.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 fx1 fxa R1 Ra 0xac3a0 0xae850 Mav K G LM MSa FRZa).
intros model1' LM'.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP2.KS_alpH9 LR0 KSa); PMALPK4.ksinc).
pose proof LRa as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
unfold PMA.peek_spec, PMSPA.peek_spec in PK.
apply (PMALPK10.src_call L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xae850 _ _ fxa Ra M1 model1' LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 0xac4b8 0 cat PK CTX G LM' ERA ltac:(split; [clear; lia| reflexivity]) X2 X3 X4 E10 I EC1).
intros fx2 R2 M2' model2' LK2' Aw2 src2 sm2 RP2 RES2 LM2 EC2.
pose proof (PMALPK4.lregs_pres R Ra R2 sp _ _ F LRa RP2) as LR2.
destruct RES2 as (CONS0 & [A256|(cv & Hc & Acv & REM2)]); cbn [PM.p_src] in CONS0; unfold PMSPA.consumed in CONS0.
- exact (p9_eof K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 _ sm2 e1 cr1 MKE CTX G LR2 LM2 A256 EC2).
- destruct (Z.eq_dec cv 125) as [->|Hne].
+ apply (p9_close K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo1 dn1 dp1 src2 tb1 tg1 vb1 vk1 pre tl tt ti sm2 e1 cr1 IG EA CTX G LR2 LM2 Acv EC2 INV1 REM2 L2).
intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 U3. apply (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3).
pose proof LI3 as (_ & INV3 & _ & (_ & RPR3 & _)). pose proof INV3 as (_ & _ & _ & SH3 & _).
apply (PMPK2.lp_mu_lt_U (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 s3 sm3 SH1 SH3 (PMALPK9.unread_nonneg _ _ _ _ _ _ RPR3)). cbn [PM.p_src]. clear - U3 CONS0; lia.
+ assert (Hc2 : 0 <= cv <= 255) by (clear - Hc; lia).
destruct (Z_lt_le_dec ti 16777216) as [HLT|HGE].
* apply (p9_val K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo1 dn1 dp1 src2 tb1 tg1 vb1 vk1 pre tl tt ti sm2 e1 cr1 cv CALL CTX G LR2 LM2 Acv Hc2 Hne EC2 INV1 HLT ltac:(clear - TI; lia)).
intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 U3. apply (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3).
pose proof LI3 as (_ & INV3 & _ & (_ & RPR3 & _)). pose proof INV3 as (_ & _ & _ & SH3 & _).
apply (PMPK2.lp_mu_lt_U (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 s3 sm3 SH1 SH3 (PMALPK9.unread_nonneg _ _ _ _ _ _ RPR3)). cbn [PM.p_src]. clear - U3 CONS0; lia.
* assert (E16 : ti = 16777216) by (clear - TI HGE; lia). subst ti.
exact (p9_valx K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo1 dn1 dp1 src2 tb1 tg1 vb1 vk1 pre tl tt sm2 e1 cr1 cv MKE CTX G LR2 LM2 Acv Hc2 Hne EC2).
Qed.
End WithHeap.
End PMALPA4.
