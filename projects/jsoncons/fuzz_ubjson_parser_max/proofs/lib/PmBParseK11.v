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
PmModelFactsA PmStepAB0 PmStep PmFrame PmParKit PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBParseD PmBParseK PmBParseK4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseK11 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "1bool"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"]; ["0LBX"; "0LK"; "0LK1"; "0LK2"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M1"; "0M1'"; "0M1v'"; "0M2"; "0R"; "0R1"; "0R1'"; "6mrestrict"]; ["7msteps"; "8credit"; "9ahid"; "9fframe"; ";defined"; ";u8_at"; ":SCFG"; "<aframe"; "<apctx"; "<lmem"; "=ADDR_B"; ">CHUNK"; ">PST"; ">VLong"; ">p_b"; ">p_depth"]; [">p_done"; ">p_k"; ">p_more"; ">p_src"; ">p_stk"; ">p_tb"; ">p_tg"; ">parser_at"; ">pst"; ">pstate"; ">sr_qc"; ">strm"; ">vec_at"; ">vstr"; "?agA"; "?agsh"]; ["@accA"; "@annA"; "@cfg"; "@ec_at"; "@o_ec"; "@o_p"; "AFPState"; "Amkst"; "Aseg_rom"; "BTSet"; "Csrealizes"; "Dmem_grows"; "Eloaded_segments"; "0SCFG_P"; "Fadd"; "Fle"]; ["Flt"; "Fmul"; "Fpow"; "0a"; "0ar"; "0c"; "0cat"; "0cr"; "0cr1"; "0dv"; "0e"; "0e1"; "0fb"; "0fl"; "0fx"; "0fx'"]; ["0model"; "0model1"; "0model1'"; "0model2"; "0mv"; "0n"; "0ois"; "0op"; "0p"; "0pc"; "0pc'"; "0r"; "0s"; "0s1"; "0sm"; "0sm1"]; ["0sp"; "GZ_to_bv"; "Gbv"; "0stk'"; "0str"; "0v"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPK11.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK11 "SG'SByR0%211'4y8%511%311p051':'QH'3'QI%211&QG&R<&Q:&R0&R1r6r4r3r2%9887654321&R?zr5%3221&R>+\0%22;1&RB+2+R0%3221%;251&QNr9r8r7+[8%544321&QOr:%24176?&Q4%1339A&QLr;%E269&Q>%11=&QA%11?%78Q7Q5Q46531?&QJ&QC%11D%311%Q32Q21%41A%611&Q;%Q3221%Q821Nr?r>%;1C%=11%Q144317'7'QM&QE%118(Q=r1%23QGQF1%73641rDrC%Q<421QJQLp041pVBR91pV<R:1pU<R;1r@(Q<&QBr=%211&Q@%113&Q?%115%Q616%G17&QF%119%Q@1:%Q?1;r<%?9<:8764321%RH8RGRFRERDAQ5Q41p0C1p0Q31p0Q91p0Q?1p0QE1p0QN1p0R11p0R51p0R<1p0RE1p0RJ1pW8S51pVJS91pV>S;1pV@S<1pQ@S>1pQ>S?1")) (only parsing).
Variables (M M' : word -> option byte).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable stk' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Lemma parser_vec_updA : ltac:(sec_stmt2 constr:(SECT) 6%nat 0%nat).
Proof.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
AG2 SH D' VEC' Hq Hq' AGQ AGT.
pose proof AG2 as [AG2d _].
unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op <= a -> a + n <= op + 360 -> PMFA.agA M M' a n).
{ intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 op 8); lia| lia| lia| exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 8) 1); lia|lia|lia|exact H8]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 9) 1); lia|lia|lia|exact H9]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 12) 4); lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [exact VEC'|].
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK11 "TK'SByR0%211'4y8%511%311p051':'QH&QG&R<&Q:&R0&R1r7r5r4r3%9887654321&R?zr6%3221&R>+\0%22;1&RB+2+R0%3221%;251&QNr:r9r8+8%544321r;+:%@261+[F%:44921&QOr<%2417<D&Q4%1339F&Q5r=%J26>%34Q821Ar>+9%N251%74Q<31E'9'7%13QBDQ5+1%33QDF1%5231&QJ&QC%11<%311%Q>2Q=1r?%511%711&Q;%Q?221%QD21Q:rDrCr@%=11%?11%Q>45418&Q>rA%211%QN2QM1rB%511&RA+Q0&QA%115%QN2QM1%5241%R3271%R821QNrGrF%@1E%91F%R62R51%=2<1%R346541'QM&QE%119(Q=r2r1%33RH21%QB3751rLrK%R>4216RMp041pVBS81pV<S91pU<S:1rH(Q<&Q?rE%211%QI12%D13&QF%115%Q=16%Q617&QD%119%<9QGQF9875431%SG8SFSESDSC>Q4Q31p0@1p0Q01p0Q81p0QC1p0QH1p0QO1p0R61p0R<1p0R=1p0RD1p0RI1p0RN1p0S11p0S51p0S;1p0SB1p0SK1p0T01pUDT<1pV:T=1pVJT=1pV>T?1pV@T@1pQ@TB1pQ>TC1")) (only parsing).
Variables (M M' : word -> option byte).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable mv : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable dv : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Lemma parser_md_updA : ltac:(sec_stmt2 constr:(SECT) 7%nat 0%nat).
Proof.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 _] AG2 SH D' C8 C9 Hv Hd Hq Hq' AGQ Hb Hb' AGV AGT.
pose proof AG2 as [AG2d _].
unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 10 <= a -> a + n <= op + 384 -> PMFA.agA M M' a n).
{ intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG1| lia| lia| exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [exact C8|].
split; [exact C9|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 12) 4); lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| exact AGV| exact VEC]|].
split; [exact Hv|]. split; [exact Hd| exact B3].
Qed.
End S.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBParseK11 "W3&R9&Ey5'SByR0%211%5241'4y8%611%311p061'D'3'5':%2211%411&Q3%611&Q1'QH'QM'QK'2'R6&Q8vR=v?vRDv=rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrG%FEEDCBA@?>=<;:987654321&Q7rFrErDrC%5BJIHGFEDCBA@?;74321&Q9rQ8rBrAr@r?r>r=r<%9JQ4Q3Q28Q1Q0ONMLKJHFEDCB;7654321'Q0&R<&R7r:&SAr8%22R31&O&Q2%12@E%321G&R8%11;%;5?:731r;r9r7%=2R>1r6%A554217%D3C71&R;%>2NQ3%@21Q5%3218'6&R?zr1%3221&R@&RB+2+R0%3221%5271%;271&8&R>&R5&Q:%221R7+8%5221r2%C221%823>%A231%G231%<11'7r3%Q@2SA1%Q711%Q>2R5R9%Q@31R;3%63S?31p081p0F1pU8S=1&Q5%F2ERJ+9%I221+1%54R0QB21%64R1QOGQ7&R3&R4%12MS4%35R5RJ1R3QGrQArQ@rQ?rQ>rQ=rQ<rQ;rQ:rQ9(Q<&Q?%11S5&QC%11S7&QE%11S9&QF%11S;&Q>%11S=&QA%11S?&QD%11SA%?9R4O=;97531%S:JT5T4T3IHGFEDCBAT2T0SOSNSMSLQDR4SESD1SBS?S>%M2QIS:%O5S1Q?1S6S5'R:&Q6%11T;&R2r4%26S7SFSDS?1QErQD%74S9521p091p0<1pV6U21pQDU41%96S>SKSFSDT5T4%=4S?;1Q9p031p0Q<1p0QA1p0QC1p0QJ1p0RN1p0S31p0SI1p0T41p0T;1pU<U=1pW<U>1pQFUC1pVFU@1pVDUA1pQNUK1pQLUL1pV0U:1pUNU;1pUBUA1pUHU>1pW0U@1pVLUC1p4UH1pQ6UG1pV4UO1pQBV11pV8V11pQHV31pQ8UL1pULV11pHV21pUFUJ1pVNUL1pW:UN1pVJV01pU>V71pUJV81pVHV91pW2V:1pU@V61p2V:1pQ4V91pJV:1pQ2V=1pV2VC1pQ>VE1pQJVK1pNW21")) (only parsing).
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
Variables (fx fx' : FPState).
Variable R1 : ltac:(sec_ty2 constr:(SECT) 32%nat 0%nat).
Variable R1' : ltac:(sec_ty2 constr:(SECT) 33%nat 0%nat).
Variables (pc pc' : Z).
Variable M1v' : ltac:(sec_ty2 constr:(SECT) 36%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 37%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 38%nat 0%nat).
Lemma md_run : ltac:(sec_stmt2 constr:(SECT) 39%nat 0%nat).
Proof.
intros CTX G LM MS MG FZ DO MO EC1 KX.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof FOK as ((rs & Hfb) & Fal).
destruct LM as (BI & RP1 & LS1 & STEP1 & EE1 & CK1).
pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1). change (PMSPA.pm_scr 10) with 32768 in *.
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
destruct RP1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
set (ois := PMSPA.o_is PMB.AD fb) in *.
assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & WF1 & FSAPP1 & FSCEIL1 & _).
pose proof (WF1 _ (or_intror Hfb)) as (FB1 & FB2 & _). cbn [ff_addr ff_class fst snd] in FB1, FB2. change (ff_bytes 4) with 1024 in *.
unfold app_mem, FS_BYTES in FSAPP1, FB2.
assert (AOF : forall a k0, fb + 32 <= a -> a + k0 <= fb + 1016 -> PMSPA.aobjA FF' a k0).
{ intros a k0 X1 X2. exists (fb, 4, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - X1 X2; lia. }
pose proof G as G'. unfold PMBLPD.aframe in G'.
destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF' LK1 cr1 Aw1 M1 model1 fx fx' R1 pc R1' pc' M1v' (fun a => op + 8 <= a < op + 10) K HH1 AM1 MS MG).
{ intros a Ha Nw. apply FZ; [exact Ha| intros X; apply Nw; clear - X; lia]. }
{ intros a Ha Wa. split.
- apply (L5SAR.fframe_client L ar LB1 FF' 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - Wa Eop; lia].
- clear - Wa O1. lia. }
intros M1' model1' HH1' AM1' MRT1' HID1' VIS1' MGM1' FR1' VV1'.
assert (EKf : L5SAR.ek L ar LB1 FF' 0 0 [(op + 8, 2)] M1 M1').
{ apply (L5SAR.ek_piece L ar LB1 FF' 0 0 [(op + 8, 2)] M1 M1' (fun a => op + 8 <= a < op + 10) FR1').
intros a Ha _ O X. apply (O (op + 8, 2)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
assert (MO0f : L5.u8_at RSEGS M1' (op + 8) 0).
{ apply (proj1 (L5A.u8_at_vis (ahid Aw1 model1) M1' (op + 8) 0 (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
rewrite VIS1'. exact MO. }
assert (DO1f : L5.u8_at RSEGS M1' (op + 9) 1).
{ apply (proj1 (L5A.u8_at_vis (ahid Aw1 model1) M1' (op + 9) 1 (OVIS (op + 9) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
rewrite VIS1'. exact DO. }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 10 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 2)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q m, In (q, m) LB1 -> forall i, q <= i < q + m -> L5.outside [(op + 8, 2)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH1 Hq AOP) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPP8 : PMKB.wapp [(op + 8, 2)]).
{ apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (Ivb : In (PM.p_b s1, 32 * 2 ^ PM.p_k s1) LB1) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s1), PM.CHUNK) LB1) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
apply (KX M1' model1').
2: { apply (PMKB.ec_keepA RSEGS L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 _ v c (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC1].
apply OUT8. clear - Eop Eoec; lia. }
split; [| split; [| split; [| split; [exact STEP1| split; [exact EE1| exact CK1]]]]].
- apply (PMBUK.binv_pieceW L ar HI M model LBX FF LK Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R) F fl 1 LK2 M2 model2 cr (PM.parser_own s) G
_ (PM.parser_own s1) M1 model1 LK1 cr1 Aw1 M1' model1' (fun a => op + 8 <= a < op + 10) BI HH1' AM1' MRT1' MGM1' FR1').
intros a X. split.
+ unfold PMBLPD.ocell. clear - X OCE SLO. lia.
+ right; right; right. intros O. apply (O (PMSPA.o_p PMB.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - X; lia].
- unfold PMSPA.run_pre. split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct (BRB1 _ Iqc) as (Xq1 & Xq2). destruct (BRB1 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (parser_md_updA M1 M1' op ois s1 0 1 PA1).
* clear - O1; lia.
* clear - O1; lia.
* apply (PMKB.agA_obj L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* apply (PMKB.agA_obj L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 (op + 10) 374 (AOF (op + 10) 374 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* exact (PMKB.agsh_obj L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 op 384 (AOF op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
* pose proof PA1 as (_ & PD1 & _). apply (L5.defined_grows M1 M1' _ _ MGM1' PD1).
* exact MO0f.
* exact DO1f.
* left; reflexivity.
* right; reflexivity.
* exact Xq1.
* clear - Xq2; lia.
* apply (PMKB.agA_blk L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 BRB1 _ _ Iqc). apply OUTB8. exact Iqc.
* exact Xb1.
* clear - Xb2; lia.
* apply (PMKB.agA_blk L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 BRB1 _ _ Ivb). apply OUTB8. exact Ivb.
* intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LB1) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKB.agA_blk L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 BRB1 _ _ Ip). apply OUTB8. exact Ip.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 BRB1 ois str sm1 (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [| | | exact IA1].
* apply incl_appr. exact INCS.
* apply OUT8. clear - Eop Eois; lia.
* intros c0 n0 p0 E0. unfold PMKB.blk_out. apply (OUTB8 p0 c0). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
+ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS1].
apply OUT8. clear - Eop Eov; lia.
+ apply (PMKB.u64_keepA RSEGS L ar _ FF' 0 0 _ M1 M1' EKf WAPP8 FRB1 (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF1].
apply OUT8. clear; lia.
+ apply (PMBSK.base_keep L ar C LY _ FF' 0 0 _ M1 M1' EKf); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
+ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar _ FF' 0 0 _ M1 M1' EKf e1 PMB.addrs_wf_A); [| exact ERR1].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
+ exact TB1.
- apply (PMBLPD.lspill_agree M1 M1' sp F _ _ _ ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia) LS1).
intros a Ha. apply FR1'; [clear - Ha SLO SHI SPT; lia| clear - Ha OCE SLO; lia].
Qed.
End S.
End WithHeap.
End PMBLPK11.
