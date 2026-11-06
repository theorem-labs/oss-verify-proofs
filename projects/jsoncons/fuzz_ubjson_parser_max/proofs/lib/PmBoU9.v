(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit
PmCertKitG PmBaKit PmBoUStmts PmBoU1 PmBoU2 PmBoU8 PmBoUP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU9 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1length"; "1list"; "1option"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0GL"; "0HI"; "0IGN"; "0K"; "0L"; "0LBX"; "4Model"]; ["5bvmap"; "0M"; "0M0"; "0MKE"; "0OPD"; "0OPN"; "0PEEK"; "0R"; "0R0"; "6credit"; "8defined"; "8u8_at"; "7SCFG"; "9mem_ok"; "9regs_at"; "9saves"]; ["9world"; ":inv_d"; ":p_src"; ":p_stk"; ":pst"; ":pstate"; ":sr_rem"; ":strm"; ":unread"; ";ignore_spec"; ";peek_spec"; ";src_read_spec"; "<cfg"; "<ec_at"; "=get_length_spec"; "=make_ec_spec"]; ["=opdel_spec"; "=opnew_spec"; ">FPState"; ">getr"; "?srealizes"; "@loaded_segments"; "0S"; "0SCFG_P"; "0SRD"; "Aadd"; "Ale"; "Alt"; "Aof_nat"; "Apow"; "Asub"; "0c"]; ["0cat"; "0cr"; "0cr0"; "0d"; "0e"; "0e0"; "0fb"; "0fx"; "0model"; "0model0"; "0s0"; "0s1"; "0sm"; "0sm0"; "BZ_to_bv"; "Bbv"]; ["Bbv_unsigned"; "0str"; "0tb"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU9.
Import PMU.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBOU2.push_st.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis PRE : PMBOUS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBOUS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBOUS.kept0 R0).
Local Abbreviation regs_at := (PMBOUS.regs_at R0 S fb).
Local Abbreviation saves := (PMBOUS.saves R0 S).
Local Abbreviation mem_ok := (PMBOUS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBOUS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBOUS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBOU1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBOU1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBOU1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBOU1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBOU1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBOU1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBOU1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBOU1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBOU2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBOU2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBOU2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU9 "B'R?yR0%211'4&QJz&R@r1%2271%5241&QK&QM+2+R0%3221%5271%=271pU8?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBOUP1.aligned; first [assumption | lia]].
Local Ltac prep_ctx M W MO :=
let PA := fresh "PA" in let IA := fresh "IA" in let VIS := fresh "VIS" in let VREF := fresh "VREF" in let BASE := fresh "BASE" in
let ERR := fresh "ERR" in let TB := fresh "TB" in let HH := fresh "HH" in let MB := fresh "MB" in let STEP := fresh "STEP" in
let EE := fresh "EE" in let CK := fresh "CK" in let EK := fresh "EK" in let DK := fresh "DK" in let STK := fresh "STK" in
pose proof W as ((PA & IA & VIS & VREF & BASE & ERR & TB) & HH & MB & STEP & EE & CK);
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF; cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF;
unfold PMSP.visitor_at in VIS; cbn [pa_vp_visitor AD PmLayoutU.ADDR_U] in VIS;
pose proof MO as (EK & DK & STK);
let MOK := fresh "MOK" in pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK;
let Mh := fresh "Mh" in let Ml := fresh "Ml" in pose proof MOK as (Mh & Ml & _);
let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in pose proof FOK as (F1 & F2 & F3);
let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in let X4 := fresh "X4" in let X5 := fresh "X5" in
pose proof SBND as (X1 & X2 & X3 & X4 & X5);
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBOUS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBOU1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBOU1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBOU1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBOU1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBOU1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBOU1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBOU1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let CRED0 := PMBOU1.CRED0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rgp0 := PMBOU1.Rgp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let errp := PMBOU1.errp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let src_call := PMBOU1.src_call L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let arm_t4 := PMBOU8.arm_t4 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Ltac regs_from KS R R1 := split; [rewrite (KS 2%nat) by PMK.inl; assumption|]; split; [rewrite (KS 8%nat) by PMK.inl; assumption|];
split; [rewrite (KS 9%nat) by PMK.inl; assumption|]; split; [rewrite (KS 18%nat) by PMK.inl; assumption|]; split; [rewrite (KS 21%nat) by PMK.inl; assumption|];
apply (kept0_of R R1 _ KS); [vm_compute; reflexivity| assumption].
Local Ltac regs_pres RP R1 R2 := match goal with H : regs_at R1 |- regs_at R2 =>
let Q2 := fresh in let Q8 := fresh in let Q9 := fresh in let Q18 := fresh in let Q21 := fresh in let QK := fresh in
pose proof H as (Q2 & Q8 & Q9 & Q18 & Q21 & QK);
split; [rewrite (PMK.cs_of_preserved R1 R2 2 RP) by PMK.inl; exact Q2|];
split; [rewrite (PMK.cs_of_preserved R1 R2 8 RP) by PMK.inl; exact Q8|];
split; [rewrite (PMK.cs_of_preserved R1 R2 9 RP) by PMK.inl; exact Q9|];
split; [rewrite (PMK.cs_of_preserved R1 R2 18 RP) by PMK.inl; exact Q18|]; split; [rewrite (PMK.cs_of_preserved R1 R2 21 RP) by PMK.inl; exact Q21|];
let k := fresh "k" in let Hk0 := fresh "Hk0" in
intros k Hk0; rewrite (PMK.cs_of_preserved R1 R2 k RP); [apply QK; exact Hk0|];
unfold PMBOUS.CSK in Hk0; cbn in Hk0; repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]); destruct Hk0 end.
Lemma arm_t3 : ltac2:(TCodec.tc2 tcn__PmBoU9 "UK&Q9vQGv=v:%43321&Q>%13543&Q?%13765&QA%13987&Q@%13;:9'QB&@y5'R?yR0%211%5241'3y8%611%311p061'?'Q4'Q7'0&I'8&NvHvQFvR6r8%544321'5&QCr9&R>&QLuC%211%42M1%7261&QI+R0%22>1%92Q01%=3Q051r:uD%<11%>2Q71%A241+1%A2Q81%E3Q831&K&QE&QN+S1%22N1r4%645>21'4&QJzr5%3221&QK+X0%2241%8241'7r=u:%Q511%Q72R01%Q:241%Q92R09%Q=3R021'6r1%B2A1%?22>%E221r>%QC21:%QB2R96%QF3R921&Q6&Q2r;%211%411%N2Q91%Q0271%Q12<1qT0R61%B2R71%K2D1&O%13R8R7L&MvBv>%36S:21R;R:D&Q0vR9vR2vR:vRAvR=vR5r?r<%9@SDSC8;7RD65432NQ:1HR3&Q=r@+8%R<2RH1vR0%55R042QH1&Q1%12R6:'2'Q5%211&Q3%11;%21D%S03421&1%1273%RO11+QP0%R7221&Q8rB%Q@11rA%4221%QC1Q0%621O%R;231'QD&L%11TD&Q<rGrF+WPn4rErD%66S054321v<%;4S2921p0=1p0F1p0L1p0Q41p0Q71p0Q>1p0QI1p0QN1p0R11p0RN1p0S81p0S@1p0SI1p0T81pU6T?1pT4TA1pT:TC1pTJTE1pTHTG1pTBTI1pQ4TK1pQ@U11pT@U81pQ:U:1pQ<U=1pQ8U@1pDUC1pHUF1").
Proof. intros IGN GL MKE OPN OPD fx R M model s1 sm e cr tb.
intros RA R19 R20 TBY Htb PK SV MO W ECZ IV1 ES1 HL0 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO. pose proof ECZ as (_ & _ & ED).
destruct PK as [P256|(c & Hc & Rc & Hrem)].
- cfeed P (PMBOUP1.uboT3e_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383c4 R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 1 T1); [regs_from KS1 R R1| exact T10| exact T11| exact SV| exact MO| exact W| lia| exact ED].
- destruct (Z.eq_dec c 35) as [->|N35].
+ cfeed P (PMBOUP1.uboT3h_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383c4 R1 0x37144 M K Mh Ml MS1).
assert (RA1 : regs_at R1) by regs_from KS1 R R1.
unfold PMPSU.ignore_spec, PMPS.ignore_spec in IGN. cbn [pa_ignore AD PmLayoutU.ADDR_U] in IGN.
apply (src_call _ 4 _ _ _ IGN fx1 R1 M model s1 sm e cr 0x383ec [] T1 ltac:(split; [lia| reflexivity]) RA1); [replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| exact T11| reflexivity| intros a I; destruct (PMFR.inW_nil a I)| exact SV| exact MO| exact W|].
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
destruct RES2 as (_ & C1). specialize (C1 Hrem). unfold PMSP.consumed in C1.
apply (arm_t4 GL MKE OPN OPD fx2 R2' M2 model (PMPS.with_src s1 src2) sm2 e cr tb RA2); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
* rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact R20.
* apply (L5C.u8_at_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact TBY].
* apply (PMBK.ec_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact ECZ].
* cbn [PMPS.with_src PM.p_src]. lia.
+ pose proof (Z_le_gt_dec c 34) as [LE|GT].
* cfeed P (PMBOUP1.uboT3l_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 39%nat => c | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383c4 R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 3 T1); [regs_from KS1 R R1| exact T10| exact T11| exact SV| exact MO| exact W| lia| exact ED].
* cfeed P (PMBOUP1.uboT3u_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 39%nat => c | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383c4 R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 3 T1); [regs_from KS1 R R1| exact T10| exact T11| exact SV| exact MO| exact W| lia| exact ED].
Qed.
Lemma arm_t2 : ltac2:(TCodec.tc2 tcn__PmBoU9 "U>&Q:vQGv=v:%43321&Q9%13543&Q>%13765&Q?%13987&QA%13;:9&Q@%13=<;'QB&@y5'R?yR0%211%5241'3y8%611%311p061'?'Q4'Q7'0&I'8&NvHvQFvR6r8%544321'5&QCr9&R>&QLuC%211%42M1%7261&QI+R0%22>1%92Q01%=3Q051r:uD%<11%>2Q71%A241+1%A2Q81%E3Q831r;u:%D11%F2Q?1%I241r4%I2Q@1%M3Q@31'7r5z%Q13Q821%Q23Q93?%5221r6%Q53Q<1B&Jr=&QN+S1%22Q>1%5341Hp071&O%13QCQB7&MvBv>r>%46RH32QGQF1&Q0vR9vR2vR:vRAvR=vR5r?r<%9@S2S18<7R065432;F1Q7Q?&Q=&QEr@+8%QI2R51vR0%65542Q41&Q1%12QC;'2'Q5%211&Q3%11;%21E%R=3421&QJ&1%1284%R=11+QP0%5221&QK&Q8&Q2rB%211rA%5221%51Q4%721Q3%9231'QD&L%11T6&Q<rGrF+WPmHrErD%66Q854321v<%;4Q:921p0=1p0H1p0O1p0Q71p0Q:1p0QB1p0QM1p0R31p0R61p0R@1p0RG1p0S01p0S91p0SH1pT8SO1pT4T11pT:T31pTJT51pTHT71pTBT91pQ4T;1pQ@TA1pT@TH1pQ:TJ1pQ<TM1pQ8U01pDU31pHU61pQ>U91").
Proof. intros PEEK IGN GL MKE OPN OPD fx R M model s1 sm e cr d.
intros RA R19 R20 R10 Hd DD SV MO W ECZ IV1 ES1 HL0 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO. pose proof ECZ as (_ & _ & ED).
destruct Hd as [->| ->].
- cfeed P (PMBOUP1.uboT2z_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383b8 R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 1 T1); [regs_from KS1 R R1| exact T10| exact T11| exact SV| exact MO| exact W| lia| exact ED].
- destruct (PMCG.u8_of_defined RSEGS M (S - 97) ltac:(lia) ltac:(lia) (DD eq_refl)) as (tb & Htb & TBY).
cfeed P (PMBOUP1.uboT2p_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383b8 R1 0x37050 M K Mh Ml MS1).
assert (RA1 : regs_at R1) by regs_from KS1 R R1.
unfold PMPSU.peek_spec, PMPS.peek_spec in PEEK. cbn [pa_peek AD PmLayoutU.ADDR_U] in PEEK.
apply (src_call _ 4 _ _ _ PEEK fx1 R1 M model s1 sm e cr 0x383c4 [] T1 ltac:(split; [lia| reflexivity]) RA1); [replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| exact I| reflexivity| intros a I; destruct (PMFR.inW_nil a I)| exact SV| exact MO| exact W|].
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
destruct RES2 as (C0 & RES2). unfold PMSP.consumed in C0.
apply (arm_t3 IGN GL MKE OPN OPD fx2 R2' M2 model (PMPS.with_src s1 src2) sm2 e cr tb RA2); try assumption.
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
+ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact R20.
+ apply (L5C.u8_at_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact TBY].
+ apply (PMBK.ec_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact ECZ].
+ cbn [PMPS.with_src PM.p_src]. lia.
Qed.
Lemma arm_t1 : ltac2:(TCodec.tc2 tcn__PmBoU9 "TF&Q:vQGv=v:%43321&Q9%13543&Q;%13765&Q>%13987&Q?%13;:9&QA%13=<;&Q@%13?>='QB&@y5'R?yR0%211%5241'3y8%611%311p061'?'Q4'Q7'0&I&NvHvQFvR6r7%544321'5&QCr8&R>&QLuC%211%42L1%7261&QI+R0%22>1%92O1%=3O51r9uD%<11%>2Q61%A241+1%A2Q71%E3Q731&O%13LK9&MvBv>r:%46R232Q0O1&Q0vR9vR2vR:vRAvR=vR5r;r6%9@R<R;8<7Q965432;HQ4Q81&Q=&QEr<+8%Q22Q>1zvR0%7565321&Q1%12M<'2'Q5%211&Q3%11<%21F%QG3421&QJ&1%1284%QG11+QP0%5221&QK&Q8&Q2r>%211r=%5221%51Q5%721Q4%9231'QD&L%11SA&Q<rCrB+WPm8rAr@%66Q954321v<%;4Q;921p0=1p0H1p0O1p0Q71p0Q:1p0QC1p0QN1p0R41p0R71p0R@1p0RO1pT4S61pT:S81pTJS:1pTHS<1pTBS>1pQ4S@1pQ@SF1pT@SM1pQ:SO1pQ<T21pQ8T51pDT81pSBT;1pHT>1pQ>TA1").
Proof. intros PEEK IGN SRD GL MKE OPN OPD fx R M model s1 sm e cr.
intros RA R19 R20 SV MO W ECZ IV1 ES1 HL0 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
cfeed P (PMBOUP1.uboT1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11 & T12).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383a8 R1 0x374b8 M K Mh Ml MS1).
assert (RA1 : regs_at R1) by regs_from KS1 R R1.
pose proof STK as (_ & _ & _ & _ & SDEF). unfold PMBOUS.SCR in SDEF.
unfold PMPSU.src_read_spec, PMPS.src_read_spec in SRD. cbn [pa_src_read AD PmLayoutU.ADDR_U] in SRD.
apply (src_call _ 4 _ _ _ SRD fx1 R1 M model s1 sm e cr 0x383b8 [(S - 97, 1)] T1 ltac:(split; [lia| reflexivity]) RA1);
[replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| | | | exact SV| exact MO| exact W|].
{ unfold PMPS.read_args. exists (S - 97), 1. rewrite L5K.rl11, L5K.rl12. split; [exact T11|]. split; [exact T12|]. split; [unfold PM.CHUNK; lia|].
unfold PMPS.read_dst. left. split; [lia|]. split; [lia|]. split; [lia|]. apply (L5.defined_sub M (S - 26624) 26624); [exact SDEF|lia|lia]. }
{ unfold PMPS.read_W. exists (S - 97), 1. rewrite L5K.rl11, L5K.rl12. split; [exact T11|]. split; [exact T12|]. split; [lia|]. split; [lia| reflexivity]. }
{ intros a I. apply PMFR.inW_inv1 in I. lia. }
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
unfold PMPS.read_res, PMSP.consumed in RES2. destruct RES2 as (p' & k' & d' & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & DEF' & _).
assert (pk : p' = S - 97 /\ k' = 1).
{ change (getr R1 (PMK.reg 11) = Z_to_bv 64 p') in Y11. change (getr R1 (PMK.reg 12) = Z_to_bv 64 k') in Y12.
rewrite T11 in Y11. rewrite T12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
destruct pk as (-> & ->).
apply (arm_t2 PEEK IGN GL MKE OPN OPD fx2 R2' M2 model (PMPS.with_src s1 src2) sm2 e cr d' RA2); try assumption.
- rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
- rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact R20.
- lia.
- intros ->. exact DEF'.
- apply (PMBK.ec_agree RSEGS M M2); [apply AGH; [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia]|lia|lia| exact ECZ].
- cbn [PMPS.with_src PM.p_src]. lia.
Qed.
End Call.
End WithHeap.
End PMBOU9.
