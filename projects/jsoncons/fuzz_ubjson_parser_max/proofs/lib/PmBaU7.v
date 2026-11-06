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
PmCertKitG PmBaKit PmBaUStmts PmBaU1 PmBaU2 PmBaU3 PmBaU4 PmBaU5 PmBaU6 PmBaU6Gc PmBaU6Gt PmBaU6C PmBaU6Cc PmBaU6Ct PmBaUP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBaU7 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaUStmts.PMBAUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1option"; "1true"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M0"; "0MKE"]; ["0OPD"; "0OPN"; "0R"; "0R0"; "6credit"; "8u8_at"; "7SCFG"; "9mem_ok"; "9regs_at"; "9saves"; "9world"; ":pa_errcat_obj"; ";ADDR_U"; "<inv_d"; "<p_depth"; "<p_more"]; ["<p_src"; "<p_stk"; "<pst"; "<pstate"; "<strm"; "<unread"; "=cfg"; "=ec_at"; ">make_ec_spec"; ">opdel_spec"; ">opnew_spec"; "?FPState"; "?getr"; "@srealizes"; "Aloaded_segments"; "0S"]; ["0SCFG_P"; "Badd"; "Ble"; "Blt"; "Bof_nat"; "Bpow"; "Bsub"; "0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"; "0fx"; "0len"; "0model"]; ["0model0"; "0s0"; "0s1"; "0sm"; "0sm0"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0str"; "0tb"; "0v"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBAU7.
Import PMU.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBAU2.push_st.
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
Hypothesis PRE : PMBAUS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBAUS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBAUS.kept0 R0).
Local Abbreviation regs_at := (PMBAUS.regs_at R0 S fb).
Local Abbreviation saves := (PMBAUS.saves R0 S).
Local Abbreviation mem_ok := (PMBAUS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBAUS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBAUS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBAU1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBAU1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBAU1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBAU1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBAU1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBAU1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBAU1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBAU1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBAU2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBAU2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBAU2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBaU7 "B'R6yR0%211'4&QBz&R7r1%2271%5241&QC&QE+2+R0%3221%5271%=271pTH?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBAUP1.aligned; first [assumption | lia]].
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
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBAUS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBAU1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBAU1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBAU1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBAU1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBAU1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBAU1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBAU1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_del := PMBAU4.grow_del L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let CRED0 := PMBAU1.CRED0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rgp0 := PMBAU1.Rgp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let call_keep0 := PMBAU4.call_keep0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_objs := PMBAU5.keep_objs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_facts := PMBAU5.push_facts L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let errp := PMBAU1.errp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_fast_c := PMBAU3.push_fast_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_fast_t := PMBAU3.push_fast_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cap_c := PMBAU6Cc.grow_cap_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cap_t := PMBAU6Ct.grow_cap_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Abbreviation gstate := (PMBAU5.gstate L HI model0 LBX fb s0 str sm0 e0).
Local Abbreviation pushok := (PMBAU5.pushok s0 sm0).
Lemma gl_err_c : ltac2:(TCodec.tc2 tcn__PmBaU7 "S:'Q;&<y5'R6yR0%211%5241'2y8%611%311p061';'Q2'Q4&D'6&HvCvQ?vQLr7%544321'5&Q<r8&R5&QDuC%211%42L1%7261&QA+R0%22>1%92O1%=3O51&I%13DC=&Gv9v>v:r9%56432IH1&Jv7vR0vQIvR1vR8vR4vQKr:(3r6%;@@:9>8Q476543=OQ321'4&QB+1%2215%326L%5221&Q7&Q>r<+8%Q32Q?1&K&L%211%85764QB1&Or;%211z%QE3QL21'Q=&FvQ@%211&Q6r@r?+VomLr>r=%66G54321v8%<4I921p0>1p0D1p0N1p0Q51p0QB1p0QI1p0QL1p0R;1pTFRB1pSBRD1pT8RF1pT6RH1pT0RJ1pLRL1pQ6S21pSLS91").
Proof. intros fx R M model s1 sm cr v.
intros RA R19 SV MO W Hv ECV HM. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56). pose proof ECV as (EV0 & _).
assert (R10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
cfeed P (PMBAUP1.ubaCe_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 48%nat => bv_unsigned (getr R (reg 10)) | 49%nat => v
| 40%nat => bv_unsigned (getr R0 (reg 1)) | 41%nat => bv_unsigned (getr R0 (reg 8)) | 42%nat => bv_unsigned (getr R0 (reg 9))
| 43%nat => bv_unsigned (getr R0 (reg 18)) | 44%nat => bv_unsigned (getr R0 (reg 19)) | 45%nat => bv_unsigned (getr R0 (reg 20))
| 46%nat => bv_unsigned (getr R0 (reg 21)) | 47%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T2 & T8 & T9 & _ & T18 & T19 & T20 & T21).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37fbc R1 0x382e8 M K Mh Ml MS1).
apply (fin fx1 R1 M model s1 sm true cr); try assumption.
- apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- left. exists v. split; [exact Hv|]. split; [exact ECV|]. split; [exact HM| reflexivity].
Qed.
Lemma gl_err_t : ltac2:(TCodec.tc2 tcn__PmBaU7 "SA'Q;&<y5'R6yR0%211%5241'2y8%611%311p061';'Q2'Q4&D'6&HvCvQ?vQLr7%544321'5&Q<r8&R5&QDuC%211%42L1%7261&QA+R0%22>1%92O1%=3O51r9uD%<11%>2Q61%A241+1%A2Q71%E3Q731&I%13LK9&Gv9v>v:r:%56432Q1Q01&Jv7vR0vQIvR1vR8vR4vQKr;(3%:@?98=7Q;65432<JQ61Q:'4&QB%12HQ=%22Q>Q2%4221&Q7&Q>r=+8%Q92QE1&K&L%211%85764QD1&Or<%211z%QK3R221'Q=&FvQ@%211&Q6rAr@+VojDr?r>%66G54321v8%<4I921p0>1p0D1p0N1p0Q41p0Q@1p0QG1p0QJ1p0R31p0RB1pTFRI1pSBRK1pT8RM1pT6RO1pT0S11pLS31pQ6S91pSLS@1").
Proof. intros fx R M model s1 sm cr v.
intros RA R19 R20 SV MO W Hv ECV HM. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56). pose proof ECV as (EV0 & _).
assert (R10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
cfeed P (PMBAUP1.ubaTe_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 48%nat => bv_unsigned (getr R (reg 10)) | 49%nat => v
| 40%nat => bv_unsigned (getr R0 (reg 1)) | 41%nat => bv_unsigned (getr R0 (reg 8)) | 42%nat => bv_unsigned (getr R0 (reg 9))
| 43%nat => bv_unsigned (getr R0 (reg 18)) | 44%nat => bv_unsigned (getr R0 (reg 19)) | 45%nat => bv_unsigned (getr R0 (reg 20))
| 46%nat => bv_unsigned (getr R0 (reg 21)) | 47%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T2 & T8 & T9 & _ & T18 & T19 & T20 & T21).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37f54 R1 0x382e8 M K Mh Ml MS1).
apply (fin fx1 R1 M model s1 sm true cr); try assumption.
- apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- left. exists v. split; [exact Hv|]. split; [exact ECV|]. split; [exact HM| reflexivity].
Qed.
Lemma gl_ok_c : ltac2:(TCodec.tc2 tcn__PmBaU7 "TE&Q8vQ@v9v7%43321&Q:%13543&Q9%13765'Q;&<y5'R6yR0%211%5241'2y8%611%311p061';'Q2'Q4'0&D'6&HvCvQ?vQLr8%544321'5&Q<r9&R5&QDuC%211%42M1%7261&QA+R0%22>1%92Q01%=3Q051r:u:%<11%>2Q71%A241r3%A2Q81%E3Q831'4&QBzr4%3221&QC&QE+2%221D%4261%:261&Ir;%23Q8Q71&Gv>v:r<%46R732Q<Q;1&JvR0vQIvR1vR8vR4vQKr=%8@R@R?7;6QD54321:?Q3Q?QC&Q7&Q>r>+8%Q=2QI1vQG%65542Q01&M+1%221;&N%119+QP0%Q8221'1'Q3%211&Q1r?%211%31J%R73521&Q5&Q0r@%211%4218%41Q1%621Q0%QD231'Q=&F%11SB&Q6rErD+VomLrCrB%66Q654321v8%;4Q8921p0=1p0F1p0O1p0Q41p0Q81p0Q@1p0QJ1p0R01p0R41p0R@1p0RI1p0S81pSNS?1pSBSA1pSFSC1pT8SE1pT6SG1pT0SI1pLSK1pQ6T11pSLT81pQ2T:1pQ4T=1pQ0T@1").
Proof. intros MKE OPN OPD fx R M model s1 sm e cr len.
intros RA R19 R10 HLn SV MO W ECZ IV1 HD1 ES1 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
destruct (Z_le_gt_dec len 16777216) as [LE|GT].
- pose proof W as ((PA & _) & _). unfold PMSP.o_p, PMSP.o_is in PA. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (_ & _ & _ & Hk & Hlen & _).
pose proof IV1 as (_ & _ & IDP & _).
destruct (Z_lt_le_dec (Z.of_nat (length (PM.p_stk s1))) (2 ^ PM.p_k s1)) as [NF|FU].
+ apply (push_fast_c fx R M model s1 sm e cr len RA R19 R10 ltac:(lia) UNR SV MO W ECZ IV1 HD1 ES1 NF).
+ assert (Hk10 : PM.p_k s1 <= 10).
{ destruct (Z_le_gt_dec (PM.p_k s1) 10) as [X|X]; [exact X|exfalso].
assert (2 ^ 11 <= 2 ^ PM.p_k s1) by (apply Z.pow_le_mono_r; lia). lia. }
apply (grow_cap_c fx R M model s1 sm e cr len RA R19 R10 ltac:(lia) SV MO W ECZ); [|exact OPN| exact OPD].
split; [exact IV1|]. split; [exact HD1|]. split; [exact ES1|]. split; [lia|]. split; [lia|].
split. { unfold PM.pstate_ok. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; lia|]. unfold PM.MAX_ITEMS. lia. }
split; [unfold PM.mode_bottom; cbn; lia|]. split; [reflexivity|]. intros _. exact UNR.
- prep_ctx M W MO. pose proof ECZ as (EC0 & _).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _). unfold PM.MAX_ITEMS in P328.
cfeed P (PMBAUP1.ubaCx_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11 & T19).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37fbc R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 13 T1); [| exact T10| exact T11| exact SV| exact MO| exact W| lia| pose proof ECZ as (_ & _ & ED); exact ED].
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
Lemma gl_ok_t : ltac2:(TCodec.tc2 tcn__PmBaU7 "U<&Q8vQ@v9v7%43321&Q:%13543&Q9%13765'Q;&<y5'R6yR0%211%5241'2y8%611%311p061';'Q2'Q4'0&D'6&HvCvQ?vQLr9%544321'5&Q<r:&R5&QDuC%211%42M1%7261&QA+R0%22>1%92Q01%=3Q051r;uD%<11%>2Q71%A241+1%A2Q81%E3Q831r<u:%D11%F2Q?1%I241r5%I2Q@1%M3Q@31'4&QBzr6%3221&QC&QE+2%221L%4261%:261&E&Q>r=&QF+S1%22QB1%64541>r7%B2A1+X0%@231%F231&Ir?%23QLQK1&Gv>v:r@%46RK32R0QO1&JvR0vQIvR1vR8vR4vQKrAr>%9@S5S48<7R965432;@1KQ@&Q7rB+8%R12R=1vQG%55Q242Q<1&M%12QK:&N%118+QP0%QC221'1'Q3%211&Q1rC%211%31I%RJ3521&Q5&Q0rD%211%4218%41Q0%621O%QO231'Q=&F%11T5&Q6rIrH+VojDrGrF%66R254321v8%;4R4921p0=1p0F1p0O1p0Q41p0Q71p0Q>1p0QI1p0QO1p0R31p0R91p0RA1p0RM1p0S61p0S?1p0SN1pTDT51pSNT61pSBT81pSFT:1pT8T<1pT6T>1pT0T@1pLTB1pQ6TH1pSLTO1pQ2U11pQ4U41pQ0U71").
Proof. intros MKE OPN OPD fx R M model s1 sm e cr len tb.
intros RA R19 R20 R10 HLn TBY Htb SV MO W ECZ IV1 HD1 ES1 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
destruct (Z_le_gt_dec len 16777216) as [LE|GT].
- pose proof W as ((PA & _) & _). unfold PMSP.o_p, PMSP.o_is in PA. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (_ & _ & _ & Hk & Hlen & _).
pose proof IV1 as (_ & _ & IDP & _).
destruct (Z_lt_le_dec (Z.of_nat (length (PM.p_stk s1))) (2 ^ PM.p_k s1)) as [NF|FU].
+ apply (push_fast_t fx R M model s1 sm e cr len tb RA R19 R20 R10 ltac:(lia) TBY Htb UNR SV MO W ECZ IV1 HD1 ES1 NF).
+ assert (Hk10 : PM.p_k s1 <= 10).
{ destruct (Z_le_gt_dec (PM.p_k s1) 10) as [X|X]; [exact X|exfalso].
assert (2 ^ 11 <= 2 ^ PM.p_k s1) by (apply Z.pow_le_mono_r; lia). lia. }
apply (grow_cap_t fx R M model s1 sm e cr len tb RA R19 R20 R10 ltac:(lia) TBY Htb SV MO W ECZ); [|exact OPN| exact OPD].
split; [exact IV1|]. split; [exact HD1|]. split; [exact ES1|]. split; [lia|]. split; [lia|].
split. { unfold PM.pstate_ok. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [lia|]. left. split; [unfold PM.mode_counted; lia|]. unfold PM.MAX_ITEMS. lia. }
split; [unfold PM.mode_bottom; cbn; lia|]. split; [reflexivity|]. intros _. exact UNR.
- prep_ctx M W MO. pose proof ECZ as (EC0 & _).
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P328 & _). unfold PM.MAX_ITEMS in P328.
cfeed P (PMBAUP1.ubaTx_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 48%nat => len | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11 & T19).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37f54 R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 13 T1); [| exact T10| exact T11| exact SV| exact MO| exact W| lia| pose proof ECZ as (_ & _ & ED); exact ED].
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
End Call.
End WithHeap.
End PMBAU7.
