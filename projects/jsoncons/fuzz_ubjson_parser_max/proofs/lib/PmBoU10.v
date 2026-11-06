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
PmCertKitG PmBaKit PmBoUStmts PmBoU1 PmBoU2 PmBoU3 PmBoU5 PmBoU6 PmBoU6Gc PmBoU6Gt PmBoU6C PmBoU6Cc PmBoU6Ct PmBoU8 PmBoU9 PmBoUP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU10 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1length"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0GL"; "0HI"; "0IGN"; "0K"]; ["0L"; "0LBX"; "4Model"; "4m_vmmaps"; "5bvmap"; "0M"; "0M0"; "0M1"; "0MKE"; "0OPD"; "0OPN"; "0PEEK"; "0R"; "0R0"; "6credit"; "6hi_heap"]; ["8u32_at"; "7SCFG"; "9mem_ok"; "9regs_at"; "9saves"; "9sd"; "9world"; ":MAX_DEPTH"; ":inv_d"; ":p_depth"; ":p_src"; ":p_stk"; ":parser_own"; ":pst"; ":pstate"; ":sr_rem"]; [":strm"; ";ignore_spec"; ";peek_spec"; ";src_read_spec"; "<cfg"; "<ec_at"; "=get_length_spec"; "=make_ec_spec"; "=opdel_spec"; "=opnew_spec"; ">FPState"; ">getr"; "?srealizes"; "@mem_grows"; "Aloaded_segments"; "0S"]; ["0SCFG_P"; "0SRD"; "Badd"; "Ble"; "Blt"; "Bof_nat"; "Bpow"; "Bsub"; "0c"; "0cat"; "0cr"; "0cr0"; "0d1"; "0e"; "0e0"; "0fb"]; ["0fx"; "0i"; "0model"; "0model0"; "0s0"; "0s1"; "0sm"; "0sm0"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0str"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU10.
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
Local Abbreviation pushok := (PMBOU5.pushok s0 sm0).
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
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU10 "B'RIyR0%211'6&R3z&RJr1%2271%5241&R4&R6+2+R0%3221%5271%=271pUJ?1").
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
Let errp0 := PMBOU1.errp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let src_call := PMBOU1.src_call L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let arm_c1 := PMBOU8.arm_c1 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let arm_t1 := PMBOU9.arm_t1 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_fast_i := PMBOU3.push_fast_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cap_i := PMBOU6C.grow_cap_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let HH0 := PMBOU1.HH0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let STK0 := PMBOU1.STK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rra0 := PMBOU1.Rra0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rsp0 := PMBOU1.Rsp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ARGS := PMBOU1.ARGS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let RPRE0 := PMBOU1.RPRE0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let EC0 := PMBOU1.EC0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
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
Lemma arm_ind : ltac2:(TCodec.tc2 tcn__PmBoU10 "SE&QIvR0v@v=%43321&QH%13543'QJ&Dy5'RIyR0%211%5241'4y8%611%311p061'B'Q='Q@'1&N&Q3vMvQOvR?r7%544321'7&QKr8&RH&R5uC%211%42L1%7261&R2+R0%22>1%92O1%=3O51&Q4%13DC=&Q2vFvAr9%46Q@32HG1&Q6vRCvR;vRDvRKvRGvR>r:r6r5%:@QKQJ9=8Q276543<MQ121&QE&QNr;+8%K2Q71zvR9%7565321&Q8+1%221>'3'Q>%211&Q;%11=%21H%QA3421&R3&2%1284%QA11+QP0%5221'QL&Q1%11RG&QDrAr@+WQU4r?r>%66Q054321v?%;4Q2921p0=1p0D1p0L1p0Q01p0Q91p0QE1p0QK1p0QN1p0R=1pTFRD1pTLRF1pU>RH1pU<RJ1pU6RL1pQ<RN1pQJS41pU2S;1pQDS=1pQFS@1").
Proof. intros OPN OPD fx R M model s1 sm e cr.
intros RA R19 SV MO W ECZ IV1 ES1 HL0.
pose proof W as ((PA & _) & _). unfold PMSP.o_p, PMSP.o_is in PA. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (_ & _ & _ & Hk & Hlen & _).
pose proof IV1 as (_ & _ & IDP & _).
assert (HD1 : PM.p_depth s1 <= 1024) by (rewrite ES1 in IDP; lia).
destruct (Z_lt_le_dec (Z.of_nat (length (PM.p_stk s1))) (2 ^ PM.p_k s1)) as [NF|FU].
- exact (push_fast_i fx R M model s1 sm e cr RA R19 SV MO W ECZ IV1 HD1 ES1 NF).
- assert (Hk10 : PM.p_k s1 <= 10).
{ destruct (Z_le_gt_dec (PM.p_k s1) 10) as [X|X]; [exact X|exfalso].
assert (2 ^ 11 <= 2 ^ PM.p_k s1) by (apply Z.pow_le_mono_r; lia). rewrite ES1 in Hlen, FU. lia. }
apply (grow_cap_i fx R M model s1 sm e cr RA R19 SV MO W ECZ); [|exact OPN| exact OPD].
split; [exact IV1|]. split; [exact HD1|]. split; [exact ES1|]. split; [lia|]. split; [lia|].
split. { unfold PM.pstate_ok. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [lia|]. right; left. split; [unfold PM.mode_indef; lia|]. split; [reflexivity|]. unfold PM.MAX_ITEMS. lia. }
split; [unfold PM.mode_bottom; cbn; lia|]. split; [reflexivity|]. unfold PM.mode_counted. cbn. lia.
Qed.
Lemma arm_k2 : ltac2:(TCodec.tc2 tcn__PmBoU10 "U2&QBvR0v@v=%43321&QA%13543&QC%13765&QF%13987&QG%13;:9&QI%13=<;&QH%13?>='QJ&Dy5'RIyR0%211%5241'4y8%611%311p061'B'Q='Q@'1&N&Q3vMvQOvR?r7%544321'7&QKr8&RH&R5uC%211%42L1%7261&R2+R0%22>1%92O1%=3O51':r9u:%=11%?2Q71%B241+X0%B2Q81%F3Q831'8';'6&R3zr1%3221&R4%123;%7231r:%Q121@%Q02QF7%Q43QF21+1&Q?&Q:%11Q:%311%@251%B271%C2<1qTBE1%G2F1%Q12I1&Q4%13QFQEQ2&Q2vFvA%36RK21QIQHD&Q6vRCvR;vRDvRKvRGvR>r;r6%9@S5S48;7R265432NQ@QMR11&QE&QNr<+8%QK2R71vR9%65542Q;1&Q8%12Q3;'3'Q>%211&Q;%11;%21E%R?3421&2%1273%R>11+QP0%QJ221'QL&Q1%11SN&QDrBrA+WQR@r@r?%66M54321v?%;4O921p0=1p0C1p0K1p0N1p0Q61p0QA1p0QF1p0QI1p0RL1p0S;1pTFSB1pTLSD1pU>SF1pU<SH1pU6SJ1pQ<SL1pQJT21pU2T91pQDT;1pQFT>1pQBTA1pJTD1pT4TG1pNTJ1pQHTM1").
Proof. intros PEEK IGN SRD GL MKE OPN OPD fx R M model s1 sm e cr.
intros RA R19 PK SV MO W ECZ IV1 ES1 HL0. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO. pose proof ECZ as (_ & _ & ED).
destruct PK as [P256|(c & Hc & Rc & Hrem)].
- cfeed P (PMBOUP1.uboK2e_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x38450 R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 1 T1); [regs_from KS1 R R1| exact T10| exact T11| exact SV| exact MO| exact W| lia| exact ED].
- destruct (Z.eq_dec c 35) as [->|N35].
+ cfeed P (PMBOUP1.uboK2h_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x38450 R1 0x37144 M K Mh Ml MS1).
assert (RA1 : regs_at R1) by regs_from KS1 R R1.
unfold PMPSU.ignore_spec, PMPS.ignore_spec in IGN. cbn [pa_ignore AD PmLayoutU.ADDR_U] in IGN.
apply (src_call _ 4 _ _ _ IGN fx1 R1 M model s1 sm e cr 0x38478 [] T1 ltac:(split; [lia| reflexivity]) RA1); [replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| exact T11| reflexivity| intros a I; destruct (PMFR.inW_nil a I)| exact SV| exact MO| exact W|].
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
destruct RES2 as (_ & C1). specialize (C1 Hrem). unfold PMSP.consumed in C1.
pose proof STEP as (_ & _ & _ & _ & U0).
apply (arm_c1 GL MKE OPN OPD fx2 R2' M2 model (PMPS.with_src s1 src2) sm2 e cr RA2); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
* apply (PMBK.ec_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact ECZ].
* cbn [PMPS.with_src PM.p_src]. lia.
+ assert (KLU : exists fx1 R1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x38450) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x384a4) M (seg_rom RSEGS))
/\ forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)).
{ destruct (Z_le_gt_dec c 34) as [LE|GT].
- cfeed P (PMBOUP1.uboK2l_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 39%nat => c | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
exists fx1, R1. split; [exact MS1|]. intros x Hx. apply KS1. revert x Hx. apply PMPK.sub_in. vm_compute. reflexivity.
- cfeed P (PMBOUP1.uboK2u_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 39%nat => c | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
exists fx1, R1. split; [exact MS1|]. intros x Hx. apply KS1. revert x Hx. apply PMPK.sub_in. vm_compute. reflexivity. }
destruct KLU as (fx1 & R1 & MS1 & KS1).
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x38450 R1 0x384a4 M K Mh Ml MS1).
apply (arm_ind OPN OPD fx1 R1 M model s1 sm e cr); try assumption.
* regs_from KS1 R R1.
* rewrite (KS1 19%nat) by PMK.inl. exact R19.
Qed.
Lemma arm_k1 : ltac2:(TCodec.tc2 tcn__PmBoU10 "U2&QBvR0v@v=%43321&QA%13543&QC%13765&QF%13987&QG%13;:9&QI%13=<;&QH%13?>='QJ&Dy5'RIyR0%211%5241'4y8%611%311p061'B'Q='Q@'1&N&Q3vMvQOvR?r7%544321'7&QKr8&RH&R5uC%211%42L1%7261&R2+R0%22>1%92O1%=3O51':r9u:%=11%?2Q71%B241+X0%B2Q81%F3Q831'8';'6&R3zr1%3221&R4%123;%7231r:%Q121@%Q02QF7%Q43QF21+1&Q?&Q:%11Q:%311%@251%B271%C2<1qTBE1%G2F1%Q12I1&Q4%13QFQEQ2&Q2vFvA%36RK21QIQHD&Q6vRCvR;vRDvRKvRGvR>r;r6%9@S5S48;7R265432NQ@QMR11&QE&QNr<+8%QK2R71vR9%65542Q;1&Q8%12Q3;'3'Q>%211&Q;%11;%21E%R?3421&2%1273%R>11+QP0%QJ221'QL&Q1%11SN&QDrBrA+WPkLr@r?%66M54321v?%;4O921p0=1p0C1p0K1p0N1p0Q61p0QA1p0QF1p0QI1p0RL1p0S;1pTFSB1pTLSD1pU>SF1pU<SH1pU6SJ1pQ<SL1pQJT21pU2T91pQDT;1pQFT>1pQBTA1pJTD1pT4TG1pNTJ1pQHTM1").
Proof. intros PEEK IGN SRD GL MKE OPN OPD fx R M model s1 sm e cr.
intros RA R19 PK SV MO W ECZ IV1 ES1 HL0. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO. pose proof ECZ as (_ & _ & ED).
destruct PK as [P256|(c & Hc & Rc & Hrem)].
- cfeed P (PMBOUP1.uboKe_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3837c R1 0x370ac M K Mh Ml MS1).
apply (errp MKE fx1 R1 M model s1 sm e cr 1 T1); [regs_from KS1 R R1| exact T10| exact T11| exact SV| exact MO| exact W| lia| exact ED].
- destruct (Z.eq_dec c 36) as [->|N36].
+ cfeed P (PMBOUP1.uboKd_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11 & T20).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3837c R1 0x37144 M K Mh Ml MS1).
assert (RA1 : regs_at R1) by regs_from KS1 R R1.
unfold PMPSU.ignore_spec, PMPS.ignore_spec in IGN. cbn [pa_ignore AD PmLayoutU.ADDR_U] in IGN.
apply (src_call _ 4 _ _ _ IGN fx1 R1 M model s1 sm e cr 0x383a8 [] T1 ltac:(split; [lia| reflexivity]) RA1); [replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| exact T11| reflexivity| intros a I; destruct (PMFR.inW_nil a I)| exact SV| exact MO| exact W|].
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
destruct RES2 as (_ & C1). specialize (C1 Hrem). unfold PMSP.consumed in C1.
pose proof STEP as (_ & _ & _ & _ & U0).
apply (arm_t1 PEEK IGN SRD GL MKE OPN OPD fx2 R2' M2 model (PMPS.with_src s1 src2) sm2 e cr RA2); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
* rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. exact T20.
* apply (PMBK.ec_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact ECZ].
* cbn [PMPS.with_src PM.p_src]. lia.
+ assert (KLU : exists fx1 R1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x3837c) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x37050) M (seg_rom RSEGS))
/\ getr R1 (reg 1) = Z_to_bv 64 0x38450 /\ getr R1 (reg 10) = Z_to_bv 64 (fb + 40 + 24)
/\ forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)).
{ destruct (Z_le_gt_dec c 35) as [LE|GT].
- cfeed P (PMBOUP1.uboKl_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 39%nat => c | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
exists fx1, R1. split; [exact MS1|]. split; [exact T1|]. split; [exact T10|]. intros x Hx. apply KS1. revert x Hx. apply PMPK.sub_in. vm_compute. reflexivity.
- cfeed P (PMBOUP1.uboKu_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 39%nat => c | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
exists fx1, R1. split; [exact MS1|]. split; [exact T1|]. split; [exact T10|]. intros x Hx. apply KS1. revert x Hx. apply PMPK.sub_in. vm_compute. reflexivity. }
destruct KLU as (fx1 & R1 & MS1 & T1 & T10 & KS1).
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3837c R1 0x37050 M K Mh Ml MS1).
assert (RA1 : regs_at R1) by regs_from KS1 R R1.
unfold PMPSU.peek_spec, PMPS.peek_spec in PEEK. cbn [pa_peek AD PmLayoutU.ADDR_U] in PEEK.
apply (src_call _ 4 _ _ _ PEEK fx1 R1 M model s1 sm e cr 0x38450 [] T1 ltac:(split; [lia| reflexivity]) RA1); [replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| exact I| reflexivity| intros a I; destruct (PMFR.inW_nil a I)| exact SV| exact MO| exact W|].
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
destruct RES2 as (_ & RES2).
apply (arm_k2 PEEK IGN SRD GL MKE OPN OPD fx2 R2' M2 model (PMPS.with_src s1 src2) sm2 e cr RA2); try assumption.
* rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19.
* apply (PMBK.ec_agree RSEGS M M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact ECZ].
Qed.
Lemma world0 : ltac2:(TCodec.tc2 tcn__PmBoU10 "=&Q6v@v=vRCvAvR;vR?vRDvRKvRGvR>vF%<@;:98765432195327").
Proof.
split; [exact RPRE0|]. split; [exact HH0|]. split; [apply L5C.model_but_vm_refl|].
split; [unfold PMSP.src_step; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|].
split; [intros X; exact X|]. unfold PMSP.credit_keep. lia.
Qed.
Lemma mem_ok0 : ltac2:(TCodec.tc2 tcn__PmBoU10 "7&Q2v@vFvAvQOvR?%66543214").
Proof. split; [apply PMK.ek_refl|]. split; [apply PMK.dk_refl| exact STK0]. Qed.
Lemma pro_world : ltac2:(TCodec.tc2 tcn__PmBoU10 "SF'RIyR0%211'4y8%511%311p051';&QMvFr2%3221'6&R3zr1%3221&R4&R6+2+R0%3221%5271%;271&9&R7vQO+QH%3221%@21C&R2%1234%?2F1%E241%:11vR?+Q8%7221+<%9221r3%L221+4%=241%K241%Q1241%F11'7r7&RHr4%22QC1%411%Q<12%73QA21p091p0F1p0Q21pU4QC1&Ov=&0'5%12QHQH&Q<vRD%211vA%73521vR;&CvRC%211%>5=54G1&Q0&QNr5%3421Q6K&Q9%11>+1%QC221%Q33R;61r6%R72R61&Q7%QH216%R:241%R<241&Q6v@vRKvRGvR>r8&Q5&Q:%11Q0%32Q11%:@9Q7LQ0NR0Q28765L176N&Q2%16;RLQ2R;R27&QE+8%R:2R51vR9%45O<2RL1%RO261%S0291p0E1p0L1p0Q21p0Q71p0QG1p0S71pTJS<1pQ@S>1").
Proof. intros M1 d1.
intros MG FR HH1 C12 Ed Hd.
pose proof world0 as W. pose proof mem_ok0 as MO. prep_ctx M0 W MO.
pose proof PA as (_ & _ & _ & P8 & _ & P12 & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & PB1 & PB2 & PB3).
assert (VIN : In (PM.p_b s0, 32 * 2 ^ PM.p_k s0) (PM.parser_own s0)) by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (own_blk _ cr0 M0 _ _ _ HH VIN) as (BK & V0 & V4). unfold hl_ceil in V4.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 56 \/ S <= a) -> (a + n <= fb + 52 \/ fb + 56 <= a) -> L5C.agree_on M0 M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FR; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PMBOUS.sd s0 (PM.p_src s0))).
{ unfold PMBOUS.sd. rewrite <- Ed.
apply (PMBK.parser_upd RSEGS AD M0 M1 (fb + 40) (fb + 440) s0 (PM.p_more s0) d1 (PM.p_b s0) (PM.p_k s0) (PM.p_stk s0) PA); [lia|lia| | | | | | | | | | | |].
- apply AGo; lia.
- apply AGo; lia.
- apply AGo; lia.
- apply PMPK.dkr_grows. exact MG.
- apply PMPK.dkr_grows. exact MG.
- apply (L5C.u8_at_agree RSEGS M0 M1); [apply AGo; lia|lia|lia| exact P8].
- exact PB1.
- replace (fb + 40 + 12) with (fb + 40 + 12) by lia. exact C12.
- exact Hd.
- apply (PMF.vec_at_agree RSEGS M0 M1); [lia|lia|lia| clear - V4 X3; lia| apply AGo; lia| apply AGo; [lia|clear - V4 X3; lia| clear - V4 X5; lia| clear - V4 X5 F1; lia]| exact PVEC].
- apply PMPK.dkr_grows. exact MG.
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG. }
destruct (keep_step M0 M1 model0 s0 (PMBOUS.sd s0 (PM.p_src s0)) sm0 e0 cr0 0 0 W MO MG) as (W1 & MO1).
{ intros i Hi N. apply FR; [exact Hi| |]; intros X; apply N; unfold PMBOU1.FPB; [left; unfold PMBOUS.SCR; lia| right; left; lia]. }
{ left; reflexivity. } { exact HH1. } { exact PA1. } { exact TB. } { reflexivity. } { exact CK. }
split; [exact W1|]. split; [exact MO1|].
apply (PMBK.ec_agree RSEGS M0 M1); [apply AGo; lia|lia|lia| exact EC0].
Qed.
Lemma entry : ltac2:(TCodec.tc2 tcn__PmBoU10 "Q7&QBvR0v@v=%43321&QA%13543&QC%13765&QF%13987&QG%13;:9&QI%13=<;&QH%13?>='QJ'QL&QN&Q1%11D&QDr1vM+WPi4vFvRC%66954321v?%<4;921pU2>1pQD@1pQFC1pQBF1pJI1pT4L1pNO1pQHQ21").
Proof. intros PEEK IGN SRD GL MKE OPN OPD fx.
pose proof world0 as W. pose proof mem_ok0 as MO. prep_ctx M0 W MO.
pose proof ARGS as (A10 & A11 & A12).
pose proof INV0 as (IM & ID & IDP & ISH & ITB). pose proof ISH as (SH1 & SH2 & _). unfold PM.MAX_DEPTH in SH2.
pose proof PA as (_ & _ & _ & _ & _ & P12 & _ & _ & _ & _ & P320 & _). unfold PM.MAX_DEPTH in P320.
pose proof (bvu (getr R0 (reg 1))) as B1. pose proof (bvu (getr R0 (reg 8))) as B8. pose proof (bvu (getr R0 (reg 9))) as B9.
destruct (Z_le_gt_dec (PM.p_depth s0) 1023) as [LE|GT].
- pose proof (PMBOUP1.uboA0_conc fx R0 M0 (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 33%nat => PM.p_depth s0 | _ => 0 end)) as P.
cbn beta iota in P. rewrite <- Rsp0 in P. PMK.feed P ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T18 & T19 & T21 & C12 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
apply (PMK.spiece RSEGS L HI KL HIok _ cr0 M0 model0 fx fx1 R0 0x38324 R1 0x37050 M1
(fun a => (S - 56 <= a < S - 56 + 56) \/ (fb + 40 + 12 <= a < fb + 40 + 12 + 4)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M0 S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
destruct (pro_world M1 (PM.p_depth s0 + 1) MG1 FRZ1 HH1 C12 eq_refl) as (W1 & MO1 & EC1); [unfold PM.MAX_DEPTH; lia|].
assert (RA1 : regs_at R1).
{ split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T21|].
apply (kept0_of R0 R1 _ KS1); [vm_compute; reflexivity| intros k _; reflexivity]. }
assert (SV1 : saves M1) by (unfold PMBOUS.saves; repeat split; assumption).
unfold PMPSU.peek_spec, PMPS.peek_spec in PEEK. cbn [pa_peek AD PmLayoutU.ADDR_U] in PEEK.
apply (src_call _ 4 _ _ _ PEEK fx1 R1 M1 model0 (PMBOUS.sd s0 (PM.p_src s0)) sm0 e0 cr0 0x3837c [] T1 ltac:(split; [lia| reflexivity]) RA1); [replace (fb + 64) with (fb + 40 + 24) by lia; exact T10| lia| exact I| reflexivity| intros a I; destruct (PMFR.inW_nil a I)| exact SV1| exact MO1| exact W1|].
intros fx2 R2' M2 src2 sm2 RP2 RES2 SV2 MO2 W2 AGH.
assert (RA2 : regs_at R2') by regs_pres RP2 R1 R2'.
destruct RES2 as (_ & RES2).
apply (arm_k1 PEEK IGN SRD GL MKE OPN OPD fx2 R2' M2 model0 (PMPS.with_src (PMBOUS.sd s0 (PM.p_src s0)) src2) sm2 e0 cr0 RA2); try assumption.
+ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. replace (fb + 64) with (fb + 40 + 24) by lia. exact T19.
+ apply (PMBK.ec_agree RSEGS M1 M2); [apply AGH; [lia|lia| intros i _ I; destruct (PMFR.inW_nil i I)]|lia|lia| exact EC1].
+ unfold PM.inv_d, PMPS.with_src, PMBOUS.sd. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [exact IM|]. split; [exact ID|]. split; [lia|]. split; [exact ISH| exact ITB].
+ reflexivity.
+ lia.
- assert (D1024 : PM.p_depth s0 = 1024) by lia.
pose proof (PMBOUP1.uboA1_conc fx R0 M0 (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) as P.
cbn beta iota in P. rewrite <- Rsp0 in P. rewrite D1024 in P12. PMK.feed P ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & _ & T18 & C12 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
apply (PMK.spiece RSEGS L HI KL HIok _ cr0 M0 model0 fx fx1 R0 0x38324 R1 0x370ac M1
(fun a => (S - 56 <= a < S - 56 + 56) \/ (fb + 40 + 12 <= a < fb + 40 + 12 + 4)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Pa. apply (PMK.cwr_stack L _ M0 S SCR a STK). unfold PMBOUS.SCR. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
destruct (pro_world M1 1025 MG1 FRZ1 HH1 C12 ltac:(lia)) as (W1 & MO1 & EC1); [unfold PM.MAX_DEPTH; lia|].
assert (KP1 : kept0 R1) by (apply (kept0_of R0 R1 _ KS1); [vm_compute; reflexivity| intros k _; reflexivity]).
assert (SV1 : saves M1) by (unfold PMBOUS.saves; repeat split; assumption).
pose proof EC1 as (_ & _ & ED1).
apply (errp0 MKE fx1 R1 M1 model0 (PMBOUS.sd s0 (PM.p_src s0)) sm0 e0 cr0 11 T1 T2 T8 T9 T18 KP1 T10 T11 SV1 MO1 W1 ltac:(lia) ED1).
Qed.
End Call.
End WithHeap.
End PMBOU10.
