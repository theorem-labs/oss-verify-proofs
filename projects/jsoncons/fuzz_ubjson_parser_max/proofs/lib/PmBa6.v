(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit
PmCertKitG PmSrcSMemmove PmBaKit PmBaStmts PmBa1 PmBa2 PmBa4 PmBa5 PmBaSP2 PmBaSP3I PmBaSP3C PmBaSP3T.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBa6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBa2.PMBA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBa5.PMBA5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaStmts.PMBAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1option"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"; "0R"]; ["0R'"; "0R0"; "6credit"; "6debit"; "6regs_preserved"; "7agree_on"; "9u64_at"; "9u8_at"; "8SCFG"; ":push_st"; ";gstate"; ";pushok"; "<kept0"; "<mem_ok"; "<saves"; "<world"]; ["=PS"; "=p_k"; "=pot_parser"; "=pst"; "=pstate"; "=strm"; ">cfg"; ">credit_keep"; ">ec_at"; "?opdel_spec"; "?opnew_spec"; "@FPState"; "@getr"; "Asrealizes"; "Bloaded_segments"; "0S"]; ["0SCFG_P"; "Cadd"; "Cle"; "Clt"; "Cmul"; "Cof_nat"; "Cpow"; "Csub"; "0a"; "0c"; "0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"]; ["0fx"; "0fx'"; "0len"; "0model"; "0model'"; "0model0"; "0n"; "0ra_alloc"; "0s0"; "0s1"; "0sm"; "0sm0"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0str"]; ["0tb"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBA6.
Import PMS.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBA2.push_st.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis PRE : PMBAS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBAS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBAS.kept0 R0).
Local Abbreviation regs_at := (PMBAS.regs_at R0 S fb).
Local Abbreviation saves := (PMBAS.saves R0 S).
Local Abbreviation mem_ok := (PMBAS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBAS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBAS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBA1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBA1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBA1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBA1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBA1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBA1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBA1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBA1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBA2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBA2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBA2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBa6 "B'R=yR0%211'3&QBz&R>r1%2271%5241&QC&QF+2+R0%3221%5271%=271pU4?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBAP2.aligned; first [assumption | lia]].
Local Ltac prep_ctx M W MO :=
let PA := fresh "PA" in let IA := fresh "IA" in let VIS := fresh "VIS" in let VREF := fresh "VREF" in let BASE := fresh "BASE" in
let ERR := fresh "ERR" in let TB := fresh "TB" in let HH := fresh "HH" in let MB := fresh "MB" in let STEP := fresh "STEP" in
let EE := fresh "EE" in let CK := fresh "CK" in let EK := fresh "EK" in let DK := fresh "DK" in let STK := fresh "STK" in
pose proof W as ((PA & IA & VIS & VREF & BASE & ERR & TB) & HH & MB & STEP & EE & CK);
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF; cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF;
unfold PMSP.visitor_at in VIS; cbn [pa_vp_visitor AD PmLayoutS.ADDR_S] in VIS;
pose proof MO as (EK & DK & STK);
let MOK := fresh "MOK" in pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK;
let Mh := fresh "Mh" in let Ml := fresh "Ml" in pose proof MOK as (Mh & Ml & _);
let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in pose proof FOK as (F1 & F2 & F3);
let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in let X4 := fresh "X4" in let X5 := fresh "X5" in
pose proof SBND as (X1 & X2 & X3 & X4 & X5);
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBAS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBA1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBA1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBA1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBA1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let ek_fp := PMBA1.ek_fp L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_run := PMBA1.WP_run L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let WP_hi := PMBA1.WP_hi L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_del := PMBA4.grow_del L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_end_i := PMBA4.grow_end_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_end_ct := PMBA4.grow_end_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let CRED0 := PMBA1.CRED0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let Rgp0 := PMBA1.Rgp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let call_keep0 := PMBA4.call_keep0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_objs := PMBA5.keep_objs L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_facts := PMBA5.push_facts L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_i := PMBA5.grow_cpy_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_ct := PMBA5.grow_cpy_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Abbreviation gstate := (PMBA5.gstate L HI model0 LBX fb s0 str sm0 e0).
Local Abbreviation pushok := (PMBA5.pushok s0 sm0).
Lemma grow_new : ltac2:(TCodec.tc2 tcn__PmBa6 "VG'5'Q;&;y5'R=yR0%211%5241'2y8%611%311p061':'Q3'Q5'1&B'Q4'4&Q<r8&R<&QEu1%211%42G1%7261+Vf[<%72H1%;3H31r9u2%:11%<2O1%?241&QGvQ?+T0%3221%B2Q31%F3Q361r:u:%E11%G2Q:1%J241&QD+Q0&QF+2&QA&Q1r7%211+1%5221%8271%;2:1%Q52QF1%Q93QF>1&LvAr;%3221&F&Q>+SH%Q02O1r>%544721r<vQO+Q8%G221%:494Q41&Nr=%23@Q91&Mv8v>v9%46321Q>;>&Ov6vR5vQLvR8vR?vR;vQNr?%9@=87;6E54321H@FNQC&Q8r@+8%Q>2I1zvQJ%65Q25321'3&QB%QC1;%2261+:%4231%6231&Q:vQ@%231NI&DrIr4%3221r5%S021R7r2%S02SA1%S43SA31%Q<3QJRC5r6%Q;6Q:Q9Q8REQB1&JrJrH&CrG%R<14%R>21R:%RA2R@1%RD2RC1%63QD51%:@QEQ@Q?QCQMQ=Q<Q;Q:R@<9E81BrQ0%R64R5SBR31%R74R6S9S1QN%Q;5R7ROQ8Q7Q6&Q7rKrN%RI11%RK21RG%RN2RM1%S12S01%C3R161&Q2%12R3QK&I%149SF7I%42R61%=4R0641%QB2SAQ3r3%S721Q5%QE21QJ&ErQ5%241QOQ=5p041p081pT>U11pSBU21'Q=&H%11QH&Q6%16S5R;S2T;RJS0v7%64S7421p081p0D1p0Q31p0Q51p0Q71p0Q:1p0QF1p0QI1p0QK1p0R11p2UD1pT:U81pLU:1pQ2U@1pT4UG1rFrE+ehTHrDrC%H6SL54321%L4SMJ1Gp081p0RC1p0RG1p0RO1p0S71p0SB1p0SH1p0SL1p0T21p0T91p0T>1p0U21p0U>1pSDUK1pSHUM1pSLUO1pTFV11pTDV31pT8V51pJV71pQ0V=1pT2VD1pT@VF1").
Proof. intros ra_alloc fx R M model s1 sm e cr c.
intros X1r X2 X10 KP C120 C128 SV MO W ECZ Hk OPN KNT.
prep_ctx M W MO.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (STKc : L5C.stk (hl_sptop L) M (S - 128) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M S SCR (S - 128) PMSP.OPNEW_SCR STK); unfold PMBAS.SCR, PMSP.OPNEW_SCR; [lia|lia|lia|]. replace (S - 128) with (S + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
pose proof (ly_kpm L LY) as KPM. pose proof (ly_bov L LY) as BOV.
pose proof (PM.pow2_pos (PM.p_k s1 + 1) ltac:(lia)) as Pp1.
assert (P11 : 2 ^ (PM.p_k s1 + 1) <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
assert (CRD : credit_ok L cr (32 * 2 ^ (PM.p_k s1 + 1))).
{ apply (PMBK.grow_credit_ok L cr0 cr (PM.pot_parser L s0) s1 CRED0 CK Hk); [lia|lia| |].
all: pose proof TB as (Tg & Tc & _); pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & _);
unfold PM.pot_text; cbn [fst snd].
- apply Z.mul_nonneg_nonneg; lia.
- assert (Cap : PM.vs_cap (PM.p_tb s1) <= 2 ^ 27).
{ destruct (PM.p_tb s1) as [n0|c0 n0 q0]; cbn [PM.vs_cap]; [lia|]. destruct PTB as (_ & _ & _ & _ & _ & _ & CB & _). lia. }
assert (0 <= (23 - PM.p_tg s1) * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia). lia. }
unfold PMS.opnew_spec, PMSP.opnew_spec in OPN. cbn [pa_opnew AD PmLayoutS.ADDR_S] in OPN.
apply (OPN fx R M model K LB1 cr (32 * 2 ^ (PM.p_k s1 + 1)) (S - 128) 0x3596c HH MOK K0); [rewrite L5K.rl10; exact X10| lia| exact CRD| rewrite L5K.rl1; exact X1r| split; [lia| reflexivity]
| rewrite L5K.rl2; exact X2| rewrite L5K.rl4; rewrite (KP 4%nat) by PMK.inl; exact Rtp0| exact STKc|].
intros fx2 R2' M2 model2 B RB RP2 FRESH HP2 MB2 HH2.
change PMSP.OPNEW_SCR with 8240 in HP2.
pose proof (L5C.fresh_block_bounds L LB1 M2 B _ FRESH) as (FB0 & FB1 & FB16 & _ & FB4).
destruct FRESH as (_ & FAP & FDEF).
assert (INC1 : incl LBX LB1) by (intros x Hx; unfold LB1; apply in_or_app; right; exact Hx).
assert (MO2 : mem_ok M2) by (apply (call_keep0 LB1 M M2 (S - 128) 8240 MO HP2 INC1); lia).
assert (EKc : PMK.ek L LB1 (S - 128) 8240 [] M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (STKc' : L5C.stk (hl_sptop L) M (S - 128) 8240) by exact STKc.
assert (SCc : 0 <= 8240) by lia.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr M _ HH); apply incl_refl).
assert (WHI0 : forall a, PMK.inW [] a -> S - 128 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (NW : forall a n0, forall i, a <= i < a + n0 -> ~ PMK.inW [] i) by (intros a n0 i _ I; exact (PMFR.inW_nil i I)).
assert (AGH : forall a n0, S - 128 <= a -> a + n0 <= 2 ^ 64 -> L5C.agree_on M M2 a n0).
{ intros a n0 H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 128) 8240 [] M M2 EKc STKc' SCc a n0 H1 H2). apply NW. }
apply (KNT fx2 R2' M2 model2 B RP2).
- change (getr R2' (reg 10) = Z_to_bv 64 B) in RB. exact RB.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia|assumption]).
- exact MO2.
- split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S].
split. { apply (PMFR.parser_keep RSEGS AD L KL LB1 (S - 128) 8240 [] M M2 EKc STKc' SCc BR1 WHI0); [lia|lia| apply NW| | exact PA].
intros x Hx. unfold LB1. apply in_or_app. left. exact Hx. }
split. { apply (PMFR.iss_keep RSEGS AD L KL LB1 (S - 128) 8240 [] M M2 EKc STKc' SCc BR1 WHI0); [lia|lia| apply NW| | exact IA].
intros x Hx. apply INC1. apply INCS. exact Hx. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact VIS]. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact VREF]. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (S - 128) 8240 [] M M2 EKc); [| | | | exact BASE].
all: intros a _; apply PMFR.outside_of_not_inW; apply PMFR.inW_nil. }
split; [|exact TB].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 (S - 128) 8240 [] M M2 EKc); [| | exact ERR].
all: intros a _; apply PMFR.outside_of_not_inW; apply PMFR.inW_nil. } }
split; [exact HH2|]. split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact STEP|]. split; [exact EE|].
split; [exact FB0|]. split; [exact FB16|]. split; [exact FB4|]. split; [exact FB1|]. split; [|exact FDEF].
intros B2 m2 Hin2. exact (L5C.blocks_apart_in B _ LB1 B2 m2 FAP Hin2).
- apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact C120].
- apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact C128].
- apply (PMBK.ec_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact ECZ].
- apply (PMBK.grow_credit L cr0 cr (PM.pot_parser L s0) s1); [exact CK| reflexivity| reflexivity| reflexivity| lia].
- intros a n0 H1 H2. apply AGH; [exact H1| clear - H2 F1 F2 X3; lia].
Qed.
Lemma grow_g_i : ltac2:(TCodec.tc2 tcn__PmBa6 "UC'Q;&;y5'R=yR0%211%5241'2y8%611%311p061':'Q3'Q5'1&B'5'4&Q<r8&R<&QEu2%211%42G1%7261&QGvQ?+T0%3221%:2K1%>3K61r9u8%=11%?2Q21%B241&QF+2&QA&Q1r6%211+1%5221%8271%J2Q;1%N3Q;;1r:u9%M11%O2QB1%Q2241vQO+8%@221%Q42QE1%Q83QE51r;uB%Q711%Q92QL1%Q<241+]@%I2;1%Q=2QN1%QA3QN41r<uC%Q@11%QB2R51%QE241&QD+Q0%Q21Q:%Q62Q51%4231%QI2R:1%QM3R:71r=u:%QL11%QN2RA1%R1241%R02RAQ;%R43RA21&LvAr>%3221&F&Q>+SH%R32R21+VlaD%544721r?+Q8%QK2Q=1%9483R61&Nr@%23?R;1&Mv8v>v9rA%56432RAQG1&Jv6vR5vR8vR?vR;vQNrB%8@=76;R054321:@EMQ6QB&Q8rCzvQJ%45O3R321&K(Q0+3%241666%45?=;D1&Q7vQL&Q2%12KC&I%RM1>%RO21RK%34@Q719%62Q01%948Q461&Q9vQ@%231Q4N'Q=&H%114&Q6rIrH+Vf[<rGrF%66QK54321v7%;4QM921p0=1p0A1p0L1p0Q21p0Q81p0QB1p0QI1p0QM1p0R21p0R91p0R>1p0RF1p0S31p0S=1p0SH1p0T91p2TI1pSHTK1pSLTM1pTFTO1pTDU11pT8U31pJU51pQ0U;1pT2UB1").
Proof. intros fx R M model s1 sm e cr B.
intros X2 X8 X9 X18 X19 X10 KP C120 C128 SV MO GS ECZ PK CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBAS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
cbn [PM.p_b PM.p_k PM.p_stk] in VC0, VC8, VC16, Hk', Hlen, Hal, DB, EL. rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4).
unfold hl_ceil in V4, GB1.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
assert (WB : L5.writable RSEGS M B (2 * (32 * 2 ^ vk1))).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
cfeed P (PMBAP2.baIG_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 54%nat => 2 ^ (vk1 + 1) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T11 & T12 & T13 & T19 & T20 & T21 & E24 & E16 & E8 & E0).
apply (PMK.spiece RSEGS L HI KL HIok ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M model fx fx1 R 0x3596c R1 0xa9160 M1
(fun a => (B + 32 * 2 ^ vk1 + 0 <= a < B + 32 * 2 ^ vk1 + 0 + 32)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Pa. apply (PMK.cwr_block L ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) B (32 * 2 ^ (vk1 + 1)) a (or_introl eq_refl)). lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= B + 32 * 2 ^ vk1 \/ B + 32 * 2 ^ vk1 + 32 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M1 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia].
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- apply AGo; [lia|lia| pose proof (GB3 vb1 (32 * 2 ^ vk1) VIN) as GAP; clear - GAP P2 Pp; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
assert (BK : PMBA1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG1)
as (RP1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi|]. intros X. apply N. unfold PMBA1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA1. } { exact ITB. }
apply (grow_cpy_i fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B (PM.PS 3 0 0 0)).
- split; [exact T2|]. split; [exact T8|]. split; [rewrite (KS1 9%nat) by PMK.inl; exact X9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact X18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T1.
- rewrite (KS1 10%nat) by PMK.inl. exact X10.
- exact T11.
- exact T12.
- exact T19.
- rewrite T20. f_equal. cbn [PM.p_k]. lia.
- exact T21.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
- exact MO1.
- split; [exact RP1|]. split; [exact HH1|]. split; [exact MB|]. split; [exact STEP|]. split; [exact EE|].
split; [exact GB0|]. split; [exact GB16|]. split; [exact GB1|]. split; [exact GB2|]. split; [exact GB3|].
intros i Hi. apply MG1. apply GBD. exact Hi.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia]|lia|lia| exact ECZ].
- exact PK.
- cbn [PM.p_k]. unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx].
replace (B + 32 * 2 ^ vk1) with (32 * 2 ^ vk1 + B) by lia.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24].
- exact CK.
- exact OPD.
Qed.
Lemma grow_g_c : ltac2:(TCodec.tc2 tcn__PmBa6 "V5'Q;&;y5'R=yR0%211%5241'2y8%611%311p061':'Q3'Q5'1&B'5'4&Q<r9&R<&QEu2%211%42G1%7261&QGvQ?+T0%3221%:2K1%>3K61r:u8%=11%?2Q21%B241&QF+2&QA&Q1r7%211+1%5221%8271%J2Q;1%N3Q;;1r;u9%M11%O2QB1%Q2241vQO+8%@221%Q42QE1%Q83QE51r<uB%Q711%Q92QL1%Q<241+]@%I2;1%Q=2QN1%QA3QN41r=uC%Q@11%QB2R51%QE241r5%QE2R61%QI3R631'3&QBzr6%3221+`PPP0%5231%7231r?uD%R011%R22RE1%R5241&QD+Q0%QB1Q0%QF2QE1%4231%R92RJ1%R=3RJ71r@u:%R<11%R>2S11%RA241%R@2S1RA%RD3S121&LvArA%3221&F&Q>+SH%RC2RB1+Vlj<%544721rB+Q8%R;2QM1%9483RF1&NrC%23?RK1&Mv8v>v9rD%56432S1R71&Jv6vR5vR8vR?vR;vQNrE%8@=76;R@54321:@EMQ6QB&Q8rFvQJ%35N2RBQL1&K(Q0%14S6Q=QOQO%35=;9B1&Q7vQL&Q2%12IA&I%S;1<%S=21S9%:4S?Q=R8R8%44?Q621%72O1%:49Q371&Q9vQ@%231Q3M'Q=&H%114&Q6rLrK+Vf[<rJrI%66QJ54321v7%;4QL921p0=1p0A1p0M1p0Q21p0Q71p0QA1p0QH1p0QL1p0R11p0R81p0R=1p0RE1p0S21p0S;1p0SD1p0SN1p0T91p0TJ1pT6U:1p2U;1pSHU=1pSLU?1pTFUA1pTDUC1pT8UE1pJUG1pQ0UM1pT2V41").
Proof. intros fx R M model s1 sm e cr B len.
intros X2 X8 X9 X18 X19 HLn X20 X10 KP C120 C128 SV MO GS ECZ PK CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBAS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
cbn [PM.p_b PM.p_k PM.p_stk] in VC0, VC8, VC16, Hk', Hlen, Hal, DB, EL. rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4).
unfold hl_ceil in V4, GB1.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
assert (WB : L5.writable RSEGS M B (2 * (32 * 2 ^ vk1))).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
cfeed P (PMBAP2.baCG_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 48%nat => len
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 54%nat => 2 ^ (vk1 + 1) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T11 & T12 & T13 & T20 & T21 & T22 & E24 & E16 & E8 & E0).
apply (PMK.spiece RSEGS L HI KL HIok ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M model fx fx1 R 0x3596c R1 0xa9160 M1
(fun a => (B + 32 * 2 ^ vk1 + 0 <= a < B + 32 * 2 ^ vk1 + 0 + 32)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Pa. apply (PMK.cwr_block L ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) B (32 * 2 ^ (vk1 + 1)) a (or_introl eq_refl)). lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= B + 32 * 2 ^ vk1 \/ B + 32 * 2 ^ vk1 + 32 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M1 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia].
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- apply AGo; [lia|lia| pose proof (GB3 vb1 (32 * 2 ^ vk1) VIN) as GAP; clear - GAP P2 Pp; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
assert (BK : PMBA1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG1)
as (RP1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi|]. intros X. apply N. unfold PMBA1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA1. } { exact ITB. }
apply (grow_cpy_ct fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B (PM.PS 2 len 0 0) len).
- split; [exact T2|]. split; [exact T8|]. split; [rewrite (KS1 9%nat) by PMK.inl; exact X9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact X18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T1.
- rewrite (KS1 10%nat) by PMK.inl. exact X10.
- exact T11.
- exact T12.
- rewrite (KS1 19%nat) by PMK.inl. exact X19.
- exact HLn.
- exact T20.
- rewrite T21. f_equal. cbn [PM.p_k]. lia.
- exact T22.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
- exact MO1.
- split; [exact RP1|]. split; [exact HH1|]. split; [exact MB|]. split; [exact STEP|]. split; [exact EE|].
split; [exact GB0|]. split; [exact GB16|]. split; [exact GB1|]. split; [exact GB2|]. split; [exact GB3|].
intros i Hi. apply MG1. apply GBD. exact Hi.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia]|lia|lia| exact ECZ].
- exact PK.
- cbn [PM.p_k]. unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx].
replace (B + 32 * 2 ^ vk1) with (32 * 2 ^ vk1 + B) by lia.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24].
- exact CK.
- exact OPD.
Qed.
Lemma grow_g_t : ltac2:(TCodec.tc2 tcn__PmBa6 "VD'Q;&;y5'R=yR0%211%5241'2y8%611%311p061':'Q3'Q5'1&B'5'4&Q<r:&R<&QEu2%211%42G1%7261&QGvQ?+T0%3221%:2K1%>3K61r;u8%=11%?2Q21%B241&QF+2&QA&Q1r8%211+1%5221%8271%J2Q;1%N3Q;;1r<u9%M11%O2QB1%Q2241vQO+8%@221%Q42QE1%Q83QE51r=uB%Q711%Q92QL1%Q<241+]@%I2;1%Q=2QN1%QA3QN41r>uC%Q@11%QB2R51%QE241r6%QE2R61%QI3R631'3&QBzr7%3221+`PPP0%5231%7231r@uD%R011%R22RE1%R5241&QD+Q0%QB1Q0%QF2QE1%4231%R92RJ1%R=3RJ71rAu:%R<11%R>2S11%RA241%R@2S1RA%RD3S121&LvArB%3221&F&Q>+SH%RC2RB1+Vln4%544721&GrC+S9%RI2RH1%44931RD%Q92Q8R5&QC+X0%22R81%Q>241rE+Q8%RE2R71%C4B3S01&NrF%23IS51&Mv8v>v9rG%56432S;RA1&Jv6vR5vR8vR?vR;vQNrHrD%9@>87<RK65432;AF1OQ8&Q8rIvQJ%35Q92RMR71&K(Q0+4%241Q7Q@R;%45?=;D1&Q7vQL&Q2%12KC&I%SG1=%SI21SE%;4:BQ@RD%44@Q821%72Q11%:49Q571&Q9vQ@%231Q5O'Q=&H%114&Q6rOrN+Vf[<rMrL%66R654321v7%;4R8921p0=1p0A1p0M1p0Q31p0Q81p0QC1p0QJ1p0QN1p0R31p0R91p0R?1p0RF1p0RK1p0S31p0S@1p0SI1p0T21p0T<1p0TG1p0U81pU2UH1pT6UI1p2UJ1pSHUL1pSLUN1pTFV01pTDV21pT8V41pJV61pQ0V<1pT2VC1").
Proof. intros fx R M model s1 sm e cr B len tb.
intros X2 X8 X9 X18 X19 HLn X20 X10 KP C120 TBY Htb C128 SV MO GS ECZ PK CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBAS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG.
assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
pose proof PVEC as (VC0 & VC8 & VC16 & Hk' & Hlen & Hal & DB & _ & _ & EL).
cbn [PM.p_b PM.p_k PM.p_stk] in VC0, VC8, VC16, Hk', Hlen, Hal, DB, EL. rewrite HL in VC8.
assert (VIN : In (vb1, 32 * 2 ^ vk1) (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX))
by (unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4).
unfold hl_ceil in V4, GB1.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
assert (WB : L5.writable RSEGS M B (2 * (32 * 2 ^ vk1))).
{ apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B (32 * 2 ^ (vk1 + 1))); [exact GBD|lia|lia]|lia|lia]. }
cfeed P (PMBAP2.baTG_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | 48%nat => len | 50%nat => tb
| 34%nat => vb1 | 35%nat => 32 * 2 ^ vk1 | 52%nat => B | 54%nat => 2 ^ (vk1 + 1) | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T11 & T12 & T13 & _ & T20 & T21 & T22 & E24 & E16 & E8 & E0).
apply (PMK.spiece RSEGS L HI KL HIok ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M model fx fx1 R 0x3596c R1 0xa9160 M1
(fun a => (B + 32 * 2 ^ vk1 + 0 <= a < B + 32 * 2 ^ vk1 + 0 + 32)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Pa. apply (PMK.cwr_block L ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) B (32 * 2 ^ (vk1 + 1)) a (or_introl eq_refl)). lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= B + 32 * 2 ^ vk1 \/ B + 32 * 2 ^ vk1 + 32 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M1 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia].
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- apply AGo; [lia|lia| pose proof (GB3 vb1 (32 * 2 ^ vk1) VIN) as GAP; clear - GAP P2 Pp; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
assert (BK : PMBA1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG1)
as (RP1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi|]. intros X. apply N. unfold PMBA1.FPB. right; right; right. lia. }
{ exact BK. } { exact PA1. } { exact ITB. }
apply (grow_cpy_ct fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B (PM.PS 4 len tb 0) len).
- split; [exact T2|]. split; [exact T8|]. split; [rewrite (KS1 9%nat) by PMK.inl; exact X9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact X18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
- exact T1.
- rewrite (KS1 10%nat) by PMK.inl. exact X10.
- exact T11.
- exact T12.
- rewrite (KS1 19%nat) by PMK.inl. exact X19.
- exact HLn.
- exact T20.
- rewrite T21. f_equal. cbn [PM.p_k]. lia.
- exact T22.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGo; [lia|lia| clear - GB1 X5 P2 Pp; lia]|lia|lia|assumption]).
- exact MO1.
- split; [exact RP1|]. split; [exact HH1|]. split; [exact MB|]. split; [exact STEP|]. split; [exact EE|].
split; [exact GB0|]. split; [exact GB16|]. split; [exact GB1|]. split; [exact GB2|]. split; [exact GB3|].
intros i Hi. apply MG1. apply GBD. exact Hi.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGo; [lia|lia| clear - GB1 X5 F1 P2 Pp; lia]|lia|lia| exact ECZ].
- exact PK.
- cbn [PM.p_k]. unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx].
replace (B + 32 * 2 ^ vk1) with (32 * 2 ^ vk1 + B) by lia.
split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24].
- exact CK.
- exact OPD.
Qed.
End Call.
End WithHeap.
End PMBA6.
