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
PmCertKitG PmSrcUMemmove PmBaKit PmBaUStmts PmBaU1 PmBaU2 PmBaU4 PmBaU5 PmBaU5C PmBaUP4I PmBaUP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBaU6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaU2.PMBAU2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaU5.PMBAU5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaUStmts.PMBAUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1option"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"; "0R"]; ["0R'"; "0R0"; "6credit"; "6debit"; "6regs_preserved"; "7agree_on"; "9u64_at"; "8SCFG"; ":push_st"; ";gstate"; ";pushok"; "<kept0"; "<mem_ok"; "<saves"; "<world"; "=PS"]; ["=p_k"; "=pot_parser"; "=pst"; "=pstate"; "=strm"; ">cfg"; ">credit_keep"; ">ec_at"; "?opdel_spec"; "?opnew_spec"; "@FPState"; "@getr"; "Asrealizes"; "Bloaded_segments"; "0S"; "0SCFG_P"]; ["Cadd"; "Cle"; "Clt"; "Cmul"; "Cof_nat"; "Cpow"; "Csub"; "0a"; "0c"; "0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"; "0fx"]; ["0fx'"; "0model"; "0model'"; "0model0"; "0n"; "0s0"; "0s1"; "0sm"; "0sm0"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0str"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBAU6.
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
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBaU6 "B'R:yR0%211'3&QAz&R;r1%2271%5241&QB&QE+2+R0%3221%5271%=271pTL?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBAUP2.aligned; first [assumption | lia]].
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
Let grow_cpy_i := PMBAU5C.grow_cpy_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_c := PMBAU5C.grow_cpy_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let grow_cpy_t := PMBAU5C.grow_cpy_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Local Abbreviation gstate := (PMBAU5.gstate L HI model0 LBX fb s0 str sm0 e0).
Local Abbreviation pushok := (PMBAU5.pushok s0 sm0).
Local Abbreviation sof := (PMBAU5.sof S fb).
Local Ltac gpost PP :=
repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end;
repeat split; first [ PMK.greg | PMK.gmem ].
Lemma grow_new : ltac2:(TCodec.tc2 tcn__PmBaU6 "V5'Q:&;y5'R:yR0%211%5241'2y8%611%311p061':'Q2'Q4'1&B'Q3'4&Q;r8&R9&QDu1%211%42G1%7261+Vho<%72H1%;3H31r9u2%:11%<2O1%?241&QFvQ>+U0%3221%B2Q31%F3Q361r:u:%E11%G2Q:1%J241&QC+Q0&QE+2&Q@&Q0r7%211+1%5221%8271%;2:1%Q52QF1%Q93QF>1&KvAr;%3221&M%134M3&Lv8v>v9vQNr<%66543Q421&Nv6vR3vQKvR5vR<vR8vQMr=%9@?87=6<54321;DQ9QDQN&Q7&Q=r>+8%Q52A1zvQI%7565321'3&QA%Q:1<%2261+:%4231%6231&Q9vQ?%231Q1J'5&DrGr4%3221r5%RH21QOr2%RH2S91%RL3S931%Q?3QBR;5r6%Q?6Q>Q=Q<R=Q;1&IrHrF&CrE%R414%R621R2%R92R81%R<2R;1%63QH51%:@QIQBQAQGQFQ?Q>Q=Q<R8<9E81B%Q:5Q9S9Q6Q5Q4&Q6rJ%R=11%R?21R;%RB2RA1%RE2RD1%?3R1M1&Q1%12R3QI&H%149RD7D%42R61%<4QN641%Q?2S5Or3%RK21Q1%QB21QG&ErQ1%241QLQ95p041p081pT:Q?1pS@Q@1'Q<&G%11QE&Q5%16R6R9RCSORLSAv7%64R8421p081p0D1p0Q21p0Q41p0Q@1p0QC1p0QE1p0QK1p2R01pT6TJ1pLTL1pQ2U21pT2U91rDrC+elW<rBrA%F6RK54321%J4RLH1Ep081p0R>1p0RB1p0RJ1p0S31p0S>1p0SF1p0SI1p0SN1p0TB1p0TN1pSBU;1pSFU=1pSJU?1pT@UA1pT>UC1pT4UE1pJUG1pQ0UM1pT0V41").
Proof. intros fx R M model s1 sm e cr c.
intros X1r X2 X10 KP SV MO W ECZ Hk OPN KNT.
prep_ctx M W MO.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (STKc : L5C.stk (hl_sptop L) M (S - 160) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M S SCR (S - 160) PMSP.OPNEW_SCR STK); unfold PMBAUS.SCR, PMSP.OPNEW_SCR; [lia|lia|lia|]. replace (S - 160) with (S + (-10) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
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
unfold PMU.opnew_spec, PMSP.opnew_spec in OPN. cbn [pa_opnew AD PmLayoutU.ADDR_U] in OPN.
apply (OPN fx R M model K LB1 cr (32 * 2 ^ (PM.p_k s1 + 1)) (S - 160) 0x363ec HH MOK K0); [rewrite L5K.rl10; exact X10| lia| exact CRD| rewrite L5K.rl1; exact X1r| split; [lia| reflexivity]
| rewrite L5K.rl2; exact X2| rewrite L5K.rl4; rewrite (KP 4%nat) by PMK.inl; exact Rtp0| exact STKc|].
intros fx2 R2' M2 model2 B RB RP2 FRESH HP2 MB2 HH2.
change PMSP.OPNEW_SCR with 8240 in HP2.
pose proof (L5C.fresh_block_bounds L LB1 M2 B _ FRESH) as (FB0 & FB1 & FB16 & _ & FB4).
destruct FRESH as (_ & FAP & FDEF).
assert (INC1 : incl LBX LB1) by (intros x Hx; unfold LB1; apply in_or_app; right; exact Hx).
assert (MO2 : mem_ok M2) by (apply (call_keep0 LB1 M M2 (S - 160) 8240 MO HP2 INC1); lia).
assert (EKc : PMK.ek L LB1 (S - 160) 8240 [] M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (STKc' : L5C.stk (hl_sptop L) M (S - 160) 8240) by exact STKc.
assert (SCc : 0 <= 8240) by lia.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr M _ HH); apply incl_refl).
assert (WHI0 : forall a, PMK.inW [] a -> S - 160 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (NW : forall a n0, forall i, a <= i < a + n0 -> ~ PMK.inW [] i) by (intros a n0 i _ I; exact (PMFR.inW_nil i I)).
assert (AGH : forall a n0, S - 160 <= a -> a + n0 <= 2 ^ 64 -> L5C.agree_on M M2 a n0).
{ intros a n0 H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1 (S - 160) 8240 [] M M2 EKc STKc' SCc a n0 H1 H2). apply NW. }
apply (KNT fx2 R2' M2 model2 B RP2).
- change (getr R2' (reg 10) = Z_to_bv 64 B) in RB. exact RB.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBAUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia|assumption]).
- exact MO2.
- split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split. { apply (PMFR.parser_keep RSEGS AD L KL LB1 (S - 160) 8240 [] M M2 EKc STKc' SCc BR1 WHI0); [lia|lia| apply NW| | exact PA].
intros x Hx. unfold LB1. apply in_or_app. left. exact Hx. }
split. { apply (PMFR.iss_keep RSEGS AD L KL LB1 (S - 160) 8240 [] M M2 EKc STKc' SCc BR1 WHI0); [lia|lia| apply NW| | exact IA].
intros x Hx. apply INC1. apply INCS. exact Hx. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact VIS]. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact VREF]. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 (S - 160) 8240 [] M M2 EKc); [| | | | exact BASE].
all: intros a _; apply PMFR.outside_of_not_inW; apply PMFR.inW_nil. }
split; [|exact TB].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 (S - 160) 8240 [] M M2 EKc); [| | exact ERR].
all: intros a _; apply PMFR.outside_of_not_inW; apply PMFR.inW_nil. } }
split; [exact HH2|]. split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact STEP|]. split; [exact EE|].
split; [exact FB0|]. split; [exact FB16|]. split; [exact FB4|]. split; [exact FB1|]. split; [|exact FDEF].
intros B2 m2 Hin2. exact (L5C.blocks_apart_in B _ LB1 B2 m2 FAP Hin2).
- apply (PMBK.ec_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact ECZ].
- apply (PMBK.grow_credit L cr0 cr (PM.pot_parser L s0) s1); [exact CK| reflexivity| reflexivity| reflexivity| lia].
- intros a n0 H1 H2. apply AGH; [exact H1| clear - H2 F1 F2 X3; lia].
Qed.
Lemma grow_g_i : ltac2:(TCodec.tc2 tcn__PmBaU6 "VI'Q:&;y5'R:yR0%211%5241'2y8%611%311p061':'Q2'Q4'1&B'5'4&Q;r8&R9&QDu2%211%42G1%7261&QFvQ>+U0%3221%:2K1%>3K61r9u8%=11%?2Q21%B241&QE+2&Q@&Q0r6%211+1%5221%8271%J2Q;1%N3Q;;1r:u9%M11%O2QB1%Q2241r7%>11%B2A1%Q42QE1%Q83QE51r;u:%Q711%Q92QL1%Q<241r4%Q<2QM1%Q@3QM31r<uB%Q?11%QA2R41%QD241vQN+]@%Q2221%QF2R71%QJ3R751r=uE%QI11%QK2R>1%QN241+Qo`0%QN2R?1%R23R?31&KvAr>%3221r?uC%R511%R72RJ1%R:241+\@%QG2G1%R;2RL1%R?3RL41&F&Q=+TH%R:2R91+Vh`8%544>21r@+S0%R?2R>1%9483R=1rA+SH%RC2RB1+WPS8%>4=421rB+T0%RH2RG1+Q8%R=2Q=1%D4C531rC+T8%RN2RM1+8%RC2QC1%J4I531rD+R0%S42S31%N4M31Q1rE+R8%S82S71z%Q34Q2421&MrF%23QBS<1&Lv8v>v9rG%56432SBR61&Iv6vR3vR5vR<vR8vQMrH%8@=76;R?54321:@FJQ0Q6&Q7rIvQI%35QH2Q0G1&J(O+3%241KKK%45><:C1&Q6vQK&Q1%12JB&H%SM1=%SO21SK%34?Q719%62O1%948Q361&Q8vQ?%231Q3M'Q<&G%114&Q5rOrN+Vho<rMrL%66RD54321v7%;4RF921p0=1p0A1p0L1p0Q21p0Q71p0QA1p0QH1p0QL1p0R21p0R71p0R>1p0RE1p0RK1p0S01p0S71p0SA1p0SF1p0SO1p0T:1p0TC1p0TN1p0U?1p2UO1pSFV11pSJV31pT@V51pT>V71pT4V91pJV;1pQ0VA1pT0VH1").
Proof. intros fx R M model s1 sm e cr B.
intros X2 X8 X9 X10 X18 X21 KP X19 C152 C160 C120 C128 C136 C64 C72 SV MO GS ECZ PK CK OPD.
pose proof GS as (RP & HH & MB & STEP & EE & GB0 & GB16 & GB1 & GB2 & GB3 & GBD).
pose proof PK as (IV1 & HD1 & ES1 & HL & Hk & Hc & Hm & Hi0 & Hcnt).
pose proof RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof MOK as (Mh & Ml & _).
pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2' & X3 & X4 & X5).
pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR. unfold PMBAUS.SCR in WR.
pose proof PA as (_ & PDEF & _). pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
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
pose proof (PMFR.brange_of_heap L HI HIok _ (PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) cr M _ HH (fun x Hx => or_intror Hx) vb1 (32 * 2 ^ vk1) VIN) as (V0 & V1 & V4). unfold hl_ceil in V4, GB1.
pose proof (GB3 vb1 (32 * 2 ^ vk1) VIN) as GAP.
assert (P2 : 2 ^ (vk1 + 1) = 2 * 2 ^ vk1) by (rewrite Z.pow_add_r by lia; lia).
assert (P10 : 2 ^ vk1 <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
pose proof (PM.pow2_pos vk1 ltac:(lia)) as Pp.
assert (WBn : L5.writable RSEGS M B (32 * 2 ^ (vk1 + 1))) by (apply (L5C.writable_of_defined RSEGS); [exact GBD|lia|lia]).
assert (GP : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x363ec) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xaa1b4) M1 (seg_rom RSEGS))
/\ mem_grows M M1
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 160 <= i < S - 160 + 64) -> ~ (S - 96 <= i < S - 96 + 40) -> ~ (B + 32 * 2 ^ vk1 <= i < B + 32 * 2 ^ vk1 + 32) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (forall x, In x [3; 4; 10; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 0x36308 /\ getr R1 (reg 2) = Z_to_bv 64 (S - 144) /\ getr R1 (reg 8) = Z_to_bv 64 (S - 96)
/\ getr R1 (reg 9) = Z_to_bv 64 (fb + 400) /\ getr R1 (reg 11) = Z_to_bv 64 vb1 /\ getr R1 (reg 12) = Z_to_bv 64 (32 * 2 ^ vk1)
/\ getr R1 (reg 18) = Z_to_bv 64 B
/\ (L5.u32_at RSEGS M1 (B + 32 * 2 ^ vk1) 3 /\ L5.u64_at RSEGS M1 (B + 32 * 2 ^ vk1 + 8) 0 /\ L5.u8_at RSEGS M1 (B + 32 * 2 ^ vk1 + 16) 0 /\ L5.u64_at RSEGS M1 (B + 32 * 2 ^ vk1 + 24) 0)
/\ L5.u64_at RSEGS M1 (S - 96) B /\ L5.u64_at RSEGS M1 (S - 88) (B + 32 * 2 ^ vk1) /\ L5.u64_at RSEGS M1 (S - 80) (B + 32 * 2 ^ vk1 + 32)
/\ L5.u64_at RSEGS M1 (S - 72) (B + 2 * (32 * 2 ^ vk1)) /\ L5.u64_at RSEGS M1 (S - 64) (fb + 400) /\ L5.u64_at RSEGS M1 (S - 120) 229544
/\ L5.u64_at RSEGS M1 (S - 128) (fb + 40) /\ L5.u64_at RSEGS M1 (S - 136) (fb + 8) /\ L5.u64_at RSEGS M1 (S - 144) (fb + 432)).
{ assert (KC : vk1 = 0 \/ vk1 = 1 \/ vk1 = 2 \/ vk1 = 3 \/ vk1 = 4 \/ vk1 = 5 \/ vk1 = 6 \/ vk1 = 7 \/ vk1 = 8 \/ vk1 = 9 \/ vk1 = 10) by lia.
destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- change (2 ^ 0) with 1 in *. change (2 ^ (0 + 1)) with 2 in *.
cfeed P (PMBAUP4I.ubaIG0_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 1) with 2 in *. change (2 ^ (1 + 1)) with 4 in *.
cfeed P (PMBAUP4I.ubaIG1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 2) with 4 in *. change (2 ^ (2 + 1)) with 8 in *.
cfeed P (PMBAUP4I.ubaIG2_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 3) with 8 in *. change (2 ^ (3 + 1)) with 16 in *.
cfeed P (PMBAUP4I.ubaIG3_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 4) with 16 in *. change (2 ^ (4 + 1)) with 32 in *.
cfeed P (PMBAUP4I.ubaIG4_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 5) with 32 in *. change (2 ^ (5 + 1)) with 64 in *.
cfeed P (PMBAUP4I.ubaIG5_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 6) with 64 in *. change (2 ^ (6 + 1)) with 128 in *.
cfeed P (PMBAUP4I.ubaIG6_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 7) with 128 in *. change (2 ^ (7 + 1)) with 256 in *.
cfeed P (PMBAUP4I.ubaIG7_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 8) with 256 in *. change (2 ^ (8 + 1)) with 512 in *.
cfeed P (PMBAUP4I.ubaIG8_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 9) with 512 in *. change (2 ^ (9 + 1)) with 1024 in *.
cfeed P (PMBAUP4I.ubaIG9_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
- change (2 ^ 10) with 1024 in *. change (2 ^ (10 + 1)) with 2048 in *.
cfeed P (PMBAUP4I.ubaIG10_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8
| 34%nat => vb1 | 52%nat => B | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & PP).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
split; [intros i Hi N1 N2 N3; apply FRZ1; [exact Hi| exact N1| exact N2| intros X; apply N3; lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply PMPK.sub_in; vm_compute; reflexivity|].
gpost PP.
}
destruct GP as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T9 & T11 & T12 & T18 & (E0 & E8 & E16 & E24) & O96 & O88 & O80 & O72 & O64 & O120 & O128 & O136 & O144).
apply (PMK.spiece RSEGS L HI KL HIok _ cr M model fx fx1 R 0x363ec R1 0xaa1b4 M1
(fun a => (S - 160 <= a < S - 160 + 64) \/ (S - 96 <= a < S - 96 + 40) \/ (B + 32 * 2 ^ vk1 <= a < B + 32 * 2 ^ vk1 + 32)) K HH Mh Ml ltac:(lia) MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
{ intros a [Pa|[Pa|Pa]]; [apply (PMK.cwr_stack L _ M S SCR a STK); unfold PMBAUS.SCR; lia| apply (PMK.cwr_stack L _ M S SCR a STK); unfold PMBAUS.SCR; lia|].
apply (PMK.cwr_block L ((B, 32 * 2 ^ (vk1 + 1)) :: PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) ++ LBX) B (32 * 2 ^ (vk1 + 1)) a (or_introl eq_refl)). lia. }
{ intros a. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AGo : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 160 \/ S - 56 <= a) -> (a + n <= B + 32 * 2 ^ vk1 \/ B + 32 * 2 ^ vk1 + 32 <= a) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ1; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
pose proof IV1 as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1)).
{ apply (PMPK.parser_at_keep RSEGS AD M M1 (fb + 40) (fb + 440) _ PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AGo; [lia|lia|lia| clear - GB1 X5 F1 P2 Pp; lia].
- apply PMPK.dkr_grows. exact MG1.
- lia.
- lia.
- apply AGo; [lia|lia| clear - V4 X5 Pp; lia| clear - GAP P2 Pp; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG1. }
assert (BK : PMBAU1.blk_ok L LBX B (32 * 2 ^ (vk1 + 1))).
{ right. split; [exact GB0|]. split; [unfold hl_ceil; exact GB1|]. split; [exact GB2|].
intros B' m' Hin'. apply GB3. apply in_or_app. right. exact Hin'. }
destruct (keep_objs M M1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e B (32 * 2 ^ (vk1 + 1)) RP MO MG1)
as (RP1 & MO1).
{ intros i Hi N. apply FRZ1; [exact Hi| | |]; intros X; apply N; unfold PMBAU1.FPB; [left; unfold PMBAUS.SCR; lia| left; unfold PMBAUS.SCR; lia| right; right; right; lia]. }
{ exact BK. } { exact PA1. } { exact ITB. }
assert (AGs : forall a n, S - 56 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n) by (intros a n H1 H2; apply AGo; [lia|lia|lia| clear - H1 GB1 X5 P2 Pp; lia]).
apply (grow_cpy_i fx1 R1 M1 model (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) sm e cr B (PM.PS 3 0 0 0)).
- exact T1.
- exact T2.
- exact T8.
- exact T9.
- exact T18.
- rewrite (KS1 21%nat) by PMK.inl. exact X21.
- intros k Hk0. rewrite (KS1 k) by (unfold PMBAUS.CSK in Hk0; cbn in Hk0 |- *; tauto). apply KP. exact Hk0.
- rewrite (KS1 19%nat) by PMK.inl. exact X19.
- rewrite (KS1 10%nat) by PMK.inl. exact X10.
- exact T11.
- exact T12.
- unfold PMBAU5.sof. repeat split; assumption.
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBAUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGs; lia|lia|lia|assumption]).
- exact MO1.
- split; [exact RP1|]. split; [exact HH1|]. split; [exact MB|]. split; [exact STEP|]. split; [exact EE|].
split; [exact GB0|]. split; [exact GB16|]. split; [exact GB1|]. split; [exact GB2|]. split; [exact GB3|].
intros i Hi. apply MG1. apply GBD. exact Hi.
- apply (PMBK.ec_agree RSEGS M M1); [apply AGs; lia|lia|lia| exact ECZ].
- exact PK.
- unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24].
- exact CK.
- exact OPD.
Qed.
End Call.
End WithHeap.
End PMBAU6.
