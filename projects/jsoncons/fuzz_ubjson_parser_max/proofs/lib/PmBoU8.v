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
PmCertKitG PmBaKit PmBoUStmts PmBoU1 PmBoU2 PmBoU4 PmBoU7 PmBoUP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBoU8 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBoUStmts.PMBOUS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1length"; "1list"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0GL"; "0HI"; "0K"; "0L"; "0LBX"; "4Model"]; ["5bvmap"; "0M"; "0M'"; "0M0"; "0M2"; "0MKE"; "0OPD"; "0OPN"; "0R"; "0R'"; "0R0"; "6credit"; "6regs_preserved"; "7agree_on"; "7hpres"; "9ra_ok"]; ["9u8_at"; "8SCFG"; ":mem_ok"; ":regs_at"; ":saves"; ":world"; ";pa_errcat_obj"; "<ADDR_U"; "=inv_d"; "=p_more"; "=p_src"; "=p_stk"; "=pst"; "=pstate"; "=strm"; "=unread"]; [">W_run"; ">cfg"; ">ec_at"; ">prog_len"; "?get_length_spec"; "?make_ec_spec"; "?opdel_spec"; "?opnew_spec"; "@FPState"; "@getr"; "Asrealizes"; "Bloaded_segments"; "0S"; "0SCFG_P"; "Cadd"; "Cle"]; ["Clt"; "Cof_nat"; "Cpow"; "Csub"; "0a"; "0cat"; "0cr"; "0cr'"; "0cr0"; "0e"; "0e'"; "0e0"; "0fb"; "0fx"; "0fx'"; "0model"]; ["0model'"; "0model0"; "0n"; "0ra"; "0s'"; "0s0"; "0s1"; "0scr'"; "0sm"; "0sm'"; "0sm0"; "0sp'"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0str"]; ["0tb"; "0v"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBOU8.
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
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBoU8 "B'RMyR0%211'5&QOz&RNr1%2271%5241&R0&R2+2+R0%3221%5271%=271pV6?1").
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
Let call_keep := PMBOU1.call_keep L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let UNR0 := PMBOU1.UNR0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let gl_err_c := PMBOU7.gl_err_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let gl_err_t := PMBOU7.gl_err_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let gl_ok_c := PMBOU7.gl_ok_c L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let gl_ok_t := PMBOU7.gl_ok_t L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma call_keep_run : ltac2:(TCodec.tc2 tcn__PmBoU8 "Q='RMyR0%211'3y8%511%311p051'9&Q2v=vCv>vQLvR<r4%76654321&Nr3r2&Q@&Q7%2218r5%77><65219&QO&R3+jP0%22?1%32>;%5221%628Bz%821:r8%J6IHGFE1p031p061p081p0?1p0H1pU@Q11pUHQ21pQ:Q41pQ4Q51").
Proof. intros M M2 sp' scr'.
intros (EK & DK & STK) HP H1 H2 H3. pose proof SBND as (X1 & X2 & X3 & X4 & X5).
split; [|split].
- apply (PMK.ek_trans L LBX S SCR _ M0 M M2 EK). intros a (Ha & CA & NE & OW).
apply (L5C.hpres_kept L _ sp' scr' _ M M2 a HP). split; [exact Ha|]. split; [|split; [exact NE| exact OW]].
apply (PMK.client_mono L LBX _ S SCR sp' scr' a CA (incl_refl _)). intros x Hx. unfold PMBOUS.SCR. lia.
- apply (PMK.dk_trans L LBX S SCR M0 M M2 DK). apply (PMK.dk_callee L LBX _ S SCR sp' scr' _ M M2 HP (incl_refl _)); unfold PMBOUS.SCR; lia.
- apply (PMK.stk_after RSEGS L KL _ M M2 S SCR sp' scr' _ STK HP); unfold PMBOUS.SCR; lia.
Qed.
Lemma gl_call : ltac2:(TCodec.tc2 tcn__PmBoU8 "V0&QDvQMv=v;%43321'9'QH&@y5'RMyR0%211%5241'3y8%611%311p061'?'Q<'Q>'0&K'6&QIr7&RL&R1u1%211%42F1%7261r9%72G1%;3G31&Or:%211&Q3vJvQLvR<%44321:u:%A11%C2Q51%F2:1&QN+Q8%2281%H2Q81%L3Q851r;u;%K11%M2Q?1%Q0241+8%;2A1%Q12QA1%Q53QA41&Q4%13GF:&Q2vCv>r<%46R132KJ1&Q5vRAvR8vREvROvRJvR;r=r8%9@R;R:8<7Q465432;IQ9Q=1&QB&QKr>zvR5%5543I21&Q8+1%221;&LrI%221R0%M3QCQBR1%L6RIKJQCQB?r6r5r4%K@RMRLJNIQFHGFEQOCR6321'8'7'5&QOr1%22@1+R0%4231%6231&Q6&Q7%211%N5MQHQB81&Q9%11R>%RH3S:1N(4%RJ3RLRH1%@231%A271%B2<1qV4S@1%E2SA1%Q95Q8RCQMQ6Q5%Q42Q3Q<&QCrJ%25R71Q?Q3S2%J241%K261%N281&R3+S@%22RI1r2%Q0221r3%RF213%Q321R<&MrQ1r?%3421Q<6p051p091pU6T81pT:T91'QJ&Q1%11T@&QA%16R4R3R8;RAROv<%64R6421p081p0I1p0QI1p0QN1p0R01p0R21pT@T61pTFT81pUDT:1pU:T<1pU2T>1pQ6T@1pQDTF1pTNTM1rCrB+Vne4rAr@%G6RJ54321%K4RKI1Fp081p0RF1p0RJ1p0S11p0S<1p0SB1p0SE1p0SO1p0T91p0T?1p0TC1pT>U01pTDU21pUBU41pU>U61pU0U81pQ4U:1pQBU@1pTLUG1pU8UI1pFUK1").
Proof. intros GL ra fx R M model s1 sm e cr.
intros X1r RAra (R2 & R8 & R9 & R18 & R21 & KP) X10 X11 SV MO W ECZ IV1 KNT.
prep_ctx M W MO.
assert (STKc : L5C.stk (hl_sptop L) M (S - 112) (PMSP.pm_scr 5)).
{ apply (PMK.stk_call L M S SCR (S - 112) (PMSP.pm_scr 5) STK); unfold PMBOUS.SCR, PMSP.pm_scr; [lia|lia|lia|]. replace (S - 112) with (S + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
unfold PMU.get_length_spec, PMSP.get_length_spec in GL. cbn [pa_get_length AD PmLayoutU.ADDR_U] in GL.
apply (GL 1 ltac:(lia) fx R M model K LBX cr (S - 112) ra fb cat s1 str sm e HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1r|]. split; [exact RAra|]. split; [exact R2|].
split; [rewrite (KP 3%nat) by PMK.inl; exact Rgp0|]. split; [rewrite (KP 4%nat) by PMK.inl; exact Rtp0|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args_gl, PMSP.o_p, PMSP.o_ec. cbn [pa_off_p pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11. split; [exact X10| exact X11]. }
{ exact (proj1 W). }
{ exact INCS. }
{ exact IV1. }
{ unfold PMSP.o_ec. cbn [pa_off_ec AD PmLayoutU.ADDR_U]. exact ECZ. }
{ destruct STEP as (_ & _ & _ & _ & U). pose proof UNR0. lia. }
{ apply (PMPK.credit_le_keep cr0 cr _ _ CRED0 CK). }
intros fx2 R2' M2 model2 s2 sm2 e2 cr2 RP2 POST HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 5) with 22528 in HP2.
destruct POST as (RP2' & STEP2 & EE2 & POST).
assert (MO2 : mem_ok M2).
{ apply (call_keep_run M M2 (S - 112) 22528 MO HP2); lia. }
assert (EKc : PMK.ek L LBX (S - 112) 22528 (PMSP.W_run AD fb) M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (STKc' : L5C.stk (hl_sptop L) M (S - 112) 22528) by exact STKc.
assert (SCc : 0 <= 22528) by lia.
assert (AGH : forall a n, S - 112 <= a -> a + n <= fb + 8 -> L5C.agree_on M M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LBX (S - 112) 22528 (PMSP.W_run AD fb) M M2 EKc STKc' SCc a n H1); [lia|].
intros i Hi I. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in I.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app] in I.
destruct I as (r0 & Hin & Hr). unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Hr; clear - Hi H1 H2 Hr F1 X1 X3; lia. }
apply (KNT fx2 R2' M2 model2 s2 sm2 e2 cr2 RP2).
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
unfold PMBOUS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia|assumption]).
- exact MO2.
- split; [exact RP2'|]. split; [exact HH2|]. split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|].
split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP STEP2)|]. split; [intros X; apply EE2; apply EE; exact X|].
unfold PMSP.credit_keep in *. lia.
- unfold PMSP.o_ec in POST. cbn [pa_off_ec AD PmLayoutU.ADDR_U] in POST. exact POST.
- exact AGH.
Qed.
Lemma arm_c1 : ltac2:(TCodec.tc2 tcn__PmBoU8 "T6&QDvQMv=v;%43321&QE%13543&QG%13765&QF%13987'QH&@y5'RMyR0%211%5241'3y8%611%311p061'?'Q<'Q>'0&K&Q3vJvQLvR<r7%544321'6&QIr8&RL&R1uC%211%42L1%7261&QN+R0%22>1%92O1%=3O51&Q4%13DC=&Q2vCv>r9%46QD32HG1&Q5vRAvR8vREvROvRJvR;r:r6r5%:@QOQN9=8Q276543<MQ121&QB&QKr;+8%K2Q71zvR5%7565321&Q8+1%221>'2'Q=%211&Q;%11=%21H%QA3421&QO&1%1284%QA11+QP0%5221&R0&Q?&Q:r=%211r<%5221%51Q7%721Q6%9231'QJ&Q1%11S5&QArBrA+WQSHr@r?%66Q:54321v<%;4Q<921p0=1p0H1p0O1p0Q71p0Q;1p0QD1p0R01p0R61p0R91p0RH1pT>RO1pTDS11pUBS31pU>S51pU0S71pQ4S91pQBS?1pTLSF1pQ>SH1pQ@SK1pQ<SN1pFT11").
Proof. intros GL MKE OPN OPD fx R M model s1 sm e cr.
intros RA R19 SV MO W ECZ IV1 ES1 HL0 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
cfeed P (PMBOUP1.uboC1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x38478 R1 0x37aa4 M K Mh Ml MS1).
assert (RA1 : regs_at R1).
{ split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP]. }
apply (gl_call GL 0x38484 fx1 R1 M model s1 sm e cr T1 ltac:(split; [lia| reflexivity]) RA1 T10 T11 SV MO W ECZ IV1).
intros fx2 R2' M2 model2 s2 sm2 e2 cr2 RP2 SV2 MO2 W2 POST AGH.
pose proof RA1 as (Q2 & Q8 & Q9 & Q18 & Q21 & QK).
assert (RA2 : regs_at R2').
{ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; exact Q2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; exact Q8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; exact Q9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; exact Q18|]. split; [rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl; exact Q21|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [apply QK; exact Hk0|]. unfold PMBOUS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0. }
assert (R19' : getr R2' (reg 19) = Z_to_bv 64 (fb + 64)).
{ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19. }
destruct POST as [(v & Hv & ECV & HM & HE)|(ECZ2 & IV2 & (ES2 & UNR2 & (len & Hl & RL)))].
- subst e2. apply (gl_err_c fx2 R2' M2 model2 s2 sm2 cr2 v RA2 R19' SV2 MO2 W2 Hv ECV HM).
- assert (HD2 : PM.p_depth s2 <= 1024).
{ pose proof IV2 as (_ & _ & D2 & _). rewrite ES2, ES1 in D2. lia. }
apply (gl_ok_c MKE OPN OPD fx2 R2' M2 model2 s2 sm2 e2 cr2 len RA2 R19' RL Hl SV2 MO2 W2 ECZ2 IV2 HD2); [rewrite ES2; exact ES1| lia].
Qed.
Lemma arm_t4 : ltac2:(TCodec.tc2 tcn__PmBoU8 "TN&QDvQMv=v;%43321&QE%13543&QG%13765&QF%13987'QH&@y5'RMyR0%211%5241'3y8%611%311p061'?'Q<'Q>'0&K'9&Q3vJvQLvR<r8%544321'6&QIr9&RL&R1uC%211%42M1%7261&QN+R0%22>1%92Q01%=3Q051r:uD%<11%>2Q71%A241+1%A2Q81%E3Q831&Q0&QK&R3+S1%22N1r4%645>21'5&QOzr5%3221&R0+X0%2241%8241&Q4r<%23Q=Q<1&Q2vCv>r=%46R>32QAQ@1&Q5vRAvR8vREvROvRJvR;r>r;%9@RHRG8<7QJ65432;@1Q9QE&QBr?+8%QB2QN1vR5%55Q642N1&Q8%12Q<:'2'Q=%211&Q;%11;%21D%R63421&1%1273%R511+QP0%Q=221&Q?&Q:rA%211r@%5221%51Q1%721Q0%QB231'QJ&Q1%11SI&QArFrE+WPo<rDrC%66R754321v<%;4R9921p0=1p0G1p0M1p0Q51p0Q81p0Q?1p0QJ1p0R01p0R41p0R>1p0RF1p0RO1p0S>1pV2SE1pT>SG1pTDSI1pUBSK1pU>SM1pU0SO1pQ4T11pQBT71pTLT>1pQ>T@1pQ@TC1pQ<TF1pFTI1").
Proof. intros GL MKE OPN OPD fx R M model s1 sm e cr tb.
intros RA R19 R20 TBY Htb SV MO W ECZ IV1 ES1 HL0 UNR. pose proof RA as (R2 & R8 & R9 & R18 & R21 & KP).
prep_ctx M W MO.
cfeed P (PMBOUP1.uboT4_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & T1 & T10 & T11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x383ec R1 0x37aa4 M K Mh Ml MS1).
assert (RA1 : regs_at R1).
{ split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|]. split; [rewrite (KS1 21%nat) by PMK.inl; exact R21|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP]. }
apply (gl_call GL 0x383f8 fx1 R1 M model s1 sm e cr T1 ltac:(split; [lia| reflexivity]) RA1 T10 T11 SV MO W ECZ IV1).
intros fx2 R2' M2 model2 s2 sm2 e2 cr2 RP2 SV2 MO2 W2 POST AGH.
pose proof RA1 as (Q2 & Q8 & Q9 & Q18 & Q21 & QK).
assert (RA2 : regs_at R2').
{ split; [rewrite (PMK.cs_of_preserved R1 R2' 2 RP2) by PMK.inl; exact Q2|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 8 RP2) by PMK.inl; exact Q8|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 9 RP2) by PMK.inl; exact Q9|].
split; [rewrite (PMK.cs_of_preserved R1 R2' 18 RP2) by PMK.inl; exact Q18|]. split; [rewrite (PMK.cs_of_preserved R1 R2' 21 RP2) by PMK.inl; exact Q21|].
intros k Hk0. rewrite (PMK.cs_of_preserved R1 R2' k RP2); [apply QK; exact Hk0|]. unfold PMBOUS.CSK in Hk0. cbn in Hk0. repeat (destruct Hk0 as [<-|Hk0]; [PMK.inl|]). destruct Hk0. }
assert (R19' : getr R2' (reg 19) = Z_to_bv 64 (fb + 64)).
{ rewrite (PMK.cs_of_preserved R1 R2' 19 RP2) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact R19. }
assert (R20' : getr R2' (reg 20) = Z_to_bv 64 1).
{ rewrite (PMK.cs_of_preserved R1 R2' 20 RP2) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact R20. }
assert (TBY2 : L5.u8_at RSEGS M2 (S - 97) tb) by (apply (L5C.u8_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact TBY]).
destruct POST as [(v & Hv & ECV & HM & HE)|(ECZ2 & IV2 & (ES2 & UNR2 & (len & Hl & RL)))].
- subst e2. apply (gl_err_t fx2 R2' M2 model2 s2 sm2 cr2 v RA2 R19' R20' SV2 MO2 W2 Hv ECV HM).
- assert (HD2 : PM.p_depth s2 <= 1024).
{ pose proof IV2 as (_ & _ & D2 & _). rewrite ES2, ES1 in D2. lia. }
apply (gl_ok_t MKE OPN OPD fx2 R2' M2 model2 s2 sm2 e2 cr2 len tb RA2 R19' R20' RL Hl TBY2 Htb SV2 MO2 W2 ECZ2 IV2 HD2); [rewrite ES2; exact ES1| lia].
Qed.
End Call.
End WithHeap.
End PMBOU8.
