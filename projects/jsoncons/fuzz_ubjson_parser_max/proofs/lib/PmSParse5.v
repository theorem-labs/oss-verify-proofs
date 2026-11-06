(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit PmParKit2 PmParStep
PmCertKitG PmSParseP PmSParseD PmSParseK Js0_code_35d98_35d9c.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSParse5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsS.PMPSS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSParseD.PMSLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1None"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LB"]; ["4Model"; "4m_halted"; "4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0R"; "0R1"; "6msteps"; "7credit"; "7hi_heap"; "7hl_sptop"; "8agree_on"; "9SCFG"]; [":ignore_spec"; ":peek_spec"; ";iter_ok"; "<cfg"; "<ec_at"; "=end_object_spec"; "=make_ec_spec"; "=read_key_spec"; ">FPState"; ">mkst"; ">seg_rom"; "?TSet"; "@srealizes"; "Amem_grows"; "Bloaded_segments"; "0SCFG_P"]; ["CIn"; "Dadd"; "Dle"; "Dlt"; "Dpow"; "Dsub"; "0bm"; "0c"; "0cr"; "0fx"; "0fx1"; "0i"; "0m"; "0model"; "0n"; "0o"]; ["0pc"; "0pc1"; "0sp"; "EZ_to_bv"; "Ebv"; "0v"; "0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia.
Module PMSLP5.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmSParse5 "Q9'R4yR0%211'4y8%511%311p051';&Nr5r4r3+@%544321&QBz%2216&QA%1296&QD+2+R0%3221%9251&Q4&Q>r8r6%45321CBr7%655413Ep031p091p0A1p0E1pS@L1pT<M1pT0N1pQ>Q01pQ<Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmSParse5 "Q4'R4yR0%211'4y8%511%311p051';'7&QBzr1%3221&QC&QD+2+R0%3221%5271%;271'8r3&R3r2%22H1%411r4%113%83G31p0:1pSHG1%;3I8:p021pQ@K1pQ<L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F.
pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B.
Qed.
Lemma tstep : ltac2:(TCodec.tc2 tcn__PmSParse5 "UL'2'6';%2211%411&K'Q8&Dy5'R4yR0%211%5241'4y8%611%311p061'@&Q;&Lv<rCrBr;&Cr9%211%8576541'8%A1C&Ar:%211(1%11H%73631%Q42JJ%Q611&B%11@(3%115%>3531&QB+SoonPPPPP0&Mv>%211%5241&QE+XPPP0%2241+T0%42N1%;231r<%=219':z%O3QJQ41'7%B2:6&QA%128Q8%E21A%5241%9271%Q73R2Q49&Q@(5r8%24R6R6Q>1rJ%53R721%O2QAQC%=2QDQ<%>2QC6%Q2221%B241%C261%G2=1'J&Q>&Q9rIrG&R3rE%22R?1&Q:%118%85763R61rHrFrD%92RF1%=5431R:6%@3?61&Q=%125R>r1%QJ2Q;1&QC&QD+2+R0%3221%5271%Q@271&9%QM2RIQJr2%R5221%QC23QM%<231%QG231%711r3%R;2S11%QI2S2S1%B231%QM231%=11r4%RA2S61rA%R02S81%I241%R4241%D11r5%Q=2SJ1%Q@11%QM12%S:3SG21p061p0>1p0E1p0N1pSHT:1rNrM%SF1Q@%SL5SK32QH1'Q<&OvQ?%211&Q3rL%26R41R>QJQIQO%74R541QIp091rK%66R8=1R6R5R3%;4R981QMp041p0B1p0QK1p0QN1p0R@1p0RO1p0S:1p0S=1p0SD1p0SK1p0T31p0T<1pS>U71p2U81pSJU91pT@U:1pSNU;1pT>U<1pT6U=1pLTM1pSLTO1pQ@U11pQ<U21pT4UB1pT2UC1pQDU:1pQBU;1pSFUB1pSDUC1pSBUE1pQ0UG1").
Proof. intros LB cr fx fx1 R R1 pc pc1 M M1 model K sp x n y m B bm.
intros HH Mh Ml TOP H1 H2 H3 H4 MS MG FRZ KONT.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R pc R1 pc1 M1
(fun a => (sp - 128 <= a < sp - 128 + 128) \/ (x <= a < x + n) \/ (y <= a < y + m)) K HH Mh Ml TOP MS MG).
- intros a Ha N. apply FRZ; [exact Ha| | |]; intros X; apply N; [left|right; left|right; right]; exact X.
- intros a Pa. destruct Pa as [Pa|[Pa|Pa]]; [unfold PMK.cwr; left; lia| unfold PMK.cwr; left; destruct H3 as [H3|H3]; lia|].
destruct H4 as [H4|(HB & H5 & H6)]; [lia|]. apply (PMK.cwr_block L LB B bm a HB). lia.
- intros a. repeat apply PMK.or_dec; apply PMK.rng_dec.
- exact KONT.
Qed.
Theorem parse_iter5 : ltac2:(TCodec.tc2 tcn__PmSParse5 "J&Q1vQ?v>v<%43321&Q0%13543&Q7%13765&Q5%13987&Q6%13;:9&Q2';'8r1+9%33421qSJ51%74CBA1p091p0<1p0?1p0B1p0E1").
Proof.
intros PK IG RK EO MKE. unfold PMSLPD.iter_ok.
intros K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI TG IH.
pose proof CTX as CTX0.
destruct CTX as (HH & MOK & K0 & ENT & FOK & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutS.ADDR_S] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
change (PMSP.pm_scr 10) with 32768 in *.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as BQ1.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as BQ8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as BQ9.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as BQ18.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as BQ19.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as BQ20.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 21))) as BQ21.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 22))) as BQ22.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 23))) as BQ23.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 24))) as BQ24.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 25))) as BQ25.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 26))) as BQ26.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 27))) as BQ27.
change (bv_modulus 64) with (2 ^ 64) in BQ1, BQ8, BQ9, BQ18, BQ19, BQ20, BQ21, BQ22, BQ23, BQ24, BQ25, BQ26, BQ27.
assert (SC0 : 0 <= 32768) by lia.
destruct LI as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & X3 & X4 & INV1 & LM1).
pose proof LM1 as LM1c.
destruct LM1 as (RPRE1 & EC1 & STEP1 & EE1 & HP1 & CK1 & MB1 & HH1 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104).
pose proof (PMFR.model_ok_but_vm model model1 MOK MB1) as MOK1. pose proof MOK1 as (Mh1 & Ml1 & _).
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 32768 sp 32768 _ STK HP1); lia).
pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1. pose proof STK1 as (_ & _ & _ & _ & SD1).
destruct RPRE1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA1, IA1, VIS1, VREF1. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S] in PA1, IA1, VIS1, VREF1.
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
assert (BRX : PMFR.brange L LBX).
{ apply (PMFR.brange_incl L LBX (PM.parser_own s ++ LBX) (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH (incl_refl _))). apply incl_appr. apply incl_refl. }
assert (WRH : forall i, PMK.inW (PMSP.W_run AD fb) i -> (fb + 8 <= i < fb + 24) \/ (fb + 48 <= i < fb + 56) \/ (fb + 320 <= i < fb + 360) \/ (fb + 376 <= i < fb + 424) \/ (fb + 480 <= i < fb + 488) \/ (fb + 592 <= i < fb + 596) \/ (0xc6260 <= i < 0xe7ec8)).
{ intros i (r0 & Hin & Hr). unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in *.
pose proof INV1 as (IM1 & ID1 & IDP1 & ISH1 & ITB1). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM1, ID1, IDP1, ISH1, ITB1.
destruct (exists_last (l := stk1) ltac:(intros E; rewrite E in ISH1; destruct ISH1 as (X & _); cbn in X; lia)) as (pre & top & Epre).
subst stk1. destruct top as [tm tl tt ti].
unfold PMSLPD.top_mode in TG. cbn [PM.p_stk] in TG. rewrite last_last in TG. cbn [PM.ps_mode] in TG.
destruct (PMPK2.top_of_shape pre (PM.PS tm tl tt ti) ISH1) as (TOK & TPOS).
pose proof PA1 as (PVP1 & PDEF1 & _ & P8 & P9 & P12 & P16 & P20 & _ & PSRC1 & _ & P328 & _ & PTB1 & PVEC1 & _).
cbn [PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk PM.p_src PM.p_tb] in P8, P9, P12, PVEC1, PSRC1, PTB1.
rewrite IM1 in P8. rewrite ID1 in P9.
pose proof PVEC1 as (VC0 & VC8 & VC16 & Hk1 & Hlen1 & Hal1 & VDB1 & _ & _ & VEL1).
rewrite length_app in Hlen1, VC8. cbn [length] in Hlen1, VC8. rewrite Nat2Z.inj_add in Hlen1, VC8. cbn [Z.of_nat Pos.of_succ_nat] in Hlen1, VC8.
assert (HT : exists T, T = vb1 + 32 * Z.of_nat (length pre)) by (eexists; reflexivity). destruct HT as (T & ET).
assert (TOPC : PM.pstate_at RSEGS M1 T (PM.PS tm tl tt ti)).
{ rewrite ET. specialize (VEL1 (length pre) ltac:(rewrite length_app; cbn; lia)). rewrite PMPK2.nth_app_at in VEL1. exact VEL1. }
pose proof TOPC as (TM0 & TL8 & TT16 & TI24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in TM0, TL8, TT16, TI24.
set (LB1 := PM.parser_own (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS tm tl tt ti])) ++ LBX) in *.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH1); apply incl_refl).
assert (VIN1 : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR1 _ _ VIN1) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (VI1 : forall a, vb1 <= a < vb1 + 32 * 2 ^ vk1 -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
assert (P2K : 0 < 2 ^ vk1) by (apply (PM.pow2_pos vk1); lia).
assert (TB : 0 <= T /\ T + 32 <= vb1 + 32 * 2 ^ vk1) by (rewrite ET; lia).
assert (TAL : T mod 16 = 0) by (rewrite ET; replace (vb1 + 32 * Z.of_nat (length pre)) with (vb1 + (Z.of_nat (length pre) * 2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal1).
assert (WT : L5.writable RSEGS M1 T 32) by (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 vb1 (32 * 2 ^ vk1)); [exact VDB1|lia|lia]|lia|lia]).
assert (WP1 : L5.writable RSEGS M1 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF1|lia|lia]).
pose proof BASE1 as (IMG1 & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG1.
pose proof EC1 as (EC1v & EC18 & EC1D).
assert (V368 : L5.u64_at RSEGS M1 (fb + 40 + 368) (T + 32)).
{ rewrite ET. replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia. replace (vb1 + 32 * Z.of_nat (length pre) + 32) with (vb1 + 32 * (Z.of_nat (length pre) + 1)) by lia. exact VC8. }
assert (V360 : L5.u64_at RSEGS M1 (fb + 40 + 360) vb1) by exact VC0.
unfold PMSP.cfg.
assert (ERRZ : forall (fx1z : FPState) (R1z : bvmap 5 word) (M1z : word -> option byte) (model1z : Model) (v : Z) (s1z : PM.pst) (sm1z : PM.strm) (e1z : bool) (cr1z : credit),
getr R1z (PMK.reg 1) = Z_to_bv 64 220584 -> getr R1z (PMK.reg 2) = Z_to_bv 64 (sp - 128) -> getr R1z (PMK.reg 8) = Z_to_bv 64 (fb + 40) ->
getr R1z (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1z (PMK.reg 10) = Z_to_bv 64 (fb + 8) -> getr R1z (PMK.reg 11) = Z_to_bv 64 v ->
getr R1z (PMK.reg 18) = Z_to_bv 64 (fb + 432) -> getr R1z (PMK.reg 19) = Z_to_bv 64 (fb + 64) -> getr R1z (PMK.reg 20) = Z_to_bv 64 10 ->
getr R1z (PMK.reg 21) = Z_to_bv 64 79444 -> getr R1z (PMK.reg 22) = Z_to_bv 64 9 -> getr R1z (PMK.reg 23) = Z_to_bv 64 256 ->
getr R1z (PMK.reg 24) = Z_to_bv 64 93 -> getr R1z (PMK.reg 25) = Z_to_bv 64 7 -> getr R1z (PMK.reg 26) = Z_to_bv 64 5 -> getr R1z (PMK.reg 27) = Z_to_bv 64 125 ->
(forall x, In x [3; 4]%nat -> getr R1z (PMK.reg x) = getr R (PMK.reg x)) -> 1 <= v <= 64 ->
PMSLPD.lmem L HI R M model LBX cr sp fb cat s str sm e M1z model1z s1z sm1z e1z cr1z ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1z R1z 0x36490 M1z model1z) K).
{ intros fx1z R1z M1z model1z v s1z sm1z e1z cr1z X1z X2z X8z X9z X10z X11z X18z X19z X20z X21z X22z X23z X24z X25z X26z X27z KS1z Hv LM1xz.
destruct LM1xz as (RPRE1z & EC1xz & STEP1z & EE1z & HP1z & CK1z & MB1z & HH1z & C8z & C16z & C24z & C32z & C40z & C48z & C56z & C64z & C72z & C80z & C88z & C96z & C104z).
pose proof EC1xz as (_ & _ & ED1z).
pose proof (PMFR.model_ok_but_vm model model1z MOK MB1z) as MOK1z. pose proof MOK1z as (Mh1z & Ml1z & _).
destruct RPRE1z as (PA1z & IA1z & VIS1z & VREF1z & BASE1z & ERR1z & TB1z).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA1z, IA1z, VIS1z, VREF1z. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA1z, IA1z, VIS1z, VREF1z.
set (LB1z := PM.parser_own s1z ++ LBX) in *.
assert (BR1z : PMFR.brange L LB1z) by (apply (PMFR.brange_of_heap L HI HIok LB1z LB1z cr1z M1z _ HH1z); apply incl_refl).
assert (STK1z : L5C.stk (hl_sptop L) M1z sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M M1z sp 32768 sp 32768 _ STK HP1z); lia).
assert (STKcz : L5C.stk (hl_sptop L) M1z (sp - 128) 14336).
{ apply (PMK.stk_call L M1z sp 32768 (sp - 128) 14336 STK1z); [lia|lia|lia|]. replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.make_ec_spec, PMSP.make_ec_spec in MKE. cbn [pa_make_ec AD PmLayoutS.ADDR_S] in MKE.
apply (MKE fx1z R1z M1z model1z K LB1z cr1z (fb + 8) v (sp - 128) 220584 e1z HH1z MOK1z K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1z|]. split; [split; [lia| reflexivity]|]. split; [exact X2z|].
split; [rewrite (KS1z 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1z 4%nat) by PMK.inl; exact Rtp|]. exact STKcz. }
{ rewrite L5K.rl10. exact X10z. } { rewrite L5K.rl11. exact X11z. } { exact Hv. } { lia. } { lia. } { exact AL1. }
{ exact ED1z. } { exact BASE1z. } { exact ERR1z. }
intros fx2z R2z M2z RP2z EC2z ERR2z HP2z HH2z.
change (PMSP.pm_scr 1) with 14336 in HP2z.
set (WEz := (fb + 8, 16) :: (if e1z then [] else PMSP.err_W AD)) in HP2z.
assert (WCEz : forall a, PMK.inW WEz a -> (fb + 8 <= a < fb + 24) \/ (0xc6260 <= a < 0xc6262) \/ (0xe7ca8 <= a < 0xe7ec8)).
{ intros a (r0 & Hin & Hr). unfold WEz in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|]. destruct e1z; [destruct Hin|].
unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; right; [left|right]; lia. }
assert (WHIEz : forall a, PMK.inW WEz a -> (sp - 128) <= a \/ hl_img_lo L <= a < hl_img_hi L).
{ intros a I. apply WCEz in I. rewrite (ly_img_lo L LY), (ly_img_hi L LY). destruct I as [I|[I|I]]; [left; lia| right; lia| right; lia]. }
assert (EKcz : PMK.ek L LB1z (sp - 128) 14336 WEz M1z M2z) by (apply (PMK.ek_of_hpres L); exact HP2z).
assert (SCcz : 0 <= 14336) by lia.
assert (HI2z : forall a n, sp - 128 <= a -> a + n <= fb + 8 -> L5C.agree_on M1z M2z a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1z (sp - 128) 14336 WEz M1z M2z EKcz STKcz SCcz a n H1); [lia|]. intros i Hi I. apply WCEz in I.
clear - Hi H1 H2 I SLO STOP. lia. }
assert (HI2'z : forall a n, fb + 24 <= a -> a + n <= fb + 752 -> L5C.agree_on M1z M2z a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB1z (sp - 128) 14336 WEz M1z M2z EKcz STKcz SCcz a n); [lia|lia|]. intros i Hi I. apply WCEz in I.
clear - Hi H1 H2 I F1 F2 SLO STOP. lia. }
assert (STK2z : L5C.stk (hl_sptop L) M2z sp 32768) by (apply (PMK.stk_after RSEGS L KL LB1z M1z M2z sp 32768 (sp - 128) 14336 WEz STK1z HP2z); lia).
pose proof (L5C.stk_writable RSEGS _ M2z sp 32768 STK2z) as WR2z.
destruct s1z as [mo1z dn1z dp1z src1z tb1z tg1z vb1z vk1z stk1z].
assert (QIN1z : In (PM.sr_qc src1z, 16384) LB1z) by (unfold LB1z, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN1z : In (vb1z, 32 * 2 ^ vk1z) LB1z) by (unfold LB1z, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR1z _ _ VIN1z) as (W0z & W1'z & W4z). unfold hl_ceil in W4z.
assert (VI1z : forall a, vb1z <= a < vb1z + 32 * 2 ^ vk1z -> ~ (65536 <= a < 954368)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'z. intros a Ha. clear - Ha W1'z. lia. }
assert (PA2z : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M2z (fb + 40) (fb + 440) (PM.PST mo1z dn1z dp1z src1z tb1z tg1z vb1z vk1z stk1z)).
{ apply (PMPK.parser_at_keep RSEGS AD M1z M2z (fb + 40) (fb + 440) _ PA1z); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply HI2'z; lia.
- apply (PMPK.dkr_hpres_blk RSEGS L KL LB1z (sp - 128) 14336 WEz M1z M2z (PM.sr_qc src1z) 16384 HP2z QIN1z BR1z). lia.
- lia.
- clear - W4z STOP. unfold hl_ceil in *. lia.
- apply (PMPK.ag_blk RSEGS L KL LB1z (sp - 128) 14336 WEz M1z M2z EKcz STKcz BR1z vb1z (32 * 2 ^ vk1z) VIN1z).
intros i Hi I. apply WCEz in I. destruct I as [I|I]; [clear - Hi I W4z SLO F1; unfold hl_ceil in *; lia| apply (VI1z i Hi); clear - I; lia].
- intros c0 n0 q0 E0. apply (PMPK.dkr_hpres_blk RSEGS L KL LB1z (sp - 128) 14336 WEz M1z M2z q0 c0 HP2z); [|exact BR1z|lia].
unfold LB1z, PM.parser_own, PM.vs_own. cbn [PM.p_tb]. rewrite E0. cbn. right. right. left. reflexivity. }
assert (SINC1z : incl (PM.vs_own str) LB1z) by (unfold LB1z; apply incl_appr; exact INCS).
assert (IA2z : PM.iss_at RSEGS AD PMSP.T3 M2z (fb + 440) str sm1z).
{ apply (PMFR.iss_keep RSEGS AD L KL LB1z (sp - 128) 14336 WEz M1z M2z EKcz STKcz SCcz BR1z WHIEz); [lia|lia| |exact SINC1z| exact IA1z].
intros i Hi I. apply WCEz in I. clear - Hi I F1 F2 SLO STOP. lia. }
assert (BASE2z : PMST.base_ok RSEGS AD M2z).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1z (sp - 128) 14336 WEz M1z M2z EKcz); [| | | | exact BASE1z].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCEz in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha.
all: clear - I Ha SLO STOP F1; lia. }
assert (HP02z : L5C.hpres L LBX sp 32768 (PMSP.W_run AD fb) M M2z).
{ apply (PMK.hpres_of L LBX sp 32768 _ M M2z).
- apply (PMK.ek_trans L LBX sp 32768 _ M M1z M2z (PMK.ek_of_hpres L LBX sp 32768 _ M M1z HP1z)).
apply (PMK.ek_callee_in' RSEGS L KL LBX LB1z sp 32768 (sp - 128) 14336 _ WEz M1z M2z HP2z); [unfold LB1z; apply incl_appr; apply incl_refl|lia|lia|unfold hl_ceil; lia|lia|
exact (PMFR.brange_hi L LBX (PMFR.brange_incl L LBX LB1z BR1z ltac:(unfold LB1z; apply incl_appr; apply incl_refl)))|].
intros a I. right. apply WCEz in I. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S app].
destruct I as [I|[I|I]]; [do 6 apply PMK.inW_next; apply PMK.inW_here; lia| do 7 apply PMK.inW_next; apply PMK.inW_here; lia| do 8 apply PMK.inW_next; apply PMK.inW_here; lia].
- destruct STK2z as (_ & _ & _ & _ & D2). exact D2.
- apply (PMK.dk_trans L LBX sp 32768 M M1z M2z (PMK.dk_of_hpres L LBX sp 32768 _ M M1z HP1z)).
apply (PMK.dk_callee L LBX LB1z sp 32768 (sp - 128) 14336 WEz M1z M2z HP2z); [unfold LB1z; apply incl_appr; apply incl_refl|lia|lia]. }
assert (VIS2z : L5.u64_at RSEGS M2z (fb + 432) (pa_vp_visitor AD)) by (unfold PMSP.visitor_at in VIS1z; apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2'z; lia|lia|lia| exact VIS1z]).
assert (VREF2z : L5.u64_at RSEGS M2z (fb + 40 + 384) (fb + 432)) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2'z; lia|lia|lia| exact VREF1z]).
assert (RP2z_ : forall k, In k PMK.cs_all -> getr R2z (PMK.reg k) = getr R1z (PMK.reg k)) by (intros k Hk; apply (PMK.cs_of_preserved R1z R2z k RP2z Hk)).
assert (D8 : L5.u64_at RSEGS M2z (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C8z]).
assert (D16 : L5.u64_at RSEGS M2z (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C16z]).
assert (D24 : L5.u64_at RSEGS M2z (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C24z]).
assert (D32 : L5.u64_at RSEGS M2z (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C32z]).
assert (D40 : L5.u64_at RSEGS M2z (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C40z]).
assert (D48 : L5.u64_at RSEGS M2z (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C48z]).
assert (D56 : L5.u64_at RSEGS M2z (sp - 56) (bv_unsigned (getr R (PMK.reg 21)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C56z]).
assert (D64 : L5.u64_at RSEGS M2z (sp - 64) (bv_unsigned (getr R (PMK.reg 22)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C64z]).
assert (D72 : L5.u64_at RSEGS M2z (sp - 72) (bv_unsigned (getr R (PMK.reg 23)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C72z]).
assert (D80 : L5.u64_at RSEGS M2z (sp - 80) (bv_unsigned (getr R (PMK.reg 24)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C80z]).
assert (D88 : L5.u64_at RSEGS M2z (sp - 88) (bv_unsigned (getr R (PMK.reg 25)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C88z]).
assert (D96 : L5.u64_at RSEGS M2z (sp - 96) (bv_unsigned (getr R (PMK.reg 26)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C96z]).
assert (D104 : L5.u64_at RSEGS M2z (sp - 104) (bv_unsigned (getr R (PMK.reg 27)))) by (apply (L5C.u64_at_agree RSEGS M1z M2z); [apply HI2z; lia|lia|lia| exact C104z]).
pose proof BASE2z as (IMG2z & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG2z.
assert (WP2z : L5.writable RSEGS M2z (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [destruct PA2z as (_ & X & _); exact X|lia|lia]).
unfold PMSP.visitor_at in VIS2z. cbn [pa_vp_visitor AD PmLayoutS.ADDR_S] in VIS2z.
cfeed P (PMSLPP.lpZ_conc fx2z R2z M2z (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8)
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20))
| 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23))
| 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26))
| 52%nat => bv_unsigned (getr R (PMK.reg 27)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3z & R3z & M3z & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3z & _ & FRZ3z & MS3z & KS3z & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & Z8)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27.
apply (tstep LB1z cr1z fx2z fx3z R2z R3z 0x35da8 0x35d98 M2z M3z model1z K sp (fb + 40 + 8) 1 0 0 0 0 HH2z Mh1z Ml1z ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)
ltac:(right; unfold hl_ceil; lia) ltac:(left; reflexivity) MS3z MG3z (fun i Hi _ N2 _ => FRZ3z i Hi N2)).
intros HH3z.
assert (AG3z : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M2z M3z a n).
{ intros a n H1 H2 H4 i Hi. apply FRZ3z; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
assert (EK3z : PMK.ek L LB1z sp 32768 [(fb + 48, 1)] M2z M3z).
{ apply (PMK.ek_piece_in RSEGS L KL LB1z sp 32768 [(fb + 48, 1)] M2z M3z (fun a => fb + 48 <= a < fb + 49) ltac:(intros a Ha N; apply FRZ3z; [exact Ha| intros X; apply N; lia])
STK2z (PMFR.brange_hi L LB1z BR1z)). intros a Ha. right. apply PMK.inW_here. lia. }
assert (STK3z : L5C.stk (hl_sptop L) M3z sp 32768) by (apply (PMK.stk_grows L M2z M3z sp 32768 MG3z STK2z)).
destruct (BR1z _ _ VIN1z) as (W0y & W1y & W4y). unfold hl_ceil in W4y.
apply (PMSLPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fx3z R3z M3z model1z (PMPK.set_more (PM.PST mo1z dn1z dp1z src1z tb1z tg1z vb1z vk1z stk1z) 0) sm1z true cr1z CTX0).
- intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | assumption | (rewrite (KS3z _) by PMK.inl; rewrite RP2z_ by PMK.inl; apply KS1z; PMK.inl) ] |]).
destruct Hk.
- exact T1.
- unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutS.ADDR_S].
split.
{ apply (PMPK.parser_more_upd RSEGS AD M2z M3z (fb + 40) (fb + 440) _ 0 PA2z); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG3z; lia.
- apply AG3z; lia.
- apply PMPK.dkr_grows. exact MG3z.
- exact Z8.
- left. reflexivity.
- apply PMPK.dkr_grows. exact MG3z.
- lia.
- clear - W4y STOP. unfold hl_ceil in *. lia.
- apply AG3z; [lia|clear - W4y STOP; unfold hl_ceil in *; lia| clear - W4y SLO F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG3z. }
split.
{ apply (PMF.iss_at_agree RSEGS AD M2z M3z (fb + 440) str sm1z); [lia|lia| apply AG3z; lia| |exact IA2z].
intros c0 n0 q0 Es. assert (HQ : In (q0, c0) LBX) by (apply INCS; rewrite Es; cbn; left; reflexivity).
destruct (BRX _ _ HQ) as (Z0 & _ & Z4). unfold hl_ceil in Z4. apply AG3z; [lia|clear - Z4 STOP; lia| clear - Z4 SLO F1; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M2z M3z); [apply AG3z; lia|lia|lia| exact VIS2z]|].
split; [apply (L5C.u64_at_agree RSEGS M2z M3z); [apply AG3z; lia|lia|lia| exact VREF2z]|].
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1z sp 32768 [(fb + 48, 1)] M2z M3z EK3z); [| | | | exact BASE2z].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in Ha; clear - I Ha SLO STOP F1; lia. }
split; [|exact TB1z].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1z sp 32768 [(fb + 48, 1)] M2z M3z EK3z); [| | exact ERR2z].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutS.ADDR_S] in Ha; clear - I Ha SLO STOP F1; lia. }
- pose proof EC2z as (_ & _ & EDx). apply (L5C.defined_agree M2z M3z (fb + 8) 16); [apply AG3z; lia| exact EDx].
- split; [exact STEP1z|]. split; [intros _; reflexivity|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M M3z).
- apply (PMK.ek_trans L LBX sp 32768 _ M M2z M3z (PMK.ek_of_hpres L LBX sp 32768 _ M M2z HP02z)).
apply (PMK.ek_weaken L LBX LB1z sp 32768 sp 32768 _ [(fb + 48, 1)] M2z M3z EK3z); [unfold LB1z; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
unfold PMSP.W_run, PMSP.o_p in O. cbn [pa_off_p AD PmLayoutS.ADDR_S app] in O. apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- destruct STK3z as (_ & _ & _ & _ & D3). exact D3.
- apply (PMK.dk_trans L LBX sp 32768 M M2z M3z (PMK.dk_of_hpres L LBX sp 32768 _ M M2z HP02z)). apply (PMK.dk_grows L LBX sp 32768 M2z M3z MG3z). }
split; [exact CK1z|]. split; [exact MB1z|]. split; [exact HH3z|].
unfold PMSLPD.lslots. repeat split; (apply (L5C.u64_at_agree RSEGS M2z M3z); [apply AG3z; lia|lia|lia|]); assumption. }
cbn beta in TG. rewrite TG in *.
-
assert (NB : ~ PM.mode_bottom 9) by (unfold PM.mode_bottom; lia).
destruct TPOS as [(Pnil & BB)|(PNE & _)]; [exfalso; apply NB; exact BB|].
assert (IB : tl = 0 /\ 0 <= ti <= 2 ^ 24) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn in TOK; lia).
destruct IB as (TL0 & IB). subst tl.
cfeed P (PMSLPP.lpH9_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_10 & Xa_11)); PMK.pvz_clrT.
assert (Ma = M1) as -> by (apply mem_eq_of_frz; exact FRZa).
apply (PMK.spiece_ro RSEGS model1 fx1 fxa R1 0x35b20 Ra 0x3643c M1 K Mh1 Ml1 MSa).
assert (STKpPK : L5C.stk (hl_sptop L) M1 (sp - 128) 20480).
{ pose proof LM1c as (_ & _ & _ & _ & HPx & _). apply (PMK.stk_call L M1 sp 32768 (sp - 128) 20480); [apply (PMK.stk_after RSEGS L KL LBX M M1 sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMPSS.peek_spec, PMPS.peek_spec, PMPS.src_spec in PK. cbn [pa_peek AD PmLayoutS.ADDR_S] in PK.
apply (PK fxa Ra M1 model1 K LBX cr1 (sp - 128) 220024 fb (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) str sm1 [] HH1 MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKpPK. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. PMK.rk. }
{ exact I. } { reflexivity. }
{ pose proof LM1c as (RPx & _). destruct RPx as (PAx & _). exact PAx. }
{ pose proof LM1c as (RPx & _). destruct RPx as (_ & IAx & _). exact IAx. }
{ pose proof LM1c as (RPx & _). destruct RPx as (_ & _ & _ & _ & BASEx & _). exact BASEx. }
{ exact INCS. }
intros fxq Rq Mq srcq smq RPq PAqx IAqx STEPq RESq HPq HHq. destruct srcq as [qcq deq remq]. change (PMSP.pm_scr 4) with 20480 in HPq.
destruct (PMSLPK.lp_lift_src L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M1 model1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) sm1 e1 cr1 Mq qcq deq remq smq 4 CTX0 LM1c ltac:(lia) ltac:(lia) HPq PAqx IAqx STEPq HHq) as (LMq & AGfq).
pose proof LMq as (RPREq & ECq & LRq). pose proof ECq as (ECqv & _ & ECqD).
pose proof LRq as (_ & _ & _ & _ & _ & _ & SLq). unfold PMSLPD.lslots in SLq.
destruct SLq as (D8q & D16q & D24q & D32q & D40q & D48q & D56q & D64q & D72q & D80q & D88q & D96q & D104q).
pose proof LRq as (_ & _ & _ & _ & _ & HHql & _).
pose proof LRq as (_ & _ & HPxq & _). assert (STKqx : L5C.stk (hl_sptop L) Mq sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M Mq sp 32768 sp 32768 _ STK HPxq); lia).
pose proof (L5C.stk_writable RSEGS _ Mq sp 32768 STKqx) as WRq.
destruct (PMSLPK.RUNF2 Mq fb _ str _ _ RPREq) as (VISq & P16q & PDq & IMGq & PAq & IAq & UNq).
assert (WPq : L5.writable RSEGS Mq (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDq|lia|lia]).
pose proof PAq as (_ & _ & _ & P8qx & P9qx & _ & _ & _ & _ & _ & _ & P328q & _ & _ & PVECq & _). cbn [PMPS.with_src PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done] in PVECq, P8qx, P9qx.
pose proof PVECq as (_ & VC8q & _ & _ & _ & _ & _ & _ & _ & VELq).
assert (TOPq : PM.pstate_at RSEGS Mq T (PM.PS 9 0 tt ti)).
{ rewrite ET. specialize (VELq (length pre) ltac:(rewrite length_app; cbn; lia)). rewrite PMPK2.nth_app_at in VELq. exact VELq. }
pose proof TOPq as (TM0q & TL8q & TT16q & TI24q). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in TM0q, TL8q, TT16q, TI24q.
assert (V368q : L5.u64_at RSEGS Mq (fb + 40 + 368) (T + 32)).
{ rewrite ET. rewrite length_app in VC8q. cbn [length] in VC8q. rewrite Nat2Z.inj_add in VC8q. cbn [Z.of_nat Pos.of_succ_nat] in VC8q.
replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia. replace (vb1 + 32 * Z.of_nat (length pre) + 32) with (vb1 + 32 * (Z.of_nat (length pre) + 1)) by lia. exact VC8q. }
assert (MXq : L5.u64_at RSEGS Mq (fb + 40 + 328) 16777216) by (unfold PM.MAX_ITEMS in P328q; exact P328q).
assert (WTq : L5.writable RSEGS Mq T 32).
{ pose proof PVECq as (_ & _ & _ & _ & _ & _ & VDBx & _). apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub Mq vb1 (32 * 2 ^ vk1)); [exact VDBx|clear - TB ET; lia|clear - TB ET; lia]|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia]. }
rewrite IM1 in P8qx. rewrite ID1 in P9qx.
destruct RESq as (CONSq & [A256|(c & Hc & Ac & REMq)]).
1: {
cfeed P (PMSLPP.lpP9e_conc fxq Rq Mq (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_1 & Xb_10 & Xb_11)); PMK.pvz_clrT.
assert (Mb = Mq) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (PMK.spiece_ro RSEGS model1 fxq fxb Rq 220024 Rb 0x36490 Mq K Mh1 Ml1 MSb).
apply (ERRZ fxb Rb Mq model1 1 (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) smq e1 cr1 Xb_1 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Xb_10 Xb_11 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx) ltac:(lia) LMq).
}
destruct (Z.eq_dec c 125) as [->|NM].
1: {
cfeed P (PMSLPP.lpP9c_conc fxq Rq Mq (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_1 & Xb_10 & Xb_11)); PMK.pvz_clrT.
assert (Mb = Mq) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (PMK.spiece_ro RSEGS model1 fxq fxb Rq 220024 Rb 0x36528 Mq K Mh1 Ml1 MSb).
assert (STKpIG : L5C.stk (hl_sptop L) Mq (sp - 128) 20480).
{ pose proof LMq as (_ & _ & _ & _ & HPx & _). apply (PMK.stk_call L Mq sp 32768 (sp - 128) 20480); [apply (PMK.stk_after RSEGS L KL LBX M Mq sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMPSS.ignore_spec, PMPS.ignore_spec, PMPS.src_spec in IG. cbn [pa_ignore AD PmLayoutS.ADDR_S] in IG.
apply (IG fxb Rb Mq model1 K LBX cr1 (sp - 128) 220052 fb (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) str smq [] HHql MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKpIG. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutS.ADDR_S]. PMK.rk. }
{ unfold PMPS.ignore_args. rewrite L5K.rl11. PMK.rk. } { reflexivity. }
{ pose proof LMq as (RPx & _). destruct RPx as (PAx & _). exact PAx. }
{ pose proof LMq as (RPx & _). destruct RPx as (_ & IAx & _). exact IAx. }
{ pose proof LMq as (RPx & _). destruct RPx as (_ & _ & _ & _ & BASEx & _). exact BASEx. }
{ exact INCS. }
intros fxg Rg Mg srcg smg RPg PAgx IAgx STEPg RESg HPg HHg. destruct srcg as [qcg deg remg]. change (PMSP.pm_scr 4) with 20480 in HPg.
destruct (PMSLPK.lp_lift_src L HI LY HIok K R M model LBX cr sp r fb cat s str sm e Mq model1 (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) smq e1 cr1 Mg qcg deg remg smg 4 CTX0 LMq ltac:(lia) ltac:(lia) HPg PAgx IAgx STEPg HHg) as (LMg & AGfg).
pose proof LMg as (RPREg & ECg & LRg). pose proof ECg as (ECgv & _ & ECgD).
pose proof LRg as (_ & _ & _ & _ & _ & _ & SLg). unfold PMSLPD.lslots in SLg.
destruct SLg as (D8g & D16g & D24g & D32g & D40g & D48g & D56g & D64g & D72g & D80g & D88g & D96g & D104g).
pose proof LRg as (_ & _ & _ & _ & _ & HHgl & _).
pose proof LRg as (_ & _ & HPxg & _). assert (STKgx : L5C.stk (hl_sptop L) Mg sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M Mg sp 32768 sp 32768 _ STK HPxg); lia).
pose proof (L5C.stk_writable RSEGS _ Mg sp 32768 STKgx) as WRg.
destruct (PMSLPK.RUNF2 Mg fb _ str _ _ RPREg) as (VISg & P16g & PDg & IMGg & PAg & IAg & UNg).
assert (WPg : L5.writable RSEGS Mg (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDg|lia|lia]).
destruct RESg as (_ & RESg). specialize (RESg REMq). unfold PMSP.consumed in CONSq, RESg. cbn [PMPS.with_src PM.p_src] in CONSq, RESg.
cfeed P (PMSLPP.lpI9_conc fxg Rg Mg (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_1 & Xc_10 & Xc_11 & Xc_12)); PMK.pvz_clrT.
assert (Mc = Mg) as -> by (apply mem_eq_of_frz; exact FRZc).
apply (PMK.spiece_ro RSEGS model1 fxg fxc Rg 0x35b94 Rc 0x366c8 Mg K Mh1 Ml1 MSc).
destruct LMg as (RPRE1c & EC1c & LR1c). pose proof HHgl as HH1x.
assert (STKc : L5C.stk (hl_sptop L) Mg (sp - 128) 14336).
{ pose proof LR1c as (_ & _ & HPx & _). apply (PMK.stk_call L Mg sp 32768 (sp - 128) 14336); [apply (PMK.stk_after RSEGS L KL LBX M Mg sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.end_object_spec, PMSP.end_object_spec, PMSP.run_spec, PMSP.run_spec_r in EO. cbn [pa_end_object AD PmLayoutS.ADDR_S] in EO.
apply (EO fxc Rc Mg model1 K LBX cr1 (sp - 128) 220068 fb cat (PMPS.with_src (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) (PM.SRC qcg deg remg)) str smg e1 HH1x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args_end, PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutS.ADDR_S PMPS.with_src PM.p_stk]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [split; [PMK.rk|]; split; [PMK.rk| PMK.rk]|]. rewrite length_app. cbn [length]. destruct pre as [|x pre']; [exfalso; apply PNE; reflexivity| cbn [length]; lia]. }
{ exact RPRE1c. } { exact INCS. } { exact INV1. } { exact EC1c. }
{ pose proof LR1c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR1c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 1) with 14336 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMSLPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PMPS.with_src (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) (PM.SRC qcg deg remg)) smg e1 cr1 M2 model2 s2 sm2 e2 cr2 14336 CTX0 LR1c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMSLPD.lslots in SL2. destruct SL2 as (D82 & D162 & D242 & D322 & D402 & D482 & D562 & D642 & D722 & D802 & D882 & D962 & D1042).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMSLPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P162 & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
pose proof PA2 as (_ & _ & _ & P82 & P92 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B12 & B22 & _).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)].
2: {
pose proof EC2 as (EC2v & _). pose proof INV2 as (IM2 & ID2 & _). rewrite ID2 in P92. rewrite IM2 in P82.
cfeed P (PMSLPP.lpD0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxy & Ry & My & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGy & _ & FRZy & MSy & KSy & Xy_10)); PMK.pvz_clrT.
assert (My = M2) as -> by (apply mem_eq_of_frz; exact FRZy).
apply (PMK.spiece_ro RSEGS model2 fx2 fxy R2 0x35ba4 Ry 0x35b20 M2 K Mh2 Ml2 MSy).
apply (IH fxy Ry M2 model2 s2 sm2 e2 cr2).
+ unfold PMSLPD.linv. do 13 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INV2|].
split; [exact RPRE2|]. split; [exact EC2| exact LR2].
+ destruct PV2 as ((top0 & Etop) & UE). pose proof INV2 as (_ & _ & _ & SH2 & _). eapply PMPK2.lp_mu_lt_U; [exact ISH1| exact SH2| exact UN2| unfold PM.unread in *; cbn [PMPS.with_src PM.p_src] in UE |- *; lia].
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutS.ADDR_S] in ECvv, ECvD.
cfeed P (PMSLPP.lpDe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxz & Rz & Mz & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGz & _ & FRZz & MSz & KSz & Xz_1 & Xz_2 & Xz_8 & Xz_9 & Xz_10 & Xz_18 & Xz_19 & Xz_20 & Xz_21 & Xz_22 & Xz_23 & Xz_24 & Xz_25 & Xz_26 & Xz_27)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xz_1.
try rewrite PMPK.word_id in Xz_2.
try rewrite PMPK.word_id in Xz_8.
try rewrite PMPK.word_id in Xz_9.
try rewrite PMPK.word_id in Xz_10.
try rewrite PMPK.word_id in Xz_18.
try rewrite PMPK.word_id in Xz_19.
try rewrite PMPK.word_id in Xz_20.
try rewrite PMPK.word_id in Xz_21.
try rewrite PMPK.word_id in Xz_22.
try rewrite PMPK.word_id in Xz_23.
try rewrite PMPK.word_id in Xz_24.
try rewrite PMPK.word_id in Xz_25.
try rewrite PMPK.word_id in Xz_26.
try rewrite PMPK.word_id in Xz_27.
assert (Mz = M2) as -> by (apply mem_eq_of_frz; exact FRZz).
apply (PMK.spiece_ro RSEGS model2 fx2 fxz R2 0x35ba4 Rz 0x35d98 M2 K Mh2 Ml2 MSz).
apply (PMSLPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxz Rz M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xz_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
}
assert (CB : 0 <= c <= 255 /\ c <> 125) by lia.
destruct (Z_lt_le_dec c 125) as [CL|CH]; destruct (Z.eq_dec ti (2 ^ 24)) as [IX|IX].
*
assert (TI24x : L5.u64_at RSEGS Mq (T + 24) (2 ^ 24)) by (rewrite <- IX; exact TI24q).
cfeed P (PMSLPP.lpP9lx_conc fxq Rq Mq (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 55%nat => c | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxd & Rd & Md & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGd & _ & FRZd & MSd & KSd & Xd_1 & Xd_10 & Xd_11 & Xd_12 & Od_1)); PMK.pvz_clrT.
apply (tstep (PM.parser_own (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) ++ LBX) cr1 fxq fxd Rq Rd 220024 0x36490 Mq Md model1 K sp 0 0 (T + 24) 8 vb1 (32 * 2 ^ vk1) HHql Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| clear - TB ET; lia]) MSd MGd (fun i Hi _ _ N3 => FRZd i Hi N3)).
intros HHd.
assert (PTd : PM.pstate_at RSEGS Md (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 9 0 tt (2 ^ 24 + 1))).
{ rewrite <- ET. split; [apply (PMF.u32_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TM0q]|].
split; [apply (L5C.u64_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8q]|].
split; [apply (L5C.u8_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16q]|].
replace (2 ^ 24 + 1) with 16777217 by reflexivity. exact Od_1. }
pose proof (PMSLPK.lp_headw_mem L HI LY HIok K R M model LBX cr sp r fb cat s str sm e Mq model1 mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 pre (PM.PS 9 0 tt ti) smq e1 cr1 Md (PM.PS 9 0 tt (2 ^ 24 + 1)) CTX0 LMq MGd (fun i Hi N => FRZd i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHd PTd) as LMd.
apply (ERRZ fxd Rd Md model1 13 (PM.PST mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 0 tt (2 ^ 24 + 1))])) smq e1 cr1 Xd_1 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Xd_10 Xd_11 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx) ltac:(lia) LMd).
*
cfeed P (PMSLPP.lpP9l_conc fxq Rq Mq (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 39%nat => ti | 55%nat => c | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxd & Rd & Md & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGd & _ & FRZd & MSd & KSd & Xd_1 & Xd_10 & Xd_11 & Xd_12 & Od_1)); PMK.pvz_clrT.
apply (tstep (PM.parser_own (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) ++ LBX) cr1 fxq fxd Rq Rd 220024 0x365f0 Mq Md model1 K sp 0 0 (T + 24) 8 vb1 (32 * 2 ^ vk1) HHql Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| clear - TB ET; lia]) MSd MGd (fun i Hi _ _ N3 => FRZd i Hi N3)).
intros HHd.
assert (PTd : PM.pstate_at RSEGS Md (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 9 0 tt (ti + 1))).
{ rewrite <- ET. split; [apply (PMF.u32_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TM0q]|].
split; [apply (L5C.u64_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8q]|].
split; [apply (L5C.u8_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16q]|].
exact Od_1. }
destruct (PMSLPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e Mq model1 mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 pre (PM.PS 9 0 tt ti) smq e1 cr1 Md (PM.PS 9 0 tt (ti + 1)) CTX0 LMq INV1 MGd (fun i Hi N => FRZd i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHd PTd ltac:(clear - TOK IB IX; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVd & LMd).
destruct LMd as (RPRE7c & EC7c & LR7c). pose proof HHd as HH7x.
assert (STKc : L5C.stk (hl_sptop L) Md (sp - 128) 26624).
{ pose proof LR7c as (_ & _ & HPx & _). apply (PMK.stk_call L Md sp 32768 (sp - 128) 26624); [apply (PMK.stk_after RSEGS L KL LBX M Md sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.read_key_spec, PMSP.read_key_spec, PMSP.run_spec, PMSP.run_spec_r in RK. cbn [pa_read_key AD PmLayoutS.ADDR_S] in RK.
apply (RK fxd Rd Md model1 K LBX cr1 (sp - 128) 220436 fb cat (PM.PST mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 0 tt (ti + 1))])) str smq e1 HH7x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutS.ADDR_S]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPRE7c. } { exact INCS. } { exact INVd. } { exact EC7c. }
{ pose proof LR7c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR7c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 7) with 26624 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMSLPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PM.PST mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 0 tt (ti + 1))])) smq e1 cr1 M2 model2 s2 sm2 e2 cr2 26624 CTX0 LR7c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMSLPD.lslots in SL2. destruct SL2 as (D82 & D162 & D242 & D322 & D402 & D482 & D562 & D642 & D722 & D802 & D882 & D962 & D1042).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMSLPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P162 & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
pose proof PA2 as (_ & _ & _ & P82 & P92 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B12 & B22 & _).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PK2)].
2: {
pose proof EC2 as (EC2v & _). pose proof INV2 as (IM2 & ID2 & _). rewrite ID2 in P92. rewrite IM2 in P82.
destruct PK2 as (SK2 & UK2).
destruct s2 as [mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 stk2]. cbn [PM.p_stk PM.p_src PM.p_b PM.p_k PM.p_tb PM.p_tg PM.p_more PM.p_done PM.p_depth] in *.
subst stk2.
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC2 & _). cbn [PM.p_b PM.p_k PM.p_stk] in PVEC2.
pose proof PVEC2 as (WC0 & WC8 & _ & Hk2 & Hlen2 & Hal2 & VDB2 & _ & _ & VEL2).
rewrite length_app in Hlen2, WC8. cbn [length] in Hlen2, WC8. rewrite Nat2Z.inj_add in Hlen2, WC8. cbn [Z.of_nat Pos.of_succ_nat] in Hlen2, WC8.
assert (HT2 : exists T2, T2 = vb2 + 32 * Z.of_nat (length pre)) by (eexists; reflexivity). destruct HT2 as (T2 & ET2).
assert (TOPC2 : PM.pstate_at RSEGS M2 T2 (PM.PS 9 0 tt (ti + 1))).
{ rewrite ET2. specialize (VEL2 (length pre) ltac:(rewrite length_app; cbn; lia)). rewrite PMPK2.nth_app_at in VEL2. exact VEL2. }
pose proof TOPC2 as (TM02 & TL82 & TT162 & TI242). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in TM02, TL82, TT162, TI242.
set (LB2 := PM.parser_own (PM.PST mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 (pre ++ [(PM.PS 9 0 tt (ti + 1))])) ++ LBX) in *.
assert (BR2 : PMFR.brange L LB2) by (apply (PMFR.brange_of_heap L HI HIok LB2 LB2 cr2 M2 _ HH2); apply incl_refl).
assert (VIN2 : In (vb2, 32 * 2 ^ vk2) LB2) by (unfold LB2, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR2 _ _ VIN2) as (W0b & W1b & W4b). unfold hl_ceil in W4b.
assert (P2K2 : 0 < 2 ^ vk2) by (apply (PM.pow2_pos vk2); lia).
assert (TB2 : 0 <= T2 /\ T2 + 32 <= vb2 + 32 * 2 ^ vk2) by (rewrite ET2; clear - Hlen2 W0b; lia).
assert (TAL2 : T2 mod 16 = 0) by (rewrite ET2; replace (vb2 + 32 * Z.of_nat (length pre)) with (vb2 + (Z.of_nat (length pre) * 2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal2).
assert (WT2 : L5.writable RSEGS M2 T2 32) by (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 vb2 (32 * 2 ^ vk2)); [exact VDB2|clear - TB2 ET2; lia|clear - TB2 ET2; lia]|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia]).
assert (V3682 : L5.u64_at RSEGS M2 (fb + 40 + 368) (T2 + 32)).
{ rewrite ET2. replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia. replace (vb2 + 32 * Z.of_nat (length pre) + 32) with (vb2 + 32 * (Z.of_nat (length pre) + 1)) by lia. exact WC8. }
cfeed P (PMSLPP.lpK90_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T2 | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL2]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_10 & Oc_1)); PMK.pvz_clrT.
apply (tstep LB2 cr2 fx2 fxc R2 Rc 0x35d14 0x35b20 M2 Mc model2 K sp 0 0 (T2 + 0) 4 vb2 (32 * 2 ^ vk2) HH2 Mh2 Ml2 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [exact VIN2| clear - TB2 ET2; lia]) MSc MGc (fun i Hi _ _ N3 => FRZc i Hi N3)).
intros HHc.
assert (PTc : PM.pstate_at RSEGS Mc (vb2 + 32 * Z.of_nat (length pre)) (PM.PS 10 0 tt (ti + 1))).
{ rewrite <- ET2. split; [exact Oc_1|]. split; [apply (L5C.u64_at_agree RSEGS M2 Mc); [intros i Hi; apply FRZc; clear - Hi TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|exact TL82]|].
split; [apply (L5C.u8_at_agree RSEGS M2 Mc); [intros i Hi; apply FRZc; clear - Hi TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|exact TT162]|].
apply (L5C.u64_at_agree RSEGS M2 Mc); [intros i Hi; apply FRZc; clear - Hi TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|exact TI242]. }
destruct (PMSLPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M2 model2 mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 pre (PM.PS 9 0 tt (ti + 1)) sm2 e2 cr2 Mc (PM.PS 10 0 tt (ti + 1)) CTX0 (conj RPRE2 (conj EC2 LR2)) INV2 MGc (fun i Hi N => FRZc i Hi ltac:(intros X; apply N; rewrite <- ET2; lia)) HHc PTc ltac:(clear - TOK IB IX; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVc & LMc).
apply (IH fxc Rc Mc model2 (PM.PST mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 (pre ++ [(PM.PS 10 0 tt (ti + 1))])) sm2 e2 cr2).
+ unfold PMSLPD.linv. do 13 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INVc| exact LMc].
+ pose proof INVc as (_ & _ & _ & SH3 & _). eapply PMPK2.lp_mu_lt_U; [exact ISH1| exact SH3| cbn [PM.p_src]; exact UN2| unfold PMSP.consumed, PM.unread in CONSq, UK2 |- *; cbn [PMPS.with_src PM.p_src] in CONSq, UK2 |- *; lia].
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutS.ADDR_S] in ECvv, ECvD.
cfeed P (PMSLPP.lpK9e_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_1 & Xc_2 & Xc_8 & Xc_9 & Xc_10 & Xc_18 & Xc_19 & Xc_20 & Xc_21 & Xc_22 & Xc_23 & Xc_24 & Xc_25 & Xc_26 & Xc_27)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xc_1.
try rewrite PMPK.word_id in Xc_2.
try rewrite PMPK.word_id in Xc_8.
try rewrite PMPK.word_id in Xc_9.
try rewrite PMPK.word_id in Xc_10.
try rewrite PMPK.word_id in Xc_18.
try rewrite PMPK.word_id in Xc_19.
try rewrite PMPK.word_id in Xc_20.
try rewrite PMPK.word_id in Xc_21.
try rewrite PMPK.word_id in Xc_22.
try rewrite PMPK.word_id in Xc_23.
try rewrite PMPK.word_id in Xc_24.
try rewrite PMPK.word_id in Xc_25.
try rewrite PMPK.word_id in Xc_26.
try rewrite PMPK.word_id in Xc_27.
assert (Mc = M2) as -> by (apply mem_eq_of_frz; exact FRZc).
apply (PMK.spiece_ro RSEGS model2 fx2 fxc R2 220436 Rc 0x35d98 M2 K Mh2 Ml2 MSc).
apply (PMSLPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxc Rc M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xc_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
*
assert (TI24x : L5.u64_at RSEGS Mq (T + 24) (2 ^ 24)) by (rewrite <- IX; exact TI24q).
cfeed P (PMSLPP.lpP9hx_conc fxq Rq Mq (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 55%nat => c | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxd & Rd & Md & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGd & _ & FRZd & MSd & KSd & Xd_1 & Xd_10 & Xd_11 & Xd_12 & Od_1)); PMK.pvz_clrT.
apply (tstep (PM.parser_own (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) ++ LBX) cr1 fxq fxd Rq Rd 220024 0x36490 Mq Md model1 K sp 0 0 (T + 24) 8 vb1 (32 * 2 ^ vk1) HHql Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| clear - TB ET; lia]) MSd MGd (fun i Hi _ _ N3 => FRZd i Hi N3)).
intros HHd.
assert (PTd : PM.pstate_at RSEGS Md (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 9 0 tt (2 ^ 24 + 1))).
{ rewrite <- ET. split; [apply (PMF.u32_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TM0q]|].
split; [apply (L5C.u64_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8q]|].
split; [apply (L5C.u8_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16q]|].
replace (2 ^ 24 + 1) with 16777217 by reflexivity. exact Od_1. }
pose proof (PMSLPK.lp_headw_mem L HI LY HIok K R M model LBX cr sp r fb cat s str sm e Mq model1 mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 pre (PM.PS 9 0 tt ti) smq e1 cr1 Md (PM.PS 9 0 tt (2 ^ 24 + 1)) CTX0 LMq MGd (fun i Hi N => FRZd i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHd PTd) as LMd.
apply (ERRZ fxd Rd Md model1 13 (PM.PST mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 0 tt (2 ^ 24 + 1))])) smq e1 cr1 Xd_1 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Xd_10 Xd_11 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx) ltac:(lia) LMd).
*
cfeed P (PMSLPP.lpP9h_conc fxq Rq Mq (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 39%nat => ti | 55%nat => c | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxd & Rd & Md & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGd & _ & FRZd & MSd & KSd & Xd_1 & Xd_10 & Xd_11 & Xd_12 & Od_1)); PMK.pvz_clrT.
apply (tstep (PM.parser_own (PMPS.with_src (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 0 tt ti])) (PM.SRC qcq deq remq)) ++ LBX) cr1 fxq fxd Rq Rd 220024 0x365f0 Mq Md model1 K sp 0 0 (T + 24) 8 vb1 (32 * 2 ^ vk1) HHql Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [unfold PM.parser_own, PM.vec_own; cbn; right; left; reflexivity| clear - TB ET; lia]) MSd MGd (fun i Hi _ _ N3 => FRZd i Hi N3)).
intros HHd.
assert (PTd : PM.pstate_at RSEGS Md (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 9 0 tt (ti + 1))).
{ rewrite <- ET. split; [apply (PMF.u32_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TM0q]|].
split; [apply (L5C.u64_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8q]|].
split; [apply (L5C.u8_at_agree RSEGS Mq Md); [intros i Hi; apply FRZd; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16q]|].
exact Od_1. }
destruct (PMSLPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e Mq model1 mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 pre (PM.PS 9 0 tt ti) smq e1 cr1 Md (PM.PS 9 0 tt (ti + 1)) CTX0 LMq INV1 MGd (fun i Hi N => FRZd i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHd PTd ltac:(clear - TOK IB IX; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVd & LMd).
destruct LMd as (RPRE7c & EC7c & LR7c). pose proof HHd as HH7x.
assert (STKc : L5C.stk (hl_sptop L) Md (sp - 128) 26624).
{ pose proof LR7c as (_ & _ & HPx & _). apply (PMK.stk_call L Md sp 32768 (sp - 128) 26624); [apply (PMK.stk_after RSEGS L KL LBX M Md sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.read_key_spec, PMSP.read_key_spec, PMSP.run_spec, PMSP.run_spec_r in RK. cbn [pa_read_key AD PmLayoutS.ADDR_S] in RK.
apply (RK fxd Rd Md model1 K LBX cr1 (sp - 128) 220436 fb cat (PM.PST mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 0 tt (ti + 1))])) str smq e1 HH7x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutS.ADDR_S]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutS.ADDR_S]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPRE7c. } { exact INCS. } { exact INVd. } { exact EC7c. }
{ pose proof LR7c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR7c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 7) with 26624 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMSLPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PM.PST mo1 dn1 dp1 (PM.SRC qcq deq remq) tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 0 tt (ti + 1))])) smq e1 cr1 M2 model2 s2 sm2 e2 cr2 26624 CTX0 LR7c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMSLPD.lslots in SL2. destruct SL2 as (D82 & D162 & D242 & D322 & D402 & D482 & D562 & D642 & D722 & D802 & D882 & D962 & D1042).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMSLPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P162 & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
pose proof PA2 as (_ & _ & _ & P82 & P92 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B12 & B22 & _).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PK2)].
2: {
pose proof EC2 as (EC2v & _). pose proof INV2 as (IM2 & ID2 & _). rewrite ID2 in P92. rewrite IM2 in P82.
destruct PK2 as (SK2 & UK2).
destruct s2 as [mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 stk2]. cbn [PM.p_stk PM.p_src PM.p_b PM.p_k PM.p_tb PM.p_tg PM.p_more PM.p_done PM.p_depth] in *.
subst stk2.
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC2 & _). cbn [PM.p_b PM.p_k PM.p_stk] in PVEC2.
pose proof PVEC2 as (WC0 & WC8 & _ & Hk2 & Hlen2 & Hal2 & VDB2 & _ & _ & VEL2).
rewrite length_app in Hlen2, WC8. cbn [length] in Hlen2, WC8. rewrite Nat2Z.inj_add in Hlen2, WC8. cbn [Z.of_nat Pos.of_succ_nat] in Hlen2, WC8.
assert (HT2 : exists T2, T2 = vb2 + 32 * Z.of_nat (length pre)) by (eexists; reflexivity). destruct HT2 as (T2 & ET2).
assert (TOPC2 : PM.pstate_at RSEGS M2 T2 (PM.PS 9 0 tt (ti + 1))).
{ rewrite ET2. specialize (VEL2 (length pre) ltac:(rewrite length_app; cbn; lia)). rewrite PMPK2.nth_app_at in VEL2. exact VEL2. }
pose proof TOPC2 as (TM02 & TL82 & TT162 & TI242). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in TM02, TL82, TT162, TI242.
set (LB2 := PM.parser_own (PM.PST mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 (pre ++ [(PM.PS 9 0 tt (ti + 1))])) ++ LBX) in *.
assert (BR2 : PMFR.brange L LB2) by (apply (PMFR.brange_of_heap L HI HIok LB2 LB2 cr2 M2 _ HH2); apply incl_refl).
assert (VIN2 : In (vb2, 32 * 2 ^ vk2) LB2) by (unfold LB2, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR2 _ _ VIN2) as (W0b & W1b & W4b). unfold hl_ceil in W4b.
assert (P2K2 : 0 < 2 ^ vk2) by (apply (PM.pow2_pos vk2); lia).
assert (TB2 : 0 <= T2 /\ T2 + 32 <= vb2 + 32 * 2 ^ vk2) by (rewrite ET2; clear - Hlen2 W0b; lia).
assert (TAL2 : T2 mod 16 = 0) by (rewrite ET2; replace (vb2 + 32 * Z.of_nat (length pre)) with (vb2 + (Z.of_nat (length pre) * 2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal2).
assert (WT2 : L5.writable RSEGS M2 T2 32) by (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 vb2 (32 * 2 ^ vk2)); [exact VDB2|clear - TB2 ET2; lia|clear - TB2 ET2; lia]|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia]).
assert (V3682 : L5.u64_at RSEGS M2 (fb + 40 + 368) (T2 + 32)).
{ rewrite ET2. replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia. replace (vb2 + 32 * Z.of_nat (length pre) + 32) with (vb2 + 32 * (Z.of_nat (length pre) + 1)) by lia. exact WC8. }
cfeed P (PMSLPP.lpK90_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T2 | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL2]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_10 & Oc_1)); PMK.pvz_clrT.
apply (tstep LB2 cr2 fx2 fxc R2 Rc 0x35d14 0x35b20 M2 Mc model2 K sp 0 0 (T2 + 0) 4 vb2 (32 * 2 ^ vk2) HH2 Mh2 Ml2 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [exact VIN2| clear - TB2 ET2; lia]) MSc MGc (fun i Hi _ _ N3 => FRZc i Hi N3)).
intros HHc.
assert (PTc : PM.pstate_at RSEGS Mc (vb2 + 32 * Z.of_nat (length pre)) (PM.PS 10 0 tt (ti + 1))).
{ rewrite <- ET2. split; [exact Oc_1|]. split; [apply (L5C.u64_at_agree RSEGS M2 Mc); [intros i Hi; apply FRZc; clear - Hi TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|exact TL82]|].
split; [apply (L5C.u8_at_agree RSEGS M2 Mc); [intros i Hi; apply FRZc; clear - Hi TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|exact TT162]|].
apply (L5C.u64_at_agree RSEGS M2 Mc); [intros i Hi; apply FRZc; clear - Hi TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|clear - TB2 W4b STOP; lia|exact TI242]. }
destruct (PMSLPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M2 model2 mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 pre (PM.PS 9 0 tt (ti + 1)) sm2 e2 cr2 Mc (PM.PS 10 0 tt (ti + 1)) CTX0 (conj RPRE2 (conj EC2 LR2)) INV2 MGc (fun i Hi N => FRZc i Hi ltac:(intros X; apply N; rewrite <- ET2; lia)) HHc PTc ltac:(clear - TOK IB IX; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVc & LMc).
apply (IH fxc Rc Mc model2 (PM.PST mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 (pre ++ [(PM.PS 10 0 tt (ti + 1))])) sm2 e2 cr2).
+ unfold PMSLPD.linv. do 13 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INVc| exact LMc].
+ pose proof INVc as (_ & _ & _ & SH3 & _). eapply PMPK2.lp_mu_lt_U; [exact ISH1| exact SH3| cbn [PM.p_src]; exact UN2| unfold PMSP.consumed, PM.unread in CONSq, UK2 |- *; cbn [PMPS.with_src PM.p_src] in CONSq, UK2 |- *; lia].
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutS.ADDR_S] in ECvv, ECvD.
cfeed P (PMSLPP.lpK9e_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSLPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMSLPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_1 & Xc_2 & Xc_8 & Xc_9 & Xc_10 & Xc_18 & Xc_19 & Xc_20 & Xc_21 & Xc_22 & Xc_23 & Xc_24 & Xc_25 & Xc_26 & Xc_27)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xc_1.
try rewrite PMPK.word_id in Xc_2.
try rewrite PMPK.word_id in Xc_8.
try rewrite PMPK.word_id in Xc_9.
try rewrite PMPK.word_id in Xc_10.
try rewrite PMPK.word_id in Xc_18.
try rewrite PMPK.word_id in Xc_19.
try rewrite PMPK.word_id in Xc_20.
try rewrite PMPK.word_id in Xc_21.
try rewrite PMPK.word_id in Xc_22.
try rewrite PMPK.word_id in Xc_23.
try rewrite PMPK.word_id in Xc_24.
try rewrite PMPK.word_id in Xc_25.
try rewrite PMPK.word_id in Xc_26.
try rewrite PMPK.word_id in Xc_27.
assert (Mc = M2) as -> by (apply mem_eq_of_frz; exact FRZc).
apply (PMK.spiece_ro RSEGS model2 fx2 fxc R2 220436 Rc 0x35d98 M2 K Mh2 Ml2 MSc).
apply (PMSLPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxc Rc M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xc_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
Qed.
End WithHeap.
End PMSLP5.
