(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmParKit2 PmParStep
PmCertKitG PmUParseP PmUParseD PmUParseK Ju0_code_3692c_36930.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUParse1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUParseD.PMULPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1None"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LB"]; ["4Model"; "4m_halted"; "4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0R"; "0R1"; "6msteps"; "7credit"; "7hi_heap"; "7hl_sptop"; "8agree_on"; "9SCFG"]; [":cfg"; ":ec_at"; ";read_value_spec"; ";rtv_spec"; "<iter_ok"; "<lpG1"; "=FPState"; "=mkst"; "=seg_rom"; ">TSet"; "?srealizes"; "@mem_grows"; "Aloaded_segments"; "0SCFG_P"; "BIn"; "Cadd"]; ["Cle"; "Clt"; "Cpow"; "Csub"; "0bm"; "0c"; "0cr"; "0fx"; "0fx1"; "0i"; "0m"; "0model"; "0n"; "0o"; "0pc"; "0pc1"]; ["0sp"; "DZ_to_bv"; "Dbv"; "0v"; "0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia.
Module PMULP1.
Import PMU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmUParse1 "Q9'R2yR0%211'4y8%511%311p051';&Nr5r4r3+@%544321&Q@z%2216&Q?%1296&QB+2+R0%3221%9251&Q1&Q<r8r6%45321CBr7%655413Ep031p091p0A1p0E1pS<L1pT8M1pSLN1pQ>Q01pQ<Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmUParse1 "Q4'R2yR0%211'4y8%511%311p051';'7&Q@zr1%3221&QA&QB+2+R0%3221%5271%;271'8r3&R1r2%22H1%411r4%113%83G31p0:1pSDG1%;3I8:p021pQ@K1pQ<L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F.
pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B.
Qed.
Lemma tstep : ltac2:(TCodec.tc2 tcn__PmUParse1 "UL'2'6';%2211%411&K'Q6&Dy5'R2yR0%211%5241'4y8%611%311p061'@&Q9&Lv<rCrBr;&Cr9%211%8576541'8%A1C&Ar:%211(1%11H%73631%Q42JJ%Q611&B%11@(3%115%>3531&Q@+SoonPPPPP0&Mv>%211%5241&QC+XPPP0%2241+T0%42N1%;231r<%=219':z%O3QJQ41'7%B2:6&Q?%128Q8%E21A%5241%9271%Q73R2Q49&Q>(5r8%24R6R6Q>1rJ%53R721%O2QAQC%=2QDQ<%>2QC6%Q2221%B241%C261%G2=1'J&Q<&Q7rIrG&R1rE%22R?1&Q8%118%85763R61rHrFrD%92RF1%=5431R:6%@3?61&Q;%125R>r1%QJ2Q;1&QA&QB+2+R0%3221%5271%Q@271&9%QM2RIQJr2%R5221%QC23QM%<231%QG231%711r3%R;2S11%QI2S2S1%B231%QM231%=11r4%RA2S61rA%R02S81%I241%R4241%D11r5%Q=2SJ1%Q@11%QM12%S:3SG21p061p0>1p0E1p0N1pSDT:1rNrM%SF1Q@%SL5SK32QH1'Q:&OvQ=%211&Q0rL%26R41R>QJQIQO%74R541QIp091rK%66R8=1R6R5R3%;4R981QMp041p0B1p0QK1p0QN1p0R@1p0RO1p0S:1p0S=1p0SD1p0SK1p0T31p0T<1pS:U71p2U81pSFU91pT<U:1pSJU;1pT:U<1pT2U=1pLTM1pSHTO1pQ@U11pQ<U21pT0UB1pSNUC1pQDU:1pQBU;1pSBUB1pS@UC1pS>UE1pQ0UG1").
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
Theorem parse_iter1 : ltac2:(TCodec.tc2 tcn__PmUParse1 "<&Q3vQ=v>v<%43321&Q2%13543&Q4&Q5%248761p041p071").
Proof.
intros RTV RV. unfold PMULPD.iter_ok.
intros K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI TG IH.
pose proof CTX as CTX0.
destruct CTX as (HH & MOK & K0 & ENT & FOK & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
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
destruct LI as (X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & X10h & X3 & X4 & INV1 & LM1).
pose proof LM1 as LM1c.
destruct LM1 as (RPRE1 & EC1 & STEP1 & EE1 & HP1 & CK1 & MB1 & HH1 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104).
pose proof (PMFR.model_ok_but_vm model model1 MOK MB1) as MOK1. pose proof MOK1 as (Mh1 & Ml1 & _).
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 32768) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 32768 sp 32768 _ STK HP1); lia).
pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1. pose proof STK1 as (_ & _ & _ & _ & SD1).
destruct RPRE1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA1, IA1, VIS1, VREF1. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutU.ADDR_U] in PA1, IA1, VIS1, VREF1.
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
assert (BRX : PMFR.brange L LBX).
{ apply (PMFR.brange_incl L LBX (PM.parser_own s ++ LBX) (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH (incl_refl _))). apply incl_appr. apply incl_refl. }
assert (WRH : forall i, PMK.inW (PMSP.W_run AD fb) i -> (fb + 8 <= i < fb + 24) \/ (fb + 48 <= i < fb + 56) \/ (fb + 320 <= i < fb + 360) \/ (fb + 376 <= i < fb + 424) \/ (fb + 480 <= i < fb + 488) \/ (fb + 592 <= i < fb + 596) \/ (0xc72b0 <= i < 0xe8f18)).
{ intros i (r0 & Hin & Hr). unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.p_more PM.p_done PM.p_depth] in *.
pose proof INV1 as (IM1 & ID1 & IDP1 & ISH1 & ITB1). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM1, ID1, IDP1, ISH1, ITB1.
destruct (exists_last (l := stk1) ltac:(intros E; rewrite E in ISH1; destruct ISH1 as (X & _); cbn in X; lia)) as (pre & top & Epre).
subst stk1. destruct top as [tm tl tt ti].
unfold PMULPD.top_mode in TG. cbn [PM.p_stk] in TG. rewrite last_last in TG. cbn [PM.ps_mode] in TG.
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
assert (VI1 : forall a, vb1 <= a < vb1 + 32 * 2 ^ vk1 -> ~ (65536 <= a < 958464)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1'. intros a Ha. clear - Ha W1'. lia. }
assert (P2K : 0 < 2 ^ vk1) by (apply (PM.pow2_pos vk1); lia).
assert (TB : 0 <= T /\ T + 32 <= vb1 + 32 * 2 ^ vk1) by (rewrite ET; lia).
assert (TAL : T mod 16 = 0) by (rewrite ET; replace (vb1 + 32 * Z.of_nat (length pre)) with (vb1 + (Z.of_nat (length pre) * 2) * 16) by lia; rewrite Z.mod_add by lia; exact Hal1).
assert (WT : L5.writable RSEGS M1 T 32) by (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 vb1 (32 * 2 ^ vk1)); [exact VDB1|lia|lia]|lia|lia]).
assert (WP1 : L5.writable RSEGS M1 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF1|lia|lia]).
pose proof BASE1 as (IMG1 & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG1.
pose proof EC1 as (EC1v & EC18 & EC1D).
assert (V368 : L5.u64_at RSEGS M1 (fb + 40 + 368) (T + 32)).
{ rewrite ET. replace (fb + 40 + 368) with (fb + 40 + 360 + 8) by lia. replace (vb1 + 32 * Z.of_nat (length pre) + 32) with (vb1 + 32 * (Z.of_nat (length pre) + 1)) by lia. exact VC8. }
assert (V360 : L5.u64_at RSEGS M1 (fb + 40 + 360) vb1) by exact VC0.
unfold PMSP.cfg.
unfold PMULPD.lpG1 in TG. destruct TG as [E|[E|[E|[E|E]]]]; rewrite E in *.
-
cfeed P (PMULPP.luH0_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_10 & Xa_11 & Xa_12 & Oa_1)); PMK.pvz_clrT.
apply (tstep LB1 cr1 fx1 fxa R1 Ra 0x365ec 0x369bc M1 Ma model1 K sp 0 0 (T + 0) 4 vb1 (32 * 2 ^ vk1) HH1 Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [exact VIN1| clear - TB ET; lia]) MSa MGa (fun i Hi _ _ N3 => FRZa i Hi N3)).
intros HHa.
assert (PTa : PM.pstate_at RSEGS Ma (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 1 tl tt ti)).
{ rewrite <- ET. split; [exact Oa_1|]. split; [apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8]|].
split; [apply (L5C.u8_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16]|].
apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TI24]. }
destruct (PMULPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M1 model1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 0 tl tt ti) sm1 e1 cr1 Ma (PM.PS 1 tl tt ti) CTX0 LM1c INV1 MGa (fun i Hi N => FRZa i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHa PTa ltac:(clear - TOK ; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVa & LMa).
destruct LMa as (RPRE9c & EC9c & LR9c). pose proof HHa as HH9x.
assert (STKc : L5C.stk (hl_sptop L) Ma (sp - 128) 30720).
{ pose proof LR9c as (_ & _ & HPx & _). apply (PMK.stk_call L Ma sp 32768 (sp - 128) 30720); [apply (PMK.stk_after RSEGS L KL LBX M Ma sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.rtv_spec, PMSP.rtv_spec, PMSP.run_spec, PMSP.run_spec_r in RTV. cbn [pa_rtv AD PmLayoutU.ADDR_U] in RTV.
apply (RTV fxa Ra Ma model1 K LBX cr1 (sp - 128) 223440 fb cat (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 1 tl tt ti)])) str sm1 e1 HH9x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPRE9c. } { exact INCS. } { exact INVa. } { exact EC9c. }
{ pose proof LR9c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR9c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 9) with 30720 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMULPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 1 tl tt ti)])) sm1 e1 cr1 M2 model2 s2 sm2 e2 cr2 30720 CTX0 LR9c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMULPD.lslots in SL2. destruct SL2 as (D8 & D16 & D24 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & D104).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMULPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P16b & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)].
2: {
pose proof EC2 as (EC2v & _).
pose proof INV2 as (IM2 & ID2 & _). pose proof PA2 as (_ & _ & _ & P82 & P92 & _). rewrite ID2 in P92.
cfeed P (PMULPP.luA0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_10)); PMK.pvz_clrT.
assert (Mb = M2) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (PMK.spiece_ro RSEGS model2 fx2 fxb R2 0x368d0 Rb 0x365ec M2 K Mh2 Ml2 MSb).
apply (IH fxb Rb M2 model2 s2 sm2 e2 cr2).
+ unfold PMULPD.linv. do 14 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INV2|].
split; [exact RPRE2|]. split; [exact EC2| exact LR2].
+ destruct PV2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _). eapply PMPK2.lp_mu_lt_U; [exact ISH1| exact SH2| exact UN2| exact UV].
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutU.ADDR_U] in ECvv, ECvD.
cfeed P (PMULPP.luAe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
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
apply (PMK.spiece_ro RSEGS model2 fx2 fxc R2 0x368d0 Rc 0x3692c M2 K Mh2 Ml2 MSc).
apply (PMULPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxc Rc M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xc_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
-
destruct TPOS as [(Pnil & _)|(_ & NB)]; [|exfalso; apply NB; unfold PM.mode_bottom; cbn; right; reflexivity].
subst pre. cbn [length Z.of_nat] in *.
assert (TV : T = vb1) by (rewrite ET; lia). assert (V360' : L5.u64_at RSEGS M1 (fb + 40 + 360) T) by (rewrite TV; exact V360).
cfeed P (PMULPP.luH1_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_2 & Xa_8 & Xa_9 & Xa_10 & Xa_11 & Xa_12 & Xa_18 & Xa_19 & Xa_20 & Xa_21 & Xa_22 & Xa_23 & Xa_24 & Xa_25 & Xa_26 & Xa_27 & Oa_1 & Oa_2)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xa_1.
try rewrite PMPK.word_id in Xa_2.
try rewrite PMPK.word_id in Xa_8.
try rewrite PMPK.word_id in Xa_9.
try rewrite PMPK.word_id in Xa_10.
try rewrite PMPK.word_id in Xa_11.
try rewrite PMPK.word_id in Xa_12.
try rewrite PMPK.word_id in Xa_18.
try rewrite PMPK.word_id in Xa_19.
try rewrite PMPK.word_id in Xa_20.
try rewrite PMPK.word_id in Xa_21.
try rewrite PMPK.word_id in Xa_22.
try rewrite PMPK.word_id in Xa_23.
try rewrite PMPK.word_id in Xa_24.
try rewrite PMPK.word_id in Xa_25.
try rewrite PMPK.word_id in Xa_26.
try rewrite PMPK.word_id in Xa_27.
apply (tstep LB1 cr1 fx1 fxa R1 Ra 0x365ec 0x3692c M1 Ma model1 K sp (fb + 48) 368 0 0 0 0 HH1 Mh1 Ml1 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(right; unfold hl_ceil; lia) ltac:(left; reflexivity) MSa MGa (fun i Hi _ N2 _ => FRZa i Hi ltac:(intros X; apply N2; lia) ltac:(intros X; apply N2; lia))).
intros HHa.
destruct Oa_2 as (U8a & U9a).
assert (AGa : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 48 \/ fb + 50 <= a) -> (a + n <= fb + 408 \/ fb + 416 <= a) -> L5C.agree_on M1 Ma a n).
{ intros a n H1 H2 H3 H4 i Hi. apply FRZa; [clear - H1 H2 Hi; lia| clear - H3 Hi; lia| clear - H4 Hi; lia]. }
assert (PAa : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 Ma (fb + 40) (fb + 440) (PM.PST 0 1 dp1 src1 tb1 tg1 vb1 vk1 [])).
{ apply (PMPK2.parser_accept_upd RSEGS AD M1 Ma (fb + 40) (fb + 440) _ PA1); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.p_depth].
- lia.
- lia.
- apply AGa; lia.
- apply AGa; lia.
- apply AGa; lia.
- apply PMPK.dkr_grows. exact MGa.
- apply PMPK.dkr_grows. exact MGa.
- exact U8a.
- replace (fb + 40 + 9) with (fb + 40 + 8 + 1) by lia. exact U9a.
- rewrite <- TV. exact Oa_1.
- apply PMPK.dkr_grows. exact MGa.
- lia.
- clear - W4 STOP. lia.
- apply AGa; [lia|clear - W4 STOP; lia| clear - W4 SLO F1; unfold hl_ceil in *; lia| clear - W4 SLO F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MGa. }
assert (EKa : PMK.ek L LB1 sp 32768 [(fb + 48, 2); (fb + 408, 8)] M1 Ma).
{ apply (PMK.ek_piece_in RSEGS L KL LB1 sp 32768 [(fb + 48, 2); (fb + 408, 8)] M1 Ma (fun a => (fb + 48 <= a < fb + 50) \/ (fb + 408 <= a < fb + 416)) ltac:(intros a Ha N; apply FRZa; [exact Ha| intros X; apply N; left; lia| intros X; apply N; right; lia]) STK1 (PMFR.brange_hi L LB1 BR1)).
intros a [Ha|Ha]; right; [apply PMK.inW_here; lia| apply PMK.inW_next; apply PMK.inW_here; lia]. }
assert (WCa : forall a, PMK.inW [(fb + 48, 2); (fb + 408, 8)] a -> (fb + 48 <= a < fb + 50) \/ (fb + 408 <= a < fb + 416)).
{ intros a (r0 & Hin & Hr). destruct Hin as [<-|[<-|[]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia. }
apply (PMULPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxa Ra Ma model1 (PM.PST 0 1 dp1 src1 tb1 tg1 vb1 vk1 []) sm1 e1 cr1 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xa_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutU.ADDR_U].
split; [exact PAa|].
split; [apply (PMF.iss_at_agree RSEGS AD M1 Ma (fb + 440) str sm1); [lia|lia| apply AGa; lia| |exact IA1]|].
{ intros c0 n0 q0 Es. assert (HQ : In (q0, c0) LBX) by (apply INCS; rewrite Es; cbn; left; reflexivity).
destruct (BRX _ _ HQ) as (Z0 & _ & Z4). unfold hl_ceil in Z4. apply AGa; [lia|clear - Z4 STOP; lia| clear - Z4 SLO F1; lia| clear - Z4 SLO F1; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M1 Ma); [apply AGa; lia|lia|lia| exact VIS1]|].
split; [apply (L5C.u64_at_agree RSEGS M1 Ma); [apply AGa; lia|lia|lia| exact VREF1]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 sp 32768 [(fb + 48, 2); (fb + 408, 8)] M1 Ma EKa); [| | | | exact BASE1]|].
all: try (intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCa in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha; clear - I Ha SLO STOP F1; lia).
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 sp 32768 [(fb + 48, 2); (fb + 408, 8)] M1 Ma EKa); [| | exact ERR1]| exact TB1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCa in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha; clear - I Ha SLO STOP F1; lia.
+ apply (L5C.defined_agree M1 Ma (fb + 8) 16); [apply AGa; lia| exact EC1D].
+ split; [exact STEP1|]. split; [exact EE1|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M Ma).
- apply (PMK.ek_trans L LBX sp 32768 _ M M1 Ma (PMK.ek_of_hpres L LBX sp 32768 _ M M1 HP1)).
apply (PMK.ek_weaken L LBX LB1 sp 32768 sp 32768 _ [(fb + 48, 2); (fb + 408, 8)] M1 Ma EKa); [unfold LB1; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. assert (X : PMK.inW [(fb + 48, 2); (fb + 408, 8)] a) by (exists r0; split; assumption). apply WCa in X.
unfold PMSP.W_run, PMSP.o_p, PMSP.o_vec in O. cbn [pa_off_p AD PmLayoutU.ADDR_U app] in O.
destruct X as [X|X]; [apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]|].
apply (O (fb + 40 + 360, 24)); [do 5 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- pose proof (PMK.stk_grows L M1 Ma sp 32768 MGa STK1) as (_ & _ & _ & _ & D). exact D.
- apply (PMK.dk_trans L LBX sp 32768 M M1 Ma (PMK.dk_of_hpres L LBX sp 32768 _ M M1 HP1)). apply (PMK.dk_grows L LBX sp 32768 M1 Ma MGa). }
split; [exact CK1|]. split; [exact MB1|]. split; [exact HHa|].
unfold PMULPD.lslots. repeat split; (apply (L5C.u64_at_agree RSEGS M1 Ma); [apply AGa; lia|lia|lia|]); assumption.
-
cfeed P (PMULPP.luH6_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_10 & Xa_11 & Xa_12 & Oa_1)); PMK.pvz_clrT.
apply (tstep LB1 cr1 fx1 fxa R1 Ra 0x365ec 0x369bc M1 Ma model1 K sp 0 0 (T + 0) 4 vb1 (32 * 2 ^ vk1) HH1 Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [exact VIN1| clear - TB ET; lia]) MSa MGa (fun i Hi _ _ N3 => FRZa i Hi N3)).
intros HHa.
assert (PTa : PM.pstate_at RSEGS Ma (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 5 tl tt ti)).
{ rewrite <- ET. split; [exact Oa_1|]. split; [apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8]|].
split; [apply (L5C.u8_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16]|].
apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TI24]. }
destruct (PMULPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M1 model1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 6 tl tt ti) sm1 e1 cr1 Ma (PM.PS 5 tl tt ti) CTX0 LM1c INV1 MGa (fun i Hi N => FRZa i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHa PTa ltac:(clear - TOK ; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVa & LMa).
destruct LMa as (RPRE9c & EC9c & LR9c). pose proof HHa as HH9x.
assert (STKc : L5C.stk (hl_sptop L) Ma (sp - 128) 30720).
{ pose proof LR9c as (_ & _ & HPx & _). apply (PMK.stk_call L Ma sp 32768 (sp - 128) 30720); [apply (PMK.stk_after RSEGS L KL LBX M Ma sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.rtv_spec, PMSP.rtv_spec, PMSP.run_spec, PMSP.run_spec_r in RTV. cbn [pa_rtv AD PmLayoutU.ADDR_U] in RTV.
apply (RTV fxa Ra Ma model1 K LBX cr1 (sp - 128) 223440 fb cat (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt ti)])) str sm1 e1 HH9x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPRE9c. } { exact INCS. } { exact INVa. } { exact EC9c. }
{ pose proof LR9c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR9c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 9) with 30720 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMULPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt ti)])) sm1 e1 cr1 M2 model2 s2 sm2 e2 cr2 30720 CTX0 LR9c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMULPD.lslots in SL2. destruct SL2 as (D8 & D16 & D24 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & D104).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMULPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P16b & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)].
2: {
pose proof EC2 as (EC2v & _).
pose proof INV2 as (IM2 & ID2 & _). pose proof PA2 as (_ & _ & _ & P82 & P92 & _). rewrite ID2 in P92.
cfeed P (PMULPP.luA0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_10)); PMK.pvz_clrT.
assert (Mb = M2) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (PMK.spiece_ro RSEGS model2 fx2 fxb R2 0x368d0 Rb 0x365ec M2 K Mh2 Ml2 MSb).
apply (IH fxb Rb M2 model2 s2 sm2 e2 cr2).
+ unfold PMULPD.linv. do 14 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INV2|].
split; [exact RPRE2|]. split; [exact EC2| exact LR2].
+ destruct PV2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _). eapply PMPK2.lp_mu_lt_U; [exact ISH1| exact SH2| exact UN2| exact UV].
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutU.ADDR_U] in ECvv, ECvD.
cfeed P (PMULPP.luAe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
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
apply (PMK.spiece_ro RSEGS model2 fx2 fxc R2 0x368d0 Rc 0x3692c M2 K Mh2 Ml2 MSc).
apply (PMULPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxc Rc M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xc_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
-
assert (TTR : 0 <= tt <= 255) by (clear - TOK; unfold PM.pstate_ok in TOK; cbn in TOK; lia).
cfeed P (PMULPP.luH8_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 53%nat => tt | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_10 & Xa_11 & Xa_12 & Xa_13 & Oa_1)); PMK.pvz_clrT.
apply (tstep LB1 cr1 fx1 fxa R1 Ra 0x365ec 0x36afc M1 Ma model1 K sp 0 0 (T + 0) 4 vb1 (32 * 2 ^ vk1) HH1 Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [exact VIN1| clear - TB ET; lia]) MSa MGa (fun i Hi _ _ N3 => FRZa i Hi N3)).
intros HHa.
assert (PTa : PM.pstate_at RSEGS Ma (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 7 tl tt ti)).
{ rewrite <- ET. split; [exact Oa_1|]. split; [apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8]|].
split; [apply (L5C.u8_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16]|].
apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TI24]. }
destruct (PMULPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M1 model1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 8 tl tt ti) sm1 e1 cr1 Ma (PM.PS 7 tl tt ti) CTX0 LM1c INV1 MGa (fun i Hi N => FRZa i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHa PTa ltac:(clear - TOK ; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVa & LMa).
destruct LMa as (RPRE8c & EC8c & LR8c). pose proof HHa as HH8x.
assert (STKc : L5C.stk (hl_sptop L) Ma (sp - 128) 28672).
{ pose proof LR8c as (_ & _ & HPx & _). apply (PMK.stk_call L Ma sp 32768 (sp - 128) 28672); [apply (PMK.stk_after RSEGS L KL LBX M Ma sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.read_value_spec, PMSP.read_value_spec, PMSP.run_spec, PMSP.run_spec_r in RV. cbn [pa_read_value AD PmLayoutU.ADDR_U] in RV.
apply (RV fxa Ra Ma model1 K LBX cr1 (sp - 128) 223276 fb cat (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt ti)])) str sm1 e1 HH8x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args_rv, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11, L5K.rl13. split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|]. exists tt. split; [clear - TOK; unfold PM.pstate_ok in TOK; cbn in TOK; lia| rewrite L5K.rl12; PMK.rk]. }
{ exact RPRE8c. } { exact INCS. } { exact INVa. } { exact EC8c. }
{ pose proof LR8c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR8c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 8) with 28672 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMULPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt ti)])) sm1 e1 cr1 M2 model2 s2 sm2 e2 cr2 28672 CTX0 LR8c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMULPD.lslots in SL2. destruct SL2 as (D8 & D16 & D24 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & D104).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMULPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P16b & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)].
2: {
pose proof EC2 as (EC2v & _).
pose proof INV2 as (IM2 & ID2 & _). pose proof PA2 as (_ & _ & _ & P82 & P92 & _). rewrite ID2 in P92.
cfeed P (PMULPP.luB0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_10)); PMK.pvz_clrT.
assert (Mb = M2) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (PMK.spiece_ro RSEGS model2 fx2 fxb R2 0x3682c Rb 0x365ec M2 K Mh2 Ml2 MSb).
apply (IH fxb Rb M2 model2 s2 sm2 e2 cr2).
+ unfold PMULPD.linv. do 14 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INV2|].
split; [exact RPRE2|]. split; [exact EC2| exact LR2].
+ destruct STEP2 as (_ & _ & _ & _ & U32). pose proof INV2 as (_ & _ & _ & SH2 & _). eapply (PMPK2.lp_mu_pushv _ _ (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1); [exact ISH1| exact SH2| | cbn [PM.p_src]; lia| exact UN2| exact U32| exact PV2]. cbn [PM.p_stk]. rewrite (PMPK2.lp_X_set_top pre (PM.PS 8 tl tt ti) (PM.PS 7 tl tt ti)). change (PMPK2.lp_w (PM.PS 7 tl tt ti)) with (tl - ti). change (PMPK2.lp_w (PM.PS 8 tl tt ti)) with (tl - ti). change (PM.mode_flag (PM.ps_mode (PM.PS 7 tl tt ti))) with 0. change (PM.mode_flag (PM.ps_mode (PM.PS 8 tl tt ti))) with 1. lia.
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutU.ADDR_U] in ECvv, ECvD.
cfeed P (PMULPP.luBe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
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
apply (PMK.spiece_ro RSEGS model2 fx2 fxc R2 0x3682c Rc 0x3692c M2 K Mh2 Ml2 MSc).
apply (PMULPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxc Rc M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xc_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
-
cfeed P (PMULPP.luH10_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_10 & Xa_11 & Xa_12 & Oa_1)); PMK.pvz_clrT.
apply (tstep LB1 cr1 fx1 fxa R1 Ra 0x365ec 0x369bc M1 Ma model1 K sp 0 0 (T + 0) 4 vb1 (32 * 2 ^ vk1) HH1 Mh1 Ml1 ltac:(clear - STOP; lia) ltac:(unfold hl_ceil; clear - SLO; lia) ltac:(clear - SHI; lia) ltac:(left; reflexivity) ltac:(right; split; [exact VIN1| clear - TB ET; lia]) MSa MGa (fun i Hi _ _ N3 => FRZa i Hi N3)).
intros HHa.
assert (PTa : PM.pstate_at RSEGS Ma (vb1 + 32 * Z.of_nat (length pre)) (PM.PS 9 tl tt ti)).
{ rewrite <- ET. split; [exact Oa_1|]. split; [apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TL8]|].
split; [apply (L5C.u8_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TT16]|].
apply (L5C.u64_at_agree RSEGS M1 Ma); [intros i Hi; apply FRZa; clear - Hi TB W4 STOP; lia|clear - TB W4 STOP; lia|clear - TB W4 STOP; lia|exact TI24]. }
destruct (PMULPK.lp_headw L HI LY HIok K R M model LBX cr sp r fb cat s str sm e M1 model1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 10 tl tt ti) sm1 e1 cr1 Ma (PM.PS 9 tl tt ti) CTX0 LM1c INV1 MGa (fun i Hi N => FRZa i Hi ltac:(intros X; apply N; rewrite <- ET; lia)) HHa PTa ltac:(clear - TOK ; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia) ltac:(unfold PM.mode_bottom; cbn [PM.ps_mode]; split; intros; lia)) as (INVa & LMa).
destruct LMa as (RPRE9c & EC9c & LR9c). pose proof HHa as HH9x.
assert (STKc : L5C.stk (hl_sptop L) Ma (sp - 128) 30720).
{ pose proof LR9c as (_ & _ & HPx & _). apply (PMK.stk_call L Ma sp 32768 (sp - 128) 30720); [apply (PMK.stk_after RSEGS L KL LBX M Ma sp 32768 sp 32768 _ STK HPx); lia|lia|lia|lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.rtv_spec, PMSP.rtv_spec, PMSP.run_spec, PMSP.run_spec_r in RTV. cbn [pa_rtv AD PmLayoutU.ADDR_U] in RTV.
apply (RTV fxa Ra Ma model1 K LBX cr1 (sp - 128) 223440 fb cat (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 tl tt ti)])) str sm1 e1 HH9x MOK1 K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPRE9c. } { exact INCS. } { exact INVa. } { exact EC9c. }
{ pose proof LR9c as (SX & _). destruct SX as (_ & _ & _ & _ & SU). unfold PM.unread in *. cbn [PM.p_src] in *. lia. }
{ pose proof LR9c as (_ & _ & _ & CKx & _). exact (PMPK.credit_le_keep cr cr1 _ _ CRED CKx). }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 9) with 30720 in HP2.
pose proof (PMFR.model_ok_but_vm model model2 MOK (L5C.model_but_vm_trans model model1 model2 MB1 MB2)) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & POST2).
destruct (PMULPK.lp_lift L HI LY HIok K R M model LBX cr sp r fb cat s str sm e _ model1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 9 tl tt ti)])) sm1 e1 cr1 M2 model2 s2 sm2 e2 cr2 30720 CTX0 LR9c ltac:(lia) ltac:(lia) HP2 STEP2 EE2 CK2 MB2 HH2) as (LR2 & STK2 & AGs2 & AGo2 & AGv2).
pose proof LR2 as (_ & _ & _ & _ & _ & _ & SL2). unfold PMULPD.lslots in SL2. destruct SL2 as (D8 & D16 & D24 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & D104).
pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2. pose proof STK2 as (_ & _ & _ & _ & SD2).
destruct (PMULPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (VIS2 & P16b & PD2 & IMG2 & PA2 & IA2 & UN2).
assert (WP2 : L5.writable RSEGS M2 (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
destruct POST2 as [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)].
2: {
pose proof EC2 as (EC2v & _).
pose proof INV2 as (IM2 & ID2 & _). pose proof PA2 as (_ & _ & _ & P82 & P92 & _). rewrite ID2 in P92.
cfeed P (PMULPP.luA0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_10)); PMK.pvz_clrT.
assert (Mb = M2) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (PMK.spiece_ro RSEGS model2 fx2 fxb R2 0x368d0 Rb 0x365ec M2 K Mh2 Ml2 MSb).
apply (IH fxb Rb M2 model2 s2 sm2 e2 cr2).
+ unfold PMULPD.linv. do 14 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INV2|].
split; [exact RPRE2|]. split; [exact EC2| exact LR2].
+ destruct PV2 as (_ & UV). pose proof INV2 as (_ & _ & _ & SH2 & _). eapply PMPK2.lp_mu_lt_U; [exact ISH1| exact SH2| exact UN2| exact UV].
}
pose proof ECv as (ECvv & _ & ECvD). unfold PMSP.o_ec in ECvv, ECvD. cbn [pa_off_ec AD PmLayoutU.ADDR_U] in ECvv, ECvD.
cfeed P (PMULPP.luAe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | 46%nat => bv_unsigned (getr R (PMK.reg 21)) | 47%nat => bv_unsigned (getr R (PMK.reg 22)) | 48%nat => bv_unsigned (getr R (PMK.reg 23)) | 49%nat => bv_unsigned (getr R (PMK.reg 24)) | 50%nat => bv_unsigned (getr R (PMK.reg 25)) | 51%nat => bv_unsigned (getr R (PMK.reg 26)) | 52%nat => bv_unsigned (getr R (PMK.reg 27)) | 56%nat => v | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact TAL]).
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
apply (PMK.spiece_ro RSEGS model2 fx2 fxc R2 0x368d0 Rc 0x3692c M2 K Mh2 Ml2 MSc).
apply (PMULPK.lp_fin L HI LY K R M model LBX cr sp r fb cat s str sm e fxc Rc M2 model2 s2 sm2 e2 cr2 CTX0).
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ (rewrite Xc_2; symmetry; exact Rsp) | PMK.rk ] |]). destruct Hx.
+ PMK.rk.
+ exact RPRE2.
+ exact ECvD.
+ exact LR2.
Qed.
End WithHeap.
End PMULP1.
