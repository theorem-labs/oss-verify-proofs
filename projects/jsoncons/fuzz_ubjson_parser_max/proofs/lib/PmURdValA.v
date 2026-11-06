(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmParStep PmCertKitG PmURdValP PmSRdValD.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmURdValA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSRdValD.PMSRVD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LB"; "4Model"; "4m_halted"]; ["4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0R"; "0R1"; "6msteps"; "7credit"; "7hi_heap"; "7hl_sptop"; "8agree_on"; "8stk"; ":range"; "9SCFG"]; [";brange"; "<pa_read_value"; "=ADDR_U"; ">args_rvP"; ">rvA"; "?cfg"; "?ec_at"; "?prog_value"; "?run_spec"; "@begin_array_spec"; "@begin_object_spec"; "@make_ec_spec"; "Aek"; "AinW"; "BFPState"; "Bmkst"]; ["Bseg_rom"; "CTSet"; "Dsrealizes"; "Emem_grows"; "Floaded_segments"; "0SCFG_P"; "Gadd"; "Gle"; "Glt"; "Gpow"; "Gsub"; "0W"; "0a"; "0c"; "0cr"; "0fx"]; ["0fx1"; "0i"; "0model"; "0n"; "0o"; "0pc"; "0pc1"; "0sp"; "HZ_to_bv"; "Hbv"; "0v"; "0x"; "0x0"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMURVA.
Import PMU.
Local Ltac gl_disp := lazymatch goal with
| |- getr _ _ = _ => PMK.rk
| |- (_ <= _ <= _)%Z => lia
| |- (_ <= _ < _)%Z => lia
| |- (_ <= _)%Z => lia
| |- (_ < _)%Z => lia
| |- forall x, In x _ -> _ => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [PMK.rk|]); destruct Hx
| |- L5.ra_ok _ => split; [lia| reflexivity]
| _ => assumption
end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmURdValA "Q9'R9yR0%211'3y8%511%311p051'9&Lr5r4r3+@%544321&QGz%2216&QF%1296&QI+2+R0%3221%9251&Q6&QDr8r6%45321CBr7%655413Ep031p091p0A1p0E1pSLL1pTFM1pT:N1pQ:Q01pQ8Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma gl_step : ltac2:(TCodec.tc2 tcn__PmURdValA "U2'1'4'9%2211%411&I'Q>&By5'R9yR0%211%5241'3y8%611%311p061'>&QA&Jv:r?r>r7&Ar5%211%8576541'6%A1C&?r6%211(0%11H%73631%Q42JJ%Q611&@%11@(2%115%>3531&QG+SoonPPPPP0&Kv<%211%5241&QJ+XPPP0%2241+R@%42N1%;231r8%=219'8z%O3QJQ41'5%B2:6&QF%128Q8%E21A%5241%9271'H&QD&Q?rDrB&R8r@%22R11&Q@%118%85763QG1rCrA%82R7QKr=%=543216%@3?61&QC%12R0QOr1%Q<2M1&QH&QI+2+R0%3221%5271%Q2271&7%Q?2R:Q<r2%QG221%Q523Q?%<231%Q9231%711r3%QM2RB1%Q;2RCH%B231%Q?231%=11r4%Q62S51%Q111%Q:12%RE3S221p061p0=1p0F1pT4SD1rIrH%S01S3%S65S532Q@1'QB&OvQE%211&Q5rGrE%36QM21QCQBQH%84QN51S=p0:1rF%76R1>1QOQNQL%<4R291SAp041p0C1p0QD1p0QG1p0R91p0RD1p0RG1p0RN1p0S51p0S=1p0SF1pT8TA1pTHTB1pT@TC1pHT31pT6T51pQ<T71pQ8T81pT>TH1pT<TI1pQ@T@1pQ>TA1pT2TH1pT0TI1pSNTK1pLTM1").
Proof. intros LB cr fx fx1 R R1 pc pc1 M M1 model K sp x n.
intros HH Mh Ml TOP H1 H2 H3 MS MG FRZ KONT.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R pc R1 pc1 M1
(fun a => (sp - 80 <= a < sp - 80 + 80) \/ (x <= a < x + n)) K HH Mh Ml TOP MS MG).
- intros a Ha N. apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X.
- intros a Pa. unfold PMK.cwr. left. destruct Pa as [Pa|Pa]; [lia|]. destruct H3 as [H3|H3]; lia.
- intros a. apply PMK.or_dec; apply PMK.rng_dec.
- exact KONT.
Qed.
Lemma gl_ek : ltac2:(TCodec.tc2 tcn__PmURdValA "RK'1'4'9%2211%411&N%611'R9yR0%211'3y8%511%311pTJ51'5&QGzr1%3221&QH&QI+2+R0%3221%5271%;271&7&QJr8+R@%3221r2%A221&QF%1245%@241%F241%;11r3%H2;1r7%82=1%G241%M241%B11'6r5&R8r4%22Q:1%411r6%113%83Q931p0:1p0B1p0O1pT4QH1&M&Kv<%211+lP0%542IG1&Q0r9%2261%QD22QB%Q323Q8%QB2QD1%QH231&Q=%12Q<Q9p031pSJR91&Q<r;r:%37B21@Q6KQ0p051p0>1p0B1p0I1pQ<R61pQ8R71pSHR@1pT8RE1pTHRF1pT@RG1pLRF1").
Proof. intros LB sp x n W M M1.
intros FRZ STK BR INF.
apply (PMK.ek_piece_in RSEGS L KL LB sp 28672 W M M1 (fun a => (sp - 80 <= a < sp - 80 + 80) \/ (x <= a < x + n))
ltac:(intros a Ha N; apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X) STK (PMFR.brange_hi L LB BR)).
intros a [Pa|Pa]; [left; lia| right; apply INF; lia].
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmURdValA "Q4'R9yR0%211'3y8%511%311p051'9'5&QGzr1%3221&QH&QI+2+R0%3221%5271%;271'6r3&R8r2%22H1%411r4%113%83G31p0:1pT4G1%;3I8:p021pQ<K1pQ8L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F.
pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B.
Qed.
Theorem rv_partA : ltac2:(TCodec.tc2 tcn__PmURdValA "G&Q9vQEv<v:%43321&Q:%13543&Q;%13765&Q8&QD&Q2&Q1%112+8&Q3&Q4%2261&Q7%:9B98A@6521p0<1p0?1p0B1").
Proof.
intros BA BO MKE. unfold PMSP.run_spec, PMSP.run_spec_r.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11 & A13 & (t & Ht & TG & A12)). destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl13 in A13.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v in *. cbn [pa_off_p pa_off_is pa_off_ec pa_off_v AD PmLayoutU.ADDR_U] in *.
change (PMSP.pm_scr 8) with 28672 in *.
assert (SC0 : 0 <= 28672) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
pose proof (L5C.stk_writable RSEGS _ M sp 28672 STK) as WR.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (unfold LB, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
destruct (BR _ _ VIN) as (V0 & V1 & V4). unfold hl_ceil in V4.
assert (QI : forall a, qc <= a < qc + 16384 -> ~ (65536 <= a < 958464)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. intros a Ha. clear - Ha Q1. lia. }
assert (VI : forall a, vb <= a < vb + 32 * 2 ^ vk -> ~ (65536 <= a < 958464)).
{ rewrite (ly_img_lo L LY), (ly_img_hi L LY) in V1. intros a Ha. clear - Ha V1. lia. }
clear Q1 V1.
pose proof PA as (_ & PDEF & _).
set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (PINC : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl; apply incl_refl).
assert (AL36 : (fb + 40 + 24) mod 8 = 0) by (replace (fb + 40 + 24) with (fb + 8 * 8) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL55 : (fb + 440) mod 8 = 0) by (replace (fb + 440) with (fb + 8 * 55) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
set (WS := PMSP.W_srcf AD fb ++ [(qc, 16384)]).
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
assert (WRH : forall i, PMK.inW (PMSP.W_run AD fb) i -> (fb + 8 <= i < fb + 24) \/ (fb + 48 <= i < fb + 56) \/ (fb + 320 <= i < fb + 360) \/ (fb + 376 <= i < fb + 424) \/ (fb + 480 <= i < fb + 488) \/ (fb + 592 <= i < fb + 596) \/ (0xc72b0 <= i < 0xe8f18)).
{ intros i (r0 & Hin & Hr). unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_is, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
assert (NWS : forall a n, sp - 28672 <= a -> a + n <= fb + 320 -> forall i, a <= i < a + n -> ~ PMK.inW WS i).
{ intros a n H1 H2 i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 SLO. unfold hl_ceil in *. lia. }
assert (NWS2 : forall a n, fb + 360 <= a -> a + n <= fb + 480 -> forall i, a <= i < a + n -> ~ PMK.inW WS i).
{ intros a n H1 H2 i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 SLO F1. unfold hl_ceil in *. lia. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as B20.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (REMB : 0 <= rem <= 16384).
{ pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _) & _). cbn [s0 PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in G1, G2, G3.
unfold PM.CHUNK in G3. lia. }
unfold PMSP.cfg. cbn [pa_read_value AD PmLayoutU.ADDR_U].
assert (FIN : forall (fx1 : FPState) (R1 : bvmap 5 word) (pc1 : Z) (M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit)
(fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (m3 : Z),
PMSP.run_pre RSEGS AD M1 fb s1 str sm1 e1 -> PMSP.src_step (PM.p_src s0) (PM.p_src s1) (PM.STRM g eg st) sm1 -> (e = true -> e1 = true) ->
L5C.hpres L LBX sp 28672 (PMSP.W_run AD fb) M M1 -> PMSP.credit_keep cr cr1 (PM.pot_parser L s0) (PM.pot_parser L s1) ->
model_but_vm model model1 -> hi_heap HI (PM.parser_own s1 ++ LBX) cr1 M1 (m_vmmaps model1) ->
((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M1 (fb + 8) v (pa_errcat_obj AD) /\ m3 = 0 /\ e1 = true)
\/ (PMSP.ec_at RSEGS M1 (fb + 8) 0 cat /\ PM.inv s1 /\ m3 = 1 /\ PMSP.prog_value s0 s1 (PM.STRM g eg st) sm1)) ->
msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x3704c) M3 (seg_rom RSEGS)) -> mem_grows M1 M3 ->
(forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 40 + 8 <= i < fb + 40 + 8 + 1) -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
L5.u8_at RSEGS M3 (fb + 40 + 8) m3 ->
(forall x, In x PMK.cs_all -> getr R3 (PMK.reg x) = getr R (PMK.reg x)) -> getr R3 (PMK.reg 1) = getr R (PMK.reg 1) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K).
{ intros fx1 R1 pc1 M1 model1 s1 sm1 e1 cr1 fx3 R3 M3 m3 RPRE1 STEP1 EE1 HP1 CK1 MB1 HH1 POST1 MS3 MG3 FRZ3 Z8 KS3 T1.
pose proof (PMFR.model_ok_but_vm model model1 MOK MB1) as MOK1. pose proof MOK1 as (Mh1 & Ml1 & _).
destruct RPRE1 as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA1, IA1, VIS1, VREF1. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U] in PA1, IA1, VIS1, VREF1.
set (LB1 := PM.parser_own s1 ++ LBX) in *.
assert (BR1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH1); apply incl_refl).
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 28672) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 28672 sp 28672 _ STK HP1); lia).
apply (gl_step LB1 cr1 fx1 fx3 R1 R3 pc1 0x3704c M1 M3 model1 K sp (fb + 40 + 8) 1 HH1 Mh1 Ml1 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(right; unfold hl_ceil; lia) MS3 MG3 FRZ3).
intros HH3.
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh1| exact Ml1| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x3704c (ltac:(oW' 0x3704c%Z)) r (ltac:(oF' 0x3704c%Z)) eq_refl (ltac:(oD' 0x3704c%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (AG3 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 80 \/ sp <= a) -> (a + n <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M1 M3 a n).
{ intros a n H1 H2 H4 H5 i Hi. apply FRZ3; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia| clear - H5 Hi; lia]. }
assert (EK3 : PMK.ek L LB1 sp 28672 [(fb + 48, 1)] M1 M3).
{ apply (gl_ek LB1 sp (fb + 40 + 8) 1 [(fb + 48, 1)] M1 M3 FRZ3 STK1 BR1). intros a Ha. apply PMK.inW_here. lia. }
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 28672) by (apply (PMK.stk_grows L M1 M3 sp 28672 MG3 STK1)).
assert (SINC1 : incl (PM.vs_own str) LB1) by (unfold LB1; apply incl_appr; exact INCS).
assert (HM3 : m3 = 0 \/ m3 = 1) by (destruct POST1 as [(v & _ & _ & -> & _)|(_ & _ & -> & _)]; [left|right]; reflexivity).
destruct s1 as [mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1].
assert (VIN1 : In (vb1, 32 * 2 ^ vk1) LB1) by (unfold LB1, PM.parser_own, PM.vec_own; cbn; right; left; reflexivity).
destruct (BR1 _ _ VIN1) as (W0 & W1' & W4). unfold hl_ceil in W4.
assert (PA3 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M3 (fb + 40) (fb + 440) (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) m3)).
{ apply (PMPK.parser_more_upd RSEGS AD M1 M3 (fb + 40) (fb + 440) _ m3 PA1); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG3; lia.
- apply AG3; lia.
- apply PMPK.dkr_grows. exact MG3.
- exact Z8.
- exact HM3.
- apply PMPK.dkr_grows. exact MG3.
- lia.
- clear - W4 STOP. unfold hl_ceil in *. lia.
- apply AG3; [lia|clear - W4 STOP; unfold hl_ceil in *; lia| clear - W4 SLO F1; unfold hl_ceil in *; lia| clear - W4 SLO F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG3. }
apply (KONT fx3 R3 M3 model1 (PMPK.set_more (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 stk1) m3) sm1 e1 cr1).
- apply PMK.preserved_by_index. exact KS3.
- unfold PMSP.run_post, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutU.ADDR_U].
split; [|split; [exact STEP1|split; [exact EE1|]]].
+ split; [exact PA3|].
split.
{ apply (PMFR.iss_keep RSEGS AD L KL LB1 sp 28672 [(fb + 48, 1)] M1 M3 EK3 STK1 SC0 BR1); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| |exact SINC1| exact IA1].
intros i Hi I. apply PMFR.inW_inv1 in I. lia. }
split.
{ unfold PMSP.visitor_at in *. apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG3; lia|lia|lia| exact VIS1]. }
split.
{ apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG3; lia|lia|lia| exact VREF1]. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB1 sp 28672 [(fb + 48, 1)] M1 M3 EK3); [| | | | exact BASE1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha; clear - I Ha SLO STOP F1; lia. }
split; [|exact TB1].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB1 sp 28672 [(fb + 48, 1)] M1 M3 EK3); [| | exact ERR1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha; clear - I Ha SLO STOP F1; lia. }
+ destruct POST1 as [(v & Hv & ECv & -> & ->)|(EC1 & INV1 & -> & PV1)].
* left. exists v. split; [exact Hv|]. split; [|split; reflexivity].
apply (ec_agree M1 M3); [apply AG3; lia|lia|lia| exact ECv].
* right. pose proof INV1 as (IM1 & _). cbn [PM.p_more] in IM1. subst mo1.
split; [apply (ec_agree M1 M3); [apply AG3; lia|lia|lia| exact EC1]|]. split; [exact INV1| exact PV1].
- apply (PMK.hpres_of L LBX sp 28672 _ M M3).
+ apply (PMK.ek_trans L LBX sp 28672 _ M M1 M3 (PMK.ek_of_hpres L LBX sp 28672 _ M M1 HP1)).
apply (PMK.ek_weaken L LBX LB1 sp 28672 sp 28672 _ [(fb + 48, 1)] M1 M3 EK3); [unfold LB1; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
unfold PMSP.W_run, PMSP.o_p in O. cbn [pa_off_p AD PmLayoutU.ADDR_U app] in O. apply (O (fb + 40 + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ destruct STK3 as (_ & _ & _ & _ & D3). exact D3.
+ apply (PMK.dk_trans L LBX sp 28672 M M1 M3 (PMK.dk_of_hpres L LBX sp 28672 _ M M1 HP1)). apply (PMK.dk_grows L LBX sp 28672 M1 M3 MG3).
- exact CK1.
- exact MB1.
- exact HH3. }
assert (BRX : PMFR.brange L LBX) by (apply (PMFR.brange_incl L LBX LB BR); unfold LB; apply incl_appr; apply incl_refl).
pose proof PA as (PVP & _ & _ & P8 & P9 & P12 & P16 & P20 & _).
pose proof INV as (IM & ID & _). cbn [s0 PM.p_more PM.p_done] in IM, ID, P8, P9.
pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in IMG.
unfold PMSP.visitor_at in VIS. cbn [pa_vp_visitor AD PmLayoutU.ADDR_U] in VIS.
assert (WP : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]).
pose proof EC0 as (EC0v & EC08 & EC0D).
assert (RPRE0 : PMSP.run_pre RSEGS AD M fb s0 str (PM.STRM g eg st) e).
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [exact PA|]. split; [exact IA|]. split; [unfold PMSP.visitor_at; cbn [pa_vp_visitor AD PmLayoutU.ADDR_U]; exact VIS|].
split; [exact VREF|]. split; [exact BASE|]. split; [exact ERR| exact TBOK]. }
assert (SSR0 : PMSP.src_step (PM.p_src s0) (PM.p_src s0) (PM.STRM g eg st) (PM.STRM g eg st)).
{ unfold PMSP.src_step, PM.unread. cbn [s0 PM.p_src PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros E; exact E| lia]. }
assert (HP00 : L5C.hpres L LBX sp 28672 (PMSP.W_run AD fb) M M) by (apply (PMK.hpres_of L LBX sp 28672 _ M M); [apply PMK.ek_refl| exact SDEF| apply PMK.dk_refl]).
assert (CK00 : PMSP.credit_keep cr cr (PM.pot_parser L s0) (PM.pot_parser L s0)) by (unfold PMSP.credit_keep; split; lia).
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (KEEPF : forall M1, mem_grows M M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
PMSP.run_pre RSEGS AD M1 fb s0 str (PM.STRM g eg st) e /\ L5C.hpres L LBX sp 28672 (PMSP.W_run AD fb) M M1 /\ PMSP.ec_at RSEGS M1 (fb + 8) 0 cat
/\ PMK.ek L LB sp 28672 [] M M1 /\ L5C.stk (hl_sptop L) M1 sp 28672).
{ intros M1 MG1 FRZ1.
assert (EK1f : PMK.ek L LB sp 28672 [] M M1).
{ apply (PMFR.ek_of_piece RSEGS L KL LB sp 28672 M M1 (fun a => sp - 80 <= a < sp - 80 + 80) ltac:(intros a Ha N; apply FRZ1; [exact Ha| exact N]) STK (PMFR.brange_hi L LB BR)). intros a Pa. lia. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 28672) by (apply (PMK.stk_grows L M M1 sp 28672 MG1 STK)).
assert (AG01 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n) by (intros a n H1 H2 i Hi; apply FRZ1; lia).
split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutU.ADDR_U].
split; [apply (PMFR.parser_keep RSEGS AD L KL LB sp 28672 [] M M1 EK1f STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact PINC| exact PA]|].
split; [apply (PMFR.iss_keep RSEGS AD L KL LB sp 28672 [] M M1 EK1f STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]|].
split; [unfold PMSP.visitor_at; cbn [pa_vp_visitor AD PmLayoutU.ADDR_U]; apply (L5C.u64_at_agree RSEGS M M1); [apply AG01; lia|lia|lia| exact VIS]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG01; lia|lia|lia| exact VREF]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 28672 [] M M1 EK1f); first [exact BASE | intros a _; apply L5C.outside_nil]|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF LB sp 28672 [] M M1 EK1f); first [exact ERR | intros a _; apply L5C.outside_nil]| exact TBOK]. }
split.
{ apply (PMK.hpres_of L LBX sp 28672 _ M M1).
- apply (PMK.ek_weaken L LBX LB sp 28672 sp 28672 _ [] M M1 EK1f); [unfold LB; apply incl_appr; apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
- destruct STK1 as (_ & _ & _ & _ & D1). exact D1.
- apply (PMK.dk_grows L LBX sp 28672 M M1 MG1). }
split; [apply (ec_agree M M1); [apply AG01; lia|lia|lia| exact EC0]|].
split; [exact EK1f| exact STK1]. }
assert (RUNF : forall M1 s1 sm1 e1, PMSP.run_pre RSEGS AD M1 fb s1 str sm1 e1 ->
L5.u64_at RSEGS M1 (fb + 432) 721464 /\ L5.u8_at RSEGS M1 (fb + 40 + 16) 0 /\ L5.writable RSEGS M1 (fb + 40) 384 /\ L5.img_clear M1 65536 749856
/\ PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s1 /\ PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str sm1 /\ PMST.base_ok RSEGS AD M1
/\ PMST.err_ok RSEGS AD M1 e1).
{ intros M1 s1 sm1 e1 (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & TB1).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA1, IA1, VIS1. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutU.ADDR_U] in PA1, IA1, VIS1.
split; [exact VIS1|]. split; [destruct PA1 as (_ & _ & _ & _ & _ & _ & X & _); exact X|].
split; [apply (L5C.writable_of_defined RSEGS); [destruct PA1 as (_ & X & _); exact X|lia|lia]|].
split; [destruct BASE1 as (X & _); cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in X; exact X|].
split; [exact PA1|]. split; [exact IA1|]. split; [exact BASE1| exact ERR1]. }
assert (LIFT : forall (M1 M2 : word -> option byte) (scr' : Z), L5C.hpres L LBX sp 28672 (PMSP.W_run AD fb) M M1 -> L5C.stk (hl_sptop L) M1 (sp - 80) scr' ->
0 <= scr' -> scr' + 80 <= 28672 -> L5C.hpres L LBX (sp - 80) scr' (PMSP.W_run AD fb) M1 M2 ->
L5C.hpres L LBX sp 28672 (PMSP.W_run AD fb) M M2 /\ (forall a n, sp - 80 <= a -> a + n <= fb + 8 -> L5C.agree_on M1 M2 a n) /\ L5C.stk (hl_sptop L) M2 sp 28672
/\ (forall a n, fb + 424 <= a -> a + n <= fb + 440 -> L5C.agree_on M1 M2 a n)).
{ intros M1 M2 scr' HP1 STKc S0 S1 HP2.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 28672) by (apply (PMK.stk_after RSEGS L KL LBX M M1 sp 28672 sp 28672 _ STK HP1); lia).
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 28672) by (apply (PMK.stk_after RSEGS L KL LBX M1 M2 sp 28672 (sp - 80) scr' _ STK1 HP2); lia).
pose proof STK2 as (_ & _ & _ & _ & SD2).
split; [|split; [|split; [exact STK2|]]].
- apply (PMK.hpres_of L LBX sp 28672 _ M M2).
+ apply (PMK.ek_trans L LBX sp 28672 _ M M1 M2 (PMK.ek_of_hpres L LBX sp 28672 _ M M1 HP1)).
apply (PMK.ek_callee_in' RSEGS L KL LBX LBX sp 28672 (sp - 80) scr' _ _ M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LBX BRX)|].
intros a I. right. exact I.
+ exact SD2.
+ apply (PMK.dk_trans L LBX sp 28672 M M1 M2 (PMK.dk_of_hpres L LBX sp 28672 _ M M1 HP1)).
apply (PMK.dk_callee L LBX LBX sp 28672 (sp - 80) scr' _ M1 M2 HP2 (incl_refl _)); lia.
- intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LBX (sp - 80) scr' (PMSP.W_run AD fb) M1 M2 (PMK.ek_of_hpres L LBX (sp - 80) scr' _ M1 M2 HP2) STKc S0 a n H1); [lia|].
intros i Hi I. apply WRH in I. clear - Hi I H1 H2 F1 SLO STOP. lia.
- intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LBX (sp - 80) scr' (PMSP.W_run AD fb) M1 M2 (PMK.ek_of_hpres L LBX (sp - 80) scr' _ M1 M2 HP2) STKc S0 a n); [lia|lia|].
intros i Hi I. apply WRH in I. clear - Hi I H1 H2 F1 SLO STOP. lia. }
unfold PMSRVD.rvA in TG. destruct TG as [E|E].
- subst t.
cfeed P (PMURVP.ruTA_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMURVP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_2 & Xa_8 & Xa_9 & Xa_12 & Xa_18 & Ca_48 & Ca_40 & Ca_32 & Ca_24 & Ca_16 & Ca_8)); PMK.pvz_clrT.
apply (gl_step LB cr fx fxa R Ra 0x36afc 0x37e78 M Ma model K sp 0 0 HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(left; reflexivity) MSa MGa (fun i Hi N1 _ => FRZa i Hi N1)).
intros HHa.
destruct (KEEPF Ma MGa FRZa) as (RPREa & HPa & ECa & _ & STKa).
assert (STKc : L5C.stk (hl_sptop L) Ma (sp - 80) 26624).
{ apply (PMK.stk_call L Ma sp 28672 (sp - 80) 26624); [apply (PMK.stk_after RSEGS L KL LBX M Ma sp 28672 sp 28672 _ STK HPa); lia|lia|lia|lia|].
replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.begin_array_spec, PMSP.begin_array_spec, PMSP.run_spec, PMSP.run_spec_r in BA. cbn [pa_begin_array AD PmLayoutU.ADDR_U] in BA.
apply (BA fxa Ra Ma model K LBX cr (sp - 80) 224712 fb cat s0 str (PM.STRM g eg st) e HHa MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPREa. } { exact INCS. }
{ exact INV. } { exact ECa. } { exact UNR. } { exact CRED. }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 7) with 26624 in HP2.
destruct (LIFT Ma M2 26624 HPa STKc ltac:(lia) ltac:(lia) HP2) as (HP02 & AG2 & STK2 & _).
pose proof (L5C.stk_writable RSEGS _ M2 sp 28672 STK2) as WR2.
assert (D8 : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_8]).
assert (D16 : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_16]).
assert (D24 : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_24]).
assert (D32 : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_32]).
assert (D40 : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_40]).
assert (D48 : L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_48]).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)]).
all: destruct (RUNF M2 s2 sm2 e2 RPRE2) as (VIS2 & P16b & WP2 & IMG2 & PA2 & _).
2: {
pose proof EC2 as (EC2v & _).
cfeed P (PMURVP.ruA0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMURVP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_1 & Xb_2 & Xb_8 & Xb_9 & Xb_10 & Xb_18 & Xb_19 & Xb_20)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xb_1.
try rewrite PMPK.word_id in Xb_2.
try rewrite PMPK.word_id in Xb_8.
try rewrite PMPK.word_id in Xb_9.
try rewrite PMPK.word_id in Xb_10.
try rewrite PMPK.word_id in Xb_18.
try rewrite PMPK.word_id in Xb_19.
try rewrite PMPK.word_id in Xb_20.
assert (Mb = M2) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (FIN fx2 R2 0x36dc8 M2 model2 s2 sm2 e2 cr2 fxb Rb M2 1 RPRE2 STEP2 EE2 HP02 CK2 MB2 HH2).
+ right. split; [exact EC2|]. split; [exact INV2|]. split; [reflexivity| exact PV2].
+ exact MSb.
+ exact MGb.
+ intros i _ _ _. reflexivity.
+ pose proof INV2 as (IM2 & _). pose proof PA2 as (_ & _ & _ & X & _). rewrite IM2 in X. exact X.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ PMK.rk | (rewrite Xb_2; symmetry; exact Rsp) ] |]). destruct Hx.
+ PMK.rk.
}
pose proof ECv as (ECvv & _).
cfeed P (PMURVP.ruAe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 39%nat => v | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMURVP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_1 & Xc_2 & Xc_8 & Xc_9 & Xc_10 & Xc_18 & Xc_19 & Xc_20 & Zc)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xc_1.
try rewrite PMPK.word_id in Xc_2.
try rewrite PMPK.word_id in Xc_8.
try rewrite PMPK.word_id in Xc_9.
try rewrite PMPK.word_id in Xc_10.
try rewrite PMPK.word_id in Xc_18.
try rewrite PMPK.word_id in Xc_19.
try rewrite PMPK.word_id in Xc_20.
apply (FIN fx2 R2 0x36dc8 M2 model2 s2 sm2 e2 cr2 fxc Rc Mc 0 RPRE2 STEP2 EE2 HP02 CK2 MB2 HH2).
+ left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [reflexivity| exact E2].
+ exact MSc.
+ exact MGc.
+ intros i Hi _ N2. exact (FRZc i Hi N2).
+ exact Zc.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ PMK.rk | (rewrite Xc_2; symmetry; exact Rsp) ] |]). destruct Hx.
+ PMK.rk.
- subst t.
cfeed P (PMURVP.ruTO_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMURVP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_1 & Xa_2 & Xa_8 & Xa_9 & Xa_12 & Xa_18 & Ca_48 & Ca_40 & Ca_32 & Ca_24 & Ca_16 & Ca_8)); PMK.pvz_clrT.
apply (gl_step LB cr fx fxa R Ra 0x36afc 0x38324 M Ma model K sp 0 0 HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(left; reflexivity) MSa MGa (fun i Hi N1 _ => FRZa i Hi N1)).
intros HHa.
destruct (KEEPF Ma MGa FRZa) as (RPREa & HPa & ECa & _ & STKa).
assert (STKc : L5C.stk (hl_sptop L) Ma (sp - 80) 26624).
{ apply (PMK.stk_call L Ma sp 28672 (sp - 80) 26624); [apply (PMK.stk_after RSEGS L KL LBX M Ma sp 28672 sp 28672 _ STK HPa); lia|lia|lia|lia|].
replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.begin_object_spec, PMSP.begin_object_spec, PMSP.run_spec, PMSP.run_spec_r in BO. cbn [pa_begin_object AD PmLayoutU.ADDR_U] in BO.
apply (BO fxa Ra Ma model K LBX cr (sp - 80) 224252 fb cat s0 str (PM.STRM g eg st) e HHa MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [PMK.rk|]. split; [split; [lia| reflexivity]|]. split; [PMK.rk|].
split; [transitivity (getr R (PMK.reg 3)); [PMK.rk| exact Rgp]|]. split; [transitivity (getr R (PMK.reg 4)); [PMK.rk| exact Rtp]|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U]. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [PMK.rk|]. split; [PMK.rk| PMK.rk]. }
{ exact RPREa. } { exact INCS. }
{ exact INV. } { exact ECa. } { exact UNR. } { exact CRED. }
intros fx2 R2 M2 model2 s2 sm2 e2 cr2 RP2 RPOST2 HP2 CK2 MB2 HH2.
change (PMSP.pm_scr 7) with 26624 in HP2.
destruct (LIFT Ma M2 26624 HPa STKc ltac:(lia) ltac:(lia) HP2) as (HP02 & AG2 & STK2 & _).
pose proof (L5C.stk_writable RSEGS _ M2 sp 28672 STK2) as WR2.
assert (D8 : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_8]).
assert (D16 : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_16]).
assert (D24 : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_24]).
assert (D32 : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_32]).
assert (D40 : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_40]).
assert (D48 : L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS Ma M2); [apply AG2; lia|lia|lia| exact Ca_48]).
destruct RPOST2 as (RPRE2 & STEP2 & EE2 & [(v & Hv & ECv & MO2 & E2)|(EC2 & INV2 & PV2)]).
all: destruct (RUNF M2 s2 sm2 e2 RPRE2) as (VIS2 & P16b & WP2 & IMG2 & PA2 & _).
2: {
pose proof EC2 as (EC2v & _).
cfeed P (PMURVP.ruO0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMURVP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxb & Rb & Mb & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGb & _ & FRZb & MSb & KSb & Xb_1 & Xb_2 & Xb_8 & Xb_9 & Xb_10 & Xb_18 & Xb_19 & Xb_20)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xb_1.
try rewrite PMPK.word_id in Xb_2.
try rewrite PMPK.word_id in Xb_8.
try rewrite PMPK.word_id in Xb_9.
try rewrite PMPK.word_id in Xb_10.
try rewrite PMPK.word_id in Xb_18.
try rewrite PMPK.word_id in Xb_19.
try rewrite PMPK.word_id in Xb_20.
assert (Mb = M2) as -> by (apply mem_eq_of_frz; exact FRZb).
apply (FIN fx2 R2 0x36bfc M2 model2 s2 sm2 e2 cr2 fxb Rb M2 1 RPRE2 STEP2 EE2 HP02 CK2 MB2 HH2).
+ right. split; [exact EC2|]. split; [exact INV2|]. split; [reflexivity| exact PV2].
+ exact MSb.
+ exact MGb.
+ intros i _ _ _. reflexivity.
+ pose proof INV2 as (IM2 & _). pose proof PA2 as (_ & _ & _ & X & _). rewrite IM2 in X. exact X.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ PMK.rk | (rewrite Xb_2; symmetry; exact Rsp) ] |]). destruct Hx.
+ PMK.rk.
}
pose proof ECv as (ECvv & _).
cfeed P (PMURVP.ruOe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | 39%nat => v | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMURVP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxc & Rc & Mc & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGc & _ & FRZc & MSc & KSc & Xc_1 & Xc_2 & Xc_8 & Xc_9 & Xc_10 & Xc_18 & Xc_19 & Xc_20 & Zc)); PMK.pvz_clrT.
try rewrite PMPK.word_id in Xc_1.
try rewrite PMPK.word_id in Xc_2.
try rewrite PMPK.word_id in Xc_8.
try rewrite PMPK.word_id in Xc_9.
try rewrite PMPK.word_id in Xc_10.
try rewrite PMPK.word_id in Xc_18.
try rewrite PMPK.word_id in Xc_19.
try rewrite PMPK.word_id in Xc_20.
apply (FIN fx2 R2 0x36bfc M2 model2 s2 sm2 e2 cr2 fxc Rc Mc 0 RPRE2 STEP2 EE2 HP02 CK2 MB2 HH2).
+ left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [reflexivity| exact E2].
+ exact MSc.
+ exact MGc.
+ intros i Hi _ N2. exact (FRZc i Hi N2).
+ exact Zc.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ PMK.rk | (rewrite Xc_2; symmetry; exact Rsp) ] |]). destruct Hx.
+ PMK.rk.
Qed.
End WithHeap.
End PMURVA.
