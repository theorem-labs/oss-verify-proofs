(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmParStep PmUGetLenP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUGetLen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmFrame.PMFR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LB"; "4Model"; "4m_halted"]; ["4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0R"; "0R1"; "6msteps"; "7credit"; "7hi_heap"; "7hl_sptop"; "8agree_on"; "8stk"; ":range"; "9SCFG"]; [";brange"; "<src_read_spec"; "=cfg"; "=ec_at"; ">get_length_spec"; ">make_ec_spec"; "?ek"; "?inW"; "@FPState"; "@mkst"; "@seg_rom"; "ATSet"; "Bsrealizes"; "Cmem_grows"; "Dloaded_segments"; "0SCFG_P"]; ["Eadd"; "Ele"; "Elt"; "Epow"; "Esub"; "0W"; "0a"; "0c"; "0cr"; "0fx"; "0fx1"; "0i"; "0model"; "0n"; "0o"; "0pc"]; ["0pc1"; "0sp"; "FZ_to_bv"; "Fbv"; "0v"; "0x"; "0x0"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMUGL.
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
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmUGetLen "Q9'R3yR0%211'3y8%511%311p051'9&Lr5r4r3+@%544321&QAz%2216&Q@%1296&QC+2+R0%3221%9251&Q3&Q>r8r6%45321CBr7%655413Ep031p091p0A1p0E1pS@L1pT:M1pSNN1pQ:Q01pQ8Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma gl_step : ltac2:(TCodec.tc2 tcn__PmUGetLen "U1'1'4'9%2211%411&I'Q8&By5'R3yR0%211%5241'3y8%611%311p061'>&Q;&Jv:r?r>r7&Ar5%211%8576541'6%A1C&?r6%211(0%11H%73631%Q42JJ%Q611&@%11@(2%115%>3531&QA+SoonPPPPP0&Kv<%211%5241&QD+XPPP0%2241+R0%42N1%;231r8%=219'8z%O3QJQ41'5%B2:6&Q@%128Q8%E21A%5241%9271'H&Q>&Q9rDrB&R2r@%22R11&Q:%118%85763QG1rCrA%82R7QKr=%=543216%@3?61&Q=%12R0QOr1%Q<2M1&QB&QC+2%221Q7%4261%Q1261&7%Q>2R9Q;r2%QF221%Q423Q>%;231%Q8231%711r3%QL2RA1%Q:2RBG%A231%Q>231%=11r4%Q52S41%Q011%Q912%RD3S121p061p0=1p0F1pSHSC1rIrH%RO1S2%S55S432Q?1'Q<&OvQ?%211&Q2rGrE%36QL21QBQAQG%84QM51S<p0:1rF%76R0>1QNQMQK%<4R191S@p041p0C1p0QC1p0QF1p0R81p0RC1p0RF1p0RM1p0S41p0S<1p0SE1pSLT@1pT<TA1pT4TB1pHT21pSJT41pQ<T61pQ8T71pT2TG1pT0TH1pQ@T?1pQ>T@1pSFTG1pSDTH1pSBTJ1pLTL1").
Proof. intros LB cr fx fx1 R R1 pc pc1 M M1 model K sp x n.
intros HH Mh Ml TOP H1 H2 H3 MS MG FRZ KONT.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R pc R1 pc1 M1
(fun a => (sp - 64 <= a < sp - 64 + 64) \/ (x <= a < x + n)) K HH Mh Ml TOP MS MG).
- intros a Ha N. apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X.
- intros a Pa. unfold PMK.cwr. left. destruct Pa as [Pa|Pa]; [lia|]. destruct H3 as [H3|H3]; lia.
- intros a. apply PMK.or_dec; apply PMK.rng_dec.
- exact KONT.
Qed.
Lemma gl_ek : ltac2:(TCodec.tc2 tcn__PmUGetLen "RJ'1'4'9%2211%411&N%611'R3yR0%211'3y8%511%311pT>51'5&QAzr1%3221&QB&QC+2+R0%3221%5271%;271&7&QDr8%2217r2%@221&Q@%124;%?241%E241%:11r3%G2:1r7%82<1%F241%L241%A11'6r5&R2r4%22Q91%411r6%113%83Q831p0:1p0B1p0N1pSHQG1&M&Kv<%211+fP0%542IG1&Q0r9%2261%QC22QA%Q323Q7%QA2QC1%QG231&Q7%12Q;Q9p031pS>R81&Q6r;r:%37B21@Q6KQ0p051p0>1p0B1p0I1pQ<R51pQ8R61pS<R?1pSLRD1pT<RE1pT4RF1pLRE1").
Proof. intros LB sp x n W M M1.
intros FRZ STK BR INF.
apply (PMK.ek_piece_in RSEGS L KL LB sp 22528 W M M1 (fun a => (sp - 64 <= a < sp - 64 + 64) \/ (x <= a < x + n))
ltac:(intros a Ha N; apply FRZ; [exact Ha| |]; intros X; apply N; [left|right]; exact X) STK (PMFR.brange_hi L LB BR)).
intros a [Pa|Pa]; [left; lia| right; apply INF; lia].
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmUGetLen "Q4'R3yR0%211'3y8%511%311p051'9'5&QAzr1%3221&QB&QC+2+R0%3221%5271%;271'6r3&R2r2%22H1%411r4%113%83G31p0:1pSHG1%;3I8:p021pQ<K1pQ8L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F.
pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B.
Qed.
Theorem get_length_ok : ltac2:(TCodec.tc2 tcn__PmUGetLen ";&Q1vQ?v<v:%43321&Q5%13543&Q4%13765p031p061").
Proof.
intros SR MKE. unfold PMU.get_length_spec, PMSP.get_length_spec, PMSP.run_spec_rd.
intros dd Hdd fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11). destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v in *. cbn [pa_off_p pa_off_is pa_off_ec pa_off_v AD PmLayoutU.ADDR_U] in *.
change (PMSP.pm_scr 5) with 22528 in *.
assert (SC0 : 0 <= 22528) by lia.
set (LB := PM.parser_own s ++ LBX) in *.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
pose proof (L5C.stk_writable RSEGS _ M sp 22528 STK) as WR.
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
set (WS := PMSP.W_srcf AD fb ++ [(qc, 16384)]).
assert (WCs : forall a, PMK.inW WS a -> (fb + 320 <= a < fb + 360) \/ (fb + 480 <= a < fb + 488) \/ (fb + 592 <= a < fb + 596) \/ (qc <= a < qc + 16384)).
{ intros a (r0 & Hin & Hr). unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is in Hin. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
assert (NWS : forall a n, sp - 22528 <= a -> a + n <= fb + 320 -> forall i, a <= i < a + n -> ~ PMK.inW WS i).
{ intros a n H1 H2 i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 SLO. unfold hl_ceil in *. lia. }
assert (NWS2 : forall a n, fb + 360 <= a -> a + n <= fb + 480 -> forall i, a <= i < a + n -> ~ PMK.inW WS i).
{ intros a n H1 H2 i Hi I. apply WCs in I. clear - Hi H1 H2 I Q4 SLO F1. unfold hl_ceil in *. lia. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as B19.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (REMB : 0 <= rem <= 16384).
{ pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _) & _). cbn [s0 PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in G1, G2, G3.
unfold PM.CHUNK in G3. lia. }
unfold PMSP.cfg. cbn [pa_get_length AD PmLayoutU.ADDR_U].
assert (RD : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (de1 rem1 : Z) (sm1 : PM.strm) (q kk rr : Z),
getr R1 (PMK.reg 1) = Z_to_bv 64 rr -> L5.ra_ok rr -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64) ->
getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 24) -> getr R1 (PMK.reg 11) = Z_to_bv 64 q -> getr R1 (PMK.reg 12) = Z_to_bv 64 kk ->
getr R1 (PMK.reg 3) = getr R (PMK.reg 3) -> getr R1 (PMK.reg 4) = getr R (PMK.reg 4) ->
sp - 64 <= q -> q + kk <= sp - 40 -> 1 <= kk <= 8 ->
PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PMPS.with_src s0 (PM.SRC qc de1 rem1)) ->
PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str sm1 -> PMST.base_ok RSEGS AD M1 -> PMST.err_ok RSEGS AD M1 e ->
PMSP.src_step (PM.SRC qc de rem) (PM.SRC qc de1 rem1) (PM.STRM g eg st) sm1 ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
PMK.ek L LB sp 22528 WS M M1 -> PMK.dk L LB sp 22528 M M1 -> L5C.stk (hl_sptop L) M1 sp 22528 -> hi_heap HI LB cr M1 (m_vmmaps model) ->
(forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (de2 rem2 d : Z) (sm2 : PM.strm),
regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 d -> 0 <= d <= kk ->
PM.unread (PM.SRC qc de2 rem2) sm2 = PM.unread (PM.SRC qc de1 rem1) sm1 - d ->
PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M2 (fb + 40) (fb + 440) (PMPS.with_src s0 (PM.SRC qc de2 rem2)) ->
PM.iss_at RSEGS AD PMSP.T3 M2 (fb + 440) str sm2 -> PMST.base_ok RSEGS AD M2 -> PMST.err_ok RSEGS AD M2 e ->
PMSP.src_step (PM.SRC qc de rem) (PM.SRC qc de2 rem2) (PM.STRM g eg st) sm2 ->
L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
PMK.ek L LB sp 22528 WS M M2 -> PMK.dk L LB sp 22528 M M2 -> L5C.stk (hl_sptop L) M2 sp 22528 -> hi_heap HI LB cr M2 (m_vmmaps model) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 rr M2 model) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x374b8 M1 model) K).
{ intros fx1 R1 M1 de1 rem1 sm1 q kk rr X1 RA1 X2 X10 X11 X12 X3 X4 Hq1 Hq2 Hkk PA1 IA1 BASE1 ERR1 STEP1 C8 C16 C24 C32 C40 EK1 DK1 STK1 HH1 KONT1.
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 64) 20480).
{ apply (PMK.stk_call L M1 sp 22528 (sp - 64) 20480 STK1); [lia|lia|lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
pose proof (L5C.stk_writable RSEGS _ M1 sp 22528 STK1) as WR1.
destruct STK1 as (_ & _ & _ & _ & SD1).
unfold PMPSU.src_read_spec, PMPS.src_read_spec, PMPS.src_spec in SR. cbn [pa_src_read AD PmLayoutU.ADDR_U] in SR.
apply (SR fx1 R1 M1 model K LBX cr (sp - 64) rr fb (PMPS.with_src s0 (PM.SRC qc de1 rem1)) str sm1 [(q, kk)] HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
split; [rewrite X3; exact Rgp|]. split; [rewrite X4; exact Rtp|]. exact STKc. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD PmLayoutU.ADDR_U]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_src, PMSP.o_p. cbn [pa_off_p AD PmLayoutU.ADDR_U]. exact X10. }
{ unfold PMPS.read_args. exists q, kk. rewrite L5K.rl11, L5K.rl12. split; [exact X11|]. split; [exact X12|]. split; [unfold PM.CHUNK; lia|].
unfold PMPS.read_dst. left. split; [lia|]. split; [lia|]. split; [lia|]. apply (L5.defined_sub M1 (sp - 22528) 22528); [exact SD1|lia|lia]. }
{ unfold PMPS.read_W. exists q, kk. rewrite L5K.rl11, L5K.rl12. split; [exact X11|]. split; [exact X12|]. split; [lia|]. split; [lia| reflexivity]. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U]. exact PA1. }
{ unfold PMSP.o_is. cbn [pa_off_is AD PmLayoutU.ADDR_U]. exact IA1. }
{ exact BASE1. } { exact INCS. }
intros fx2 R2 M2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 HH2.
unfold PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U] in PA2, IA2.
change (PMSP.pm_scr 4) with 20480 in HP2.
destruct src2 as [qc2 de2 rem2].
assert (QC2 : qc2 = qc) by (destruct STEP2 as (E & _); exact E). subst qc2.
unfold PMPS.read_res, PMSP.consumed in RES2. destruct RES2 as (p' & k' & d' & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & _).
assert (pk : p' = q /\ k' = kk).
{ change (getr R1 (PMK.reg 11) = Z_to_bv 64 p') in Y11. change (getr R1 (PMK.reg 12) = Z_to_bv 64 k') in Y12.
rewrite X11 in Y11. rewrite X12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
assert (CONS' : PMSP.consumed (PM.SRC qc de1 rem1) (PM.SRC qc de2 rem2) sm1 sm2 = d') by exact CONS.
destruct pk as (-> & ->). change (getr R2 (PMK.reg 10) = Z_to_bv 64 d') in Y10.
set (Wq := PMSP.W_src AD fb (PM.SRC qc de1 rem1) ++ [(q, kk)]) in HP2.
assert (EKc : PMK.ek L LB (sp - 64) 20480 Wq M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 20480) by lia.
assert (WCq : forall a, PMK.inW Wq a -> PMK.inW WS a \/ (q <= a < q + kk)).
{ intros a (r0 & Hin & Hr). unfold Wq in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [left; exists r0; split; [exact Hin| exact Hr]| right; exact Hr]. }
assert (HI2 : forall a n, sp - 64 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WS i) -> (forall i, a <= i < a + n -> ~ (q <= i < q + kk)) ->
L5C.agree_on M1 M2 a n).
{ intros a n H1 H2 N1 N2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 64) 20480 Wq M1 M2 EKc STKc SCc a n H1 H2). intros i Hi I.
destruct (WCq i I) as [I'|I']; [exact (N1 i Hi I')| exact (N2 i Hi I')]. }
assert (NQ : forall a n, sp - 40 <= a -> forall i, a <= i < a + n -> ~ (q <= i < q + kk)) by (intros a n H i Hi X; lia).
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 22528) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 22528 (sp - 64) 20480 Wq (conj A16 (conj SLO (conj SHI (conj STOP SD1)))) HP2); lia).
pose proof STK2 as (_ & _ & _ & _ & SD2).
apply (KONT1 fx2 R2 M2 de2 rem2 (PMSP.consumed (PM.SRC qc de1 rem1) (PM.SRC qc de2 rem2) sm1 sm2) sm2 RP2).
- rewrite CONS'. exact Y10.
- rewrite CONS'. exact Hd.
- unfold PMSP.consumed. lia.
- exact PA2.
- exact IA2.
- apply (PMKP.base_ok_keep RSEGS AD L KL SF LB (sp - 64) 20480 Wq M1 M2 EKc); [| | | | exact BASE1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; destruct (WCq a I) as [I'|I']; [apply WCs in I'|];
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha.
all: first [ destruct I' as [I'|[I'|[I'|I']]]; [clear - I' Ha SLO F1 STOP; lia ..| apply (QI a I'); clear - Ha; lia] | clear - I' Ha SLO Hq1 STOP; lia ].
- apply (PMKP.err_ok_keep RSEGS AD L KL SF LB (sp - 64) 20480 Wq M1 M2 EKc); [| | exact ERR1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; destruct (WCq a I) as [I'|I']; [apply WCs in I'|];
cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha.
all: first [ destruct I' as [I'|[I'|[I'|I']]]; [clear - I' Ha SLO F1 STOP; lia ..| apply (QI a I'); clear - Ha; lia] | clear - I' Ha SLO Hq1 STOP; lia ].
- unfold PMSP.src_step, PM.unread in STEP1, STEP2 |- *. cbn [PMPS.with_src PM.p_src PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st] in STEP1, STEP2 |- *.
destruct STEP1 as (_ & E1 & L1 & S1 & U1). destruct STEP2 as (_ & E2 & L2 & S2 & U2).
split; [reflexivity|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; [lia|lia| apply NWS; lia| apply NQ; lia]|lia|lia| exact C8].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; [lia|lia| apply NWS; lia| apply NQ; lia]|lia|lia| exact C16].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; [lia|lia| apply NWS; lia| apply NQ; lia]|lia|lia| exact C24].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; [lia|lia| apply NWS; lia| apply NQ; lia]|lia|lia| exact C32].
- apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; [lia|lia| apply NWS; lia| apply NQ; lia]|lia|lia| exact C40].
- apply (PMK.ek_trans L LB sp 22528 WS M M1 M2 EK1).
apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 22528 (sp - 64) 20480 WS Wq M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. destruct (WCq a I) as [I'|I']; [right; exact I'| left; lia].
- apply (PMK.dk_trans L LB sp 22528 M M1 M2 DK1).
apply (PMK.dk_callee L LB LB sp 22528 (sp - 64) 20480 Wq M1 M2 HP2 (incl_refl _)); lia.
- exact STK2.
- exact HH2. }
assert (OWNF : forall B m, In (B, m) (PM.parser_own s0) -> B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B).
{ intros B m Hin. assert (HB : In (B, m) LB) by (apply PINC; exact Hin). destruct (BR B m HB) as (Z0 & Z1 & Z4).
split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
assert (HB' : In (B', m') LB) by (unfold LB; apply in_or_app; right; exact Hin').
assert (NE : B <> B') by (apply (PMPK.fst_neq_app (PM.parser_own s0) LBX B m B' m' NDL Hin Hin')).
exact (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m B' m' HH HB HB' NE). }
assert (FINW : forall M3 W3, PMK.ek L LB sp 22528 W3 M M3 -> PMK.dk L LB sp 22528 M M3 -> L5C.stk (hl_sptop L) M3 sp 22528 ->
(forall a, PMK.inW W3 a -> PMK.inW (PMSP.W_run AD fb) a \/ (qc <= a < qc + 16384)) ->
L5C.hpres L LBX sp 22528 (PMSP.W_run AD fb) M M3).
{ intros M3 W3 EK3 DK3 STK3 HW. apply (PMK.hpres_of L LBX sp 22528 _ M M3).
- apply (PMPK.ek_drop_own L (PM.parser_own s0) LBX sp 22528 (PMSP.W_run AD fb) W3 M M3 EK3 OWNF).
intros a O. destruct (PMK.rng_dec a qc (qc + 16384)) as [IQ|NQ].
+ right. exists qc, 16384. split; [unfold s0, PM.parser_own, PM.src_own; cbn; left; reflexivity| exact IQ].
+ left. intros r0 Hr0 Hin. destruct (HW a (ex_intro _ r0 (conj Hr0 Hin))) as [I'|I']; [exact (PMK.inW_not_outside _ a I' O)| exact (NQ I')].
- destruct STK3 as (_ & _ & _ & _ & D3). exact D3.
- apply (PMPK.dk_incl L LBX LB sp 22528 M M3 DK3). unfold LB. apply incl_appr. apply incl_refl. }
assert (WSR : forall a, PMK.inW WS a -> PMK.inW (PMSP.W_run AD fb) a \/ (qc <= a < qc + 16384)).
{ intros a I. apply WCs in I. destruct I as [I|[I|[I|I]]]; [left|left|left|right; exact I].
all: unfold PMSP.W_run, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is; cbn [pa_off_p pa_off_is AD PmLayoutU.ADDR_U app].
- apply PMK.inW_next. apply PMK.inW_here. lia.
- do 2 apply PMK.inW_next. apply PMK.inW_here. lia.
- do 3 apply PMK.inW_next. apply PMK.inW_here. lia. }
assert (OKP : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (de1 rem1 : Z) (sm1 : PM.strm),
getr R1 (PMK.reg 1) = getr R (PMK.reg 1) -> (forall x, In x PMK.cs_all -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PMPS.with_src s0 (PM.SRC qc de1 rem1)) ->
PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str sm1 -> PMST.base_ok RSEGS AD M1 -> PMST.err_ok RSEGS AD M1 e ->
PMSP.src_step (PM.SRC qc de rem) (PM.SRC qc de1 rem1) (PM.STRM g eg st) sm1 ->
PM.unread (PM.SRC qc de1 rem1) sm1 < PM.unread (PM.SRC qc de rem) (PM.STRM g eg st) ->
PMK.ek L LB sp 22528 WS M M1 -> PMK.dk L LB sp 22528 M M1 -> L5C.stk (hl_sptop L) M1 sp 22528 -> hi_heap HI LB cr M1 (m_vmmaps model) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x37c8c M1 model) K).
{ intros fx1 R1 M1 de1 rem1 sm1 E1 E2 PA1 IA1 BASE1 ERR1 STEP1 UN1 EK1 DK1 STK1 HH1.
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx1 R1 M1 0x37c8c (ltac:(oW' 0x37c8c%Z)) r (ltac:(oF' 0x37c8c%Z)) eq_refl (ltac:(oD' 0x37c8c%Z))); [rewrite E1; exact Rra| lia| exact Hr2]. }
assert (AGH : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WS i) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB sp 22528 WS M M1 EK1 STK SC0 a n H1 H2 N). }
apply (KONT fx1 R1 M1 model (PMPS.with_src s0 (PM.SRC qc de1 rem1)) sm1 e cr).
- apply PMK.preserved_by_index. exact E2.
- unfold PMSP.run_post_d, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutU.ADDR_U].
split; [|split; [exact STEP1|split; [intros X; exact X|right]]].
+ split; [exact PA1|]. split; [exact IA1|].
split; [unfold PMSP.visitor_at in *; apply (L5C.u64_at_agree RSEGS M M1); [apply AGH; [lia|lia| apply NWS2; lia]|lia|lia| exact VIS]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGH; [lia|lia| apply NWS2; lia]|lia|lia| exact VREF]|].
split; [exact BASE1|]. split; [exact ERR1| exact TBOK].
+ split; [apply (ec_agree M M1); [apply AGH; [lia|lia| apply NWS; lia]|lia|lia| exact EC0]|].
split; [exact INV|].
unfold PMSP.prog_len. split; [reflexivity|]. split; [exact UN1|].
exists (bv_unsigned (getr R1 (PMK.reg 10))). split.
* pose proof (bv_unsigned_in_range 64 (getr R1 (PMK.reg 10))) as BB. change (bv_modulus 64) with (2 ^ 64) in BB. lia.
* rewrite L5K.rl10. symmetry. apply PMPK.word_id.
- apply (FINW M1 WS EK1 DK1 STK1 WSR).
- assert (EP : PM.pot_parser L (PMPS.with_src s0 (PM.SRC qc de1 rem1)) = PM.pot_parser L s0) by reflexivity.
rewrite EP. unfold PMSP.credit_keep. lia.
- apply L5C.model_but_vm_refl.
- exact HH1. }
assert (ERRP : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (v de1 rem1 : Z) (sm1 : PM.strm),
getr R1 (PMK.reg 1) = Z_to_bv 64 228460 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) ->
getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 11) = Z_to_bv 64 v ->
getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 40 + 24) ->
(forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) -> 1 <= v <= 64 ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) (PMPS.with_src s0 (PM.SRC qc de1 rem1)) ->
PM.iss_at RSEGS AD PMSP.T3 M1 (fb + 440) str sm1 -> PMST.base_ok RSEGS AD M1 -> PMST.err_ok RSEGS AD M1 e ->
PMSP.src_step (PM.SRC qc de rem) (PM.SRC qc de1 rem1) (PM.STRM g eg st) sm1 ->
PMK.ek L LB sp 22528 WS M M1 -> PMK.dk L LB sp 22528 M M1 -> L5C.stk (hl_sptop L) M1 sp 22528 -> hi_heap HI LB cr M1 (m_vmmaps model) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x370ac M1 model) K).
{ intros fx1 R1 M1 v de1 rem1 sm1 X1 X2 X8 X9 X10 X11 X18 KS1 Hv C8 C16 C24 C32 C40 PA1 IA1 BASE1 ERR1 STEP1 EK1 DK1 STK1 HH1.
assert (AGH1 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW WS i) -> L5C.agree_on M M1 a n).
{ intros a n H1 H2 N. apply (PMPK.ag_hi RSEGS L KL LB sp 22528 WS M M1 EK1 STK SC0 a n H1 H2 N). }
assert (EC1 : PMSP.ec_at RSEGS M1 (fb + 8) 0 cat) by (apply (ec_agree M M1); [apply AGH1; [lia|lia| apply NWS; lia]|lia|lia| exact EC0]).
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 64) 14336).
{ apply (PMK.stk_call L M1 sp 22528 (sp - 64) 14336 STK1); [lia|lia|lia|]. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.make_ec_spec, PMSP.make_ec_spec in MKE. cbn [pa_make_ec AD PmLayoutU.ADDR_U] in MKE.
apply (MKE fx1 R1 M1 model K LB cr (fb + 8) v (sp - 64) 228460 e HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
{ rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hv. } { lia. } { lia. } { exact AL1. }
{ destruct EC1 as (_ & _ & ED). exact ED. } { exact BASE1. } { exact ERR1. }
intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
change (PMSP.pm_scr 1) with 14336 in HP2.
set (WE := (fb + 8, 16) :: (if e then [] else PMSP.err_W AD)) in HP2.
assert (WCE : forall a, PMK.inW WE a -> (fb + 8 <= a < fb + 24) \/ (0xc72b0 <= a < 0xc72b2) \/ (0xe8cf8 <= a < 0xe8f18)).
{ intros a (r0 & Hin & Hr). unfold WE in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|]. destruct e; [destruct Hin|].
unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; right; [left|right]; lia. }
assert (WHIE : forall a, PMK.inW WE a -> (sp - 64) <= a \/ hl_img_lo L <= a < hl_img_hi L).
{ intros a I. apply WCE in I. rewrite (ly_img_lo L LY), (ly_img_hi L LY). destruct I as [I|[I|I]]; [left; lia| right; lia| right; lia]. }
assert (EKc : PMK.ek L LB (sp - 64) 14336 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= 14336) by lia.
assert (HI2 : forall a n, sp - 64 <= a -> a + n <= fb + 8 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 64) 14336 WE M1 M2 EKc STKc SCc a n H1); [lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I SLO STOP. lia. }
assert (HI2' : forall a n, fb + 24 <= a -> a + n <= fb + 752 -> L5C.agree_on M1 M2 a n).
{ intros a n H1 H2. apply (PMPK.ag_hi RSEGS L KL LB (sp - 64) 14336 WE M1 M2 EKc STKc SCc a n); [lia|lia|]. intros i Hi I. apply WCE in I.
clear - Hi H1 H2 I F1 F2 SLO STOP. lia. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 22528) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 22528 (sp - 64) 14336 WE STK1 HP2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp 22528 STK2) as WR2.
assert (PA2 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M2 (fb + 40) (fb + 440) (PMPS.with_src s0 (PM.SRC qc de1 rem1))).
{ apply (PMPK.parser_at_keep RSEGS AD M1 M2 (fb + 40) (fb + 440) _ PA1); cbn [s0 PMPS.with_src PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
- lia.
- lia.
- apply HI2'; lia.
- apply (PMPK.dkr_hpres_blk RSEGS L KL LB (sp - 64) 14336 WE M1 M2 qc 16384 HP2 QIN BR). lia.
- lia.
- clear - V4 STOP. unfold hl_ceil in *. lia.
- apply (PMPK.ag_blk RSEGS L KL LB (sp - 64) 14336 WE M1 M2 EKc STKc BR vb (32 * 2 ^ vk) VIN).
intros i Hi I. apply WCE in I. destruct I as [I|I]; [clear - Hi I V4 SLO F1; unfold hl_ceil in *; lia| apply (VI i Hi); clear - I; lia].
- intros c0 n0 q0 E0. apply (PMPK.dkr_hpres_blk RSEGS L KL LB (sp - 64) 14336 WE M1 M2 q0 c0 HP2); [|exact BR|lia].
unfold LB, s0, PM.parser_own, PM.vs_own. rewrite E0. cbn. right. right. left. reflexivity. }
assert (IA2 : PM.iss_at RSEGS AD PMSP.T3 M2 (fb + 440) str sm1).
{ apply (PMFR.iss_keep RSEGS AD L KL LB (sp - 64) 14336 WE M1 M2 EKc STKc SCc BR WHIE); [lia|lia| |exact SINC| exact IA1].
intros i Hi I. apply WCE in I. clear - Hi I F1 F2 SLO STOP. lia. }
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB (sp - 64) 14336 WE M1 M2 EKc); [| | | | exact BASE1].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCE in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha.
all: clear - I Ha SLO STOP F1; lia. }
assert (RP2_ : forall k, In k PMK.cs_all -> getr R2 (PMK.reg k) = getr R1 (PMK.reg k)) by (intros k Hk; apply (PMK.cs_of_preserved R1 R2 k RP2 Hk)).
cfeed P (PMUGLP.uglZ_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8
| 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
| 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1]
| (apply (L5C.u64_at_agree RSEGS M1 M2); [apply HI2; lia|lia|lia|assumption])
| (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (fb + 40) 384); [destruct PA2 as (_ & PD2 & _); exact PD2|lia|lia]|lia|lia]) ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T10 & T18 & T19 & Z8)); PMK.pvz_clrT.
rewrite PMPK.word_id in T1, T8, T9, T18, T19.
apply (gl_step LB cr fx2 fx3 R2 R3 0x37c6c 0x37c8c M2 M3 model K sp (fb + 40 + 8) 1 HH2 Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(right; unfold hl_ceil; lia) MS3 MG3 (fun i Hi _ N2 => FRZ3 i Hi N2)).
intros HH3.
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
{ apply (PMK.ret_to RSEGS fx3 R3 M3 0x37c8c (ltac:(oW' 0x37c8c%Z)) r (ltac:(oF' 0x37c8c%Z)) eq_refl (ltac:(oD' 0x37c8c%Z))); [rewrite T1; exact Rra| lia| exact Hr2]. }
assert (AG3 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 64 \/ sp <= a) -> (a + n <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M2 M3 a n).
{ intros a n H1 H2 H3 H4 i Hi. apply FRZ3; [clear - H1 H2 Hi; lia| clear - H4 Hi; lia]. }
assert (EK3 : PMK.ek L LB sp 22528 [(fb + 48, 1)] M2 M3).
{ apply (gl_ek LB sp (fb + 40 + 8) 1 [(fb + 48, 1)] M2 M3 (fun i Hi _ N2 => FRZ3 i Hi N2) STK2 BR). intros a Ha. apply PMK.inW_here. lia. }
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 22528) by (apply (PMK.stk_grows L M2 M3 sp 22528 MG3 STK2)).
apply (KONT fx3 R3 M3 model (PMPK.set_more (PMPS.with_src s0 (PM.SRC qc de1 rem1)) 0) sm1 true cr).
- apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | assumption | (rewrite (KS3 _) by PMK.inl; rewrite RP2_ by PMK.inl; apply KS1; PMK.inl) ] |]).
destruct Hk.
- unfold PMSP.run_post_d, PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD PmLayoutU.ADDR_U].
split; [|split; [exact STEP1|split; [intros _; reflexivity| left]]].
+ split.
{ apply (PMPK.parser_more_upd RSEGS AD M2 M3 (fb + 40) (fb + 440) _ 0 PA2); cbn [s0 PMPS.with_src PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
- lia.
- lia.
- apply AG3; lia.
- apply AG3; lia.
- apply PMPK.dkr_grows. exact MG3.
- exact Z8.
- left. reflexivity.
- apply PMPK.dkr_grows. exact MG3.
- lia.
- clear - V4 STOP. unfold hl_ceil in *. lia.
- apply AG3; [lia|clear - V4 STOP; unfold hl_ceil in *; lia| clear - V4 SLO; unfold hl_ceil in *; lia| clear - V4 SLO F1; unfold hl_ceil in *; lia].
- intros c0 n0 q0 _. apply PMPK.dkr_grows. exact MG3. }
split.
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 22528 [(fb + 48, 1)] M2 M3 EK3 STK2 SC0 BR); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| |exact SINC| exact IA2].
intros i Hi I. apply PMFR.inW_inv1 in I. lia. }
split.
{ unfold PMSP.visitor_at in *. apply (L5C.u64_at_agree RSEGS M M3); [|lia|lia| exact VIS].
apply (L5C.agree_on_trans M M1 M3); [apply AGH1; [lia|lia| apply NWS2; lia]|].
apply (L5C.agree_on_trans M1 M2 M3); [apply HI2'; lia| apply AG3; lia]. }
split.
{ apply (L5C.u64_at_agree RSEGS M M3); [|lia|lia| exact VREF].
apply (L5C.agree_on_trans M M1 M3); [apply AGH1; [lia|lia| apply NWS2; lia]|].
apply (L5C.agree_on_trans M1 M2 M3); [apply HI2'; lia| apply AG3; lia]. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 22528 [(fb + 48, 1)] M2 M3 EK3); [| | | | exact BASE2].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutU.ADDR_U] in Ha; clear - I Ha SLO STOP F1; lia. }
split; [|exact TBOK].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB sp 22528 [(fb + 48, 1)] M2 M3 EK3); [| | exact ERR2].
all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply PMFR.inW_inv1 in I;
cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U] in Ha; clear - I Ha SLO STOP F1; lia. }
+ exists v. split; [exact Hv|]. split; [|split; reflexivity].
apply (ec_agree M2 M3); [apply AG3; lia|lia|lia| exact EC2].
- apply (FINW M3 (WS ++ WE ++ [(fb + 48, 1)])).
+ apply (PMK.ek_trans L LB sp 22528 _ M M1 M3).
{ apply (PMK.ek_weaken L LB LB sp 22528 sp 22528 _ WS M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0. apply O. apply in_or_app. left. exact Hr0. }
apply (PMK.ek_trans L LB sp 22528 _ M1 M2 M3).
{ apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 22528 (sp - 64) 14336 _ WE M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
intros a I. right. apply PMK.inW_app_r. apply PMK.inW_app_l. exact I. }
apply (PMK.ek_weaken L LB LB sp 22528 sp 22528 _ [(fb + 48, 1)] M2 M3 EK3); [apply incl_refl| intros x Hx; exact Hx|].
intros a O r0 Hr0. apply O. apply in_or_app. right. apply in_or_app. right. exact Hr0.
+ apply (PMK.dk_trans L LB sp 22528 M M1 M3 DK1). apply (PMK.dk_trans L LB sp 22528 M1 M2 M3).
{ apply (PMK.dk_callee L LB LB sp 22528 (sp - 64) 14336 WE M1 M2 HP2 (incl_refl _)); lia. }
apply (PMK.dk_grows L LB sp 22528 M2 M3 MG3).
+ exact STK3.
+ intros a I. destruct I as (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
{ apply WSR. exists r0. split; assumption. }
apply in_app_or in Hin. left. unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U app].
destruct Hin as [Hin|[<-|[]]].
* assert (X : PMK.inW WE a) by (exists r0; split; assumption). apply WCE in X.
destruct X as [X|[X|X]]; [do 6 apply PMK.inW_next; apply PMK.inW_here; lia| do 7 apply PMK.inW_next; apply PMK.inW_here; lia| do 8 apply PMK.inW_next; apply PMK.inW_here; lia].
* unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply PMK.inW_here. lia.
- assert (EP : PM.pot_parser L (PMPK.set_more (PMPS.with_src s0 (PM.SRC qc de1 rem1)) 0) = PM.pot_parser L s0) by reflexivity.
rewrite EP. unfold PMSP.credit_keep. lia.
- apply L5C.model_but_vm_refl.
- exact HH3. }
cfeed P (PMUGLP.uglA_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1]]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
apply (gl_step LB cr fx fx1 R R1 0x37aa4 0x374b8 M M1 model K sp 0 0 HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(left; reflexivity) MS1 MG1 (fun i Hi N1 _ => FRZ1 i Hi N1)).
intros HH1.
assert (EK1f : PMK.ek L LB sp 22528 [] M M1).
{ apply (PMFR.ek_of_piece RSEGS L KL LB sp 22528 M M1 (fun a => sp - 64 <= a < sp - 64 + 64) ltac:(intros a Ha N; apply FRZ1; [exact Ha| exact N]) STK (PMFR.brange_hi L LB BR)). intros a Pa. lia. }
assert (EK1 : PMK.ek L LB sp 22528 WS M M1).
{ apply (PMK.ek_weaken L LB LB sp 22528 sp 22528 WS [] M M1 EK1f); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 22528) by (apply (PMK.stk_grows L M M1 sp 22528 MG1 STK)).
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (R1x : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)).
{ intros x Hx. apply KS1. revert x Hx. apply (PMPK.sub_in PMUGLP.KS_uglA). vm_compute. reflexivity. }
apply (RD fx1 R1 M1 de rem (PM.STRM g eg st) (sp - 41) 1 228056 X1 ltac:(split; [lia| reflexivity]) X2 X10 X11 X12
ltac:(apply R1x; PMK.inl) ltac:(apply R1x; PMK.inl) ltac:(lia) ltac:(lia) ltac:(lia)).
{ apply (PMFR.parser_keep RSEGS AD L KL LB sp 22528 [] M M1 EK1f STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact PINC| exact PA]. }
{ apply (PMFR.iss_keep RSEGS AD L KL LB sp 22528 [] M M1 EK1f STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]. }
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 22528 [] M M1 EK1f); first [exact BASE | intros a _; apply L5C.outside_nil]. }
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LB sp 22528 [] M M1 EK1f); first [exact ERR | intros a _; apply L5C.outside_nil]. }
{ unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros E; exact E| lia]. }
{ exact C8. } { exact C16. } { exact C24. } { exact C32. } { exact C40. }
{ exact EK1. } { apply (PMK.dk_grows L LB sp 22528 M M1 MG1). } { exact STK1. } { exact HH1. }
intros fx2 R2 M2 de2 rem2 d sm2 RP2 Y10 Hd UN2 PA2 IA2 BASE2 ERR2 STEP2 D8 D16 D24 D32 D40 EK2 DK2 STK2 HH2. unfold PMSP.cfg.
pose proof STK2 as (_ & _ & _ & _ & SD2). pose proof (L5C.stk_writable RSEGS _ M2 sp 22528 STK2) as WR2.
assert (R2x : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg x) = getr R (PMK.reg x)).
{ intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply (PMPK.sub_in PMK.cs_all); vm_compute; reflexivity). apply R1x. exact Hx. }
assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 (fb + 8)) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; exact X9).
assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 (fb + 40 + 24)) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; exact X18).
clear X1 X2 X8 X9 X10 X11 X12 X18 KS1 R1x RP2.
destruct (Z.eq_dec d 0) as [Dz|Dnz].
-
subst d.
cfeed P (PMUGLP.uglE0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3 & T1 & T10 & T11).
assert (M3 = M2) as -> by (apply functional_extensionality; exact FR3).
apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 0x37ad8 R3 0x370ac M2 K Mh Ml MS3).
apply (ERRP fx3 R3 M2 1 de2 rem2 sm2 T1); try gl_disp.
-
assert (d = 1) as -> by lia. clear Dnz.
cfeed P (PMUGLP.uglB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3).
assert (M3 = M2) as -> by (apply functional_extensionality; exact FR3).
apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 0x37ad8 R3 0x37adc M2 K Mh Ml MS3).
destruct (PMPX.lbu_run RSEGS fx3 R3 M2 0x37adc (ltac:(oW' 0x37adc%Z)) 10%bv 2%bv 23%bv (sp - 64) (ltac:(oF' 0x37adc%Z)) eq_refl (ltac:(oD' 0x37adc%Z))) as (b & Hb & U8 & MSb).
{ intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. }
{ lia. } { lia. } { rewrite L5K.rl2. rewrite (KS3 2%nat) by PMK.inl. exact R2_2. } { lia. }
{ change (bv_signed (23%bv : bv 12)) with 23. lia. } { change (bv_signed (23%bv : bv 12)) with 23. apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]. }
change (0x37adc + 4) with 0x37ae0 in MSb. rewrite L5K.rl10 in MSb.
apply (PMK.spiece_ro RSEGS model fx3 fx3 R3 0x37adc _ 0x37ae0 M2 K Mh Ml MSb).
set (R4 := regupd R3 (PMK.reg 10) (Z_to_bv 64 b)).
assert (O4 : forall k, k <> 10%nat -> (k < 32)%nat -> getr R4 (PMK.reg k) = getr R3 (PMK.reg k)) by (intros k N Hk; apply PMPX.regupd_other_idx; lia).
assert (R4_10 : getr R4 (PMK.reg 10) = Z_to_bv 64 b) by (apply PMPX.regupd_same_idx; lia).
assert (R4_2 : getr R4 (PMK.reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite O4 by lia; rewrite (KS3 2%nat) by PMK.inl; exact R2_2).
assert (R4_8 : getr R4 (PMK.reg 8) = Z_to_bv 64 (fb + 40)) by (rewrite O4 by lia; rewrite (KS3 8%nat) by PMK.inl; exact R2_8).
assert (R4_9 : getr R4 (PMK.reg 9) = Z_to_bv 64 (fb + 8)) by (rewrite O4 by lia; rewrite (KS3 9%nat) by PMK.inl; exact R2_9).
assert (R4_18 : getr R4 (PMK.reg 18) = Z_to_bv 64 (fb + 40 + 24)) by (rewrite O4 by lia; rewrite (KS3 18%nat) by PMK.inl; exact R2_18).
assert (R4x : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (PMK.reg x) = getr R (PMK.reg x)).
{ intros x Hx. rewrite O4 by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [lia|]); destruct Hx).
rewrite (KS3 x) by (revert x Hx; apply (PMPK.sub_in PMUGLP.KS_uglB); vm_compute; reflexivity). apply R2x. exact Hx. }
clearbody R4. clear O4 KS3 R2_2 R2_8 R2_9 R2_18 R2x.
assert (DFLT : b <> 105 -> b <> 85 -> b <> 73 -> b <> 108 -> b <> 76 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R4 0x37ae0 M2 model) K).
{ intros N1 N2 N3 N4 N5.
assert (CASES : (0 <= b <= 72) \/ (74 <= b <= 75) \/ (77 <= b <= 84) \/ (86 <= b <= 104) \/ (106 <= b <= 107) \/ (109 <= b <= 255)) by lia.
destruct CASES as [Bc|[Bc|[Bc|[Bc|[Bc|Bc]]]]].
- cfeed P (PMUGLP.uglTd1_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => b | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & T1 & T10 & T11).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x370ac M2 K Mh Ml MS5).
apply (ERRP fx5 R5 M2 5 de2 rem2 sm2 T1); try gl_disp.
- cfeed P (PMUGLP.uglTd2_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => b | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & T1 & T10 & T11).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x370ac M2 K Mh Ml MS5).
apply (ERRP fx5 R5 M2 5 de2 rem2 sm2 T1); try gl_disp.
- cfeed P (PMUGLP.uglTd3_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => b | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & T1 & T10 & T11).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x370ac M2 K Mh Ml MS5).
apply (ERRP fx5 R5 M2 5 de2 rem2 sm2 T1); try gl_disp.
- cfeed P (PMUGLP.uglTd4_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => b | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & T1 & T10 & T11).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x370ac M2 K Mh Ml MS5).
apply (ERRP fx5 R5 M2 5 de2 rem2 sm2 T1); try gl_disp.
- cfeed P (PMUGLP.uglTd5_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => b | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & T1 & T10 & T11).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x370ac M2 K Mh Ml MS5).
apply (ERRP fx5 R5 M2 5 de2 rem2 sm2 T1); try gl_disp.
- cfeed P (PMUGLP.uglTd6_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => b | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & T1 & T10 & T11).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x370ac M2 K Mh Ml MS5).
apply (ERRP fx5 R5 M2 5 de2 rem2 sm2 T1); try gl_disp.
}
destruct (Z.eq_dec b 105) as [Bt0|Bt0].
{
subst b.
cfeed P (PMUGLP.uglTi_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z19).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x374b8 M2 K Mh Ml MS5).
apply (RD fx5 R5 M2 de2 rem2 sm2 (sp - 56) 1 228116 Z1 ltac:(split; [lia| reflexivity])); try gl_disp.
intros fx6 R6 M6 de6 rem6 d6 sm6 RP6 Y6 Hd6 UN6 PA6 IA6 BASE6 ERR6 STEP6 E8 E16 E24 E32 E40 EK6 DK6 STK6 HH6. unfold PMSP.cfg.
pose proof STK6 as (_ & _ & _ & _ & SD6). pose proof (L5C.stk_writable RSEGS _ M6 sp 22528 STK6) as WR6.
destruct (Z.eq_dec d6 1) as [Dw|Dw].
2:{
cfeed P (PMUGLP.uglNi_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => d6 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (rewrite Y6; f_equal; lia) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7 & W1 & W10 & W11).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37b14 R7 0x370ac M6 K Mh Ml MS7).
apply (ERRP fx7 R7 M6 1 de6 rem6 sm6 W1); try gl_disp.
}
subst d6.
cfeed P (PMUGLP.uglVi_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37b14 R7 0x37b1c M6 K Mh Ml MS7).
pose proof (bv_unsigned_in_range 64 (getr R7 (PMK.reg 10))) as B7. change (bv_modulus 64) with (2 ^ 64) in B7.
cfeed P (PMUGLP.uglSi_conc fx7 R7 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx8 & R8 & M8 & MG8 & FR8 & _ & EX8).
assert (M8 = M6) as -> by (apply functional_extensionality; exact FR8).
destruct EX8 as [(MS8 & KS8 & W1 & W2 & W8 & W9 & W18 & W19)|(MS8 & KS8 & W1 & W10 & W11 & W19)].
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37b1c R8 0x37c8c M6 K Mh Ml MS8).
rewrite PMPK.word_id in W1, W8, W9, W18, W19.
apply (OKP fx8 R8 M6 de6 rem6 sm6 W1); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite W2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
+ unfold PM.unread in UN2, UN6 |- *. lia.
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37b1c R8 0x370ac M6 K Mh Ml MS8).
apply (ERRP fx8 R8 M6 4 de6 rem6 sm6 W1); try gl_disp.
}
destruct (Z.eq_dec b 85) as [Bt1|Bt1].
{
subst b.
cfeed P (PMUGLP.uglTU_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & Z1 & Z10 & Z11 & Z12).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x374b8 M2 K Mh Ml MS5).
apply (RD fx5 R5 M2 de2 rem2 sm2 (sp - 56) 1 228304 Z1 ltac:(split; [lia| reflexivity])); try gl_disp.
intros fx6 R6 M6 de6 rem6 d6 sm6 RP6 Y6 Hd6 UN6 PA6 IA6 BASE6 ERR6 STEP6 E8 E16 E24 E32 E40 EK6 DK6 STK6 HH6. unfold PMSP.cfg.
pose proof STK6 as (_ & _ & _ & _ & SD6). pose proof (L5C.stk_writable RSEGS _ M6 sp 22528 STK6) as WR6.
destruct (Z.eq_dec d6 1) as [Dw|Dw].
2:{
cfeed P (PMUGLP.uglNU_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => d6 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (rewrite Y6; f_equal; lia) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7 & W1 & W10 & W11).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37bd0 R7 0x370ac M6 K Mh Ml MS7).
apply (ERRP fx7 R7 M6 1 de6 rem6 sm6 W1); try gl_disp.
}
subst d6.
cfeed P (PMUGLP.uglVU_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7 & W1 & W2 & W8 & W9 & W18 & W19).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37bd0 R7 0x37c8c M6 K Mh Ml MS7).
rewrite PMPK.word_id in W1, W8, W9, W18, W19.
apply (OKP fx7 R7 M6 de6 rem6 sm6 W1); try assumption.
- intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite W2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
- unfold PM.unread in UN2, UN6 |- *. lia. }
destruct (Z.eq_dec b 73) as [Bt2|Bt2].
{
subst b.
cfeed P (PMUGLP.uglTI_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z19).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x374b8 M2 K Mh Ml MS5).
apply (RD fx5 R5 M2 de2 rem2 sm2 (sp - 56) 2 228416 Z1 ltac:(split; [lia| reflexivity])); try gl_disp.
intros fx6 R6 M6 de6 rem6 d6 sm6 RP6 Y6 Hd6 UN6 PA6 IA6 BASE6 ERR6 STEP6 E8 E16 E24 E32 E40 EK6 DK6 STK6 HH6. unfold PMSP.cfg.
pose proof STK6 as (_ & _ & _ & _ & SD6). pose proof (L5C.stk_writable RSEGS _ M6 sp 22528 STK6) as WR6.
destruct (Z.eq_dec d6 2) as [Dw|Dw].
2:{
cfeed P (PMUGLP.uglNI_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => d6 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (rewrite Y6; f_equal; lia) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7 & W1 & W10 & W11).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37c40 R7 0x370ac M6 K Mh Ml MS7).
apply (ERRP fx7 R7 M6 1 de6 rem6 sm6 W1); try gl_disp.
}
subst d6.
cfeed P (PMUGLP.uglVI_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37c40 R7 0x37c54 M6 K Mh Ml MS7).
pose proof (bv_unsigned_in_range 64 (getr R7 (PMK.reg 10))) as B7. change (bv_modulus 64) with (2 ^ 64) in B7.
cfeed P (PMUGLP.uglSI_conc fx7 R7 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx8 & R8 & M8 & MG8 & FR8 & _ & EX8).
assert (M8 = M6) as -> by (apply functional_extensionality; exact FR8).
destruct EX8 as [(MS8 & KS8 & W1 & W2 & W8 & W9 & W18 & W19)|(MS8 & KS8 & W1 & W10 & W11)].
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37c54 R8 0x37c8c M6 K Mh Ml MS8).
rewrite PMPK.word_id in W1, W8, W9, W18, W19.
apply (OKP fx8 R8 M6 de6 rem6 sm6 W1); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite W2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
+ unfold PM.unread in UN2, UN6 |- *. lia.
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37c54 R8 0x370ac M6 K Mh Ml MS8).
apply (ERRP fx8 R8 M6 4 de6 rem6 sm6 W1); try gl_disp.
}
destruct (Z.eq_dec b 108) as [Bt3|Bt3].
{
subst b.
cfeed P (PMUGLP.uglTl_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z19).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x374b8 M2 K Mh Ml MS5).
apply (RD fx5 R5 M2 de2 rem2 sm2 (sp - 56) 4 228336 Z1 ltac:(split; [lia| reflexivity])); try gl_disp.
intros fx6 R6 M6 de6 rem6 d6 sm6 RP6 Y6 Hd6 UN6 PA6 IA6 BASE6 ERR6 STEP6 E8 E16 E24 E32 E40 EK6 DK6 STK6 HH6. unfold PMSP.cfg.
pose proof STK6 as (_ & _ & _ & _ & SD6). pose proof (L5C.stk_writable RSEGS _ M6 sp 22528 STK6) as WR6.
destruct (Z.eq_dec d6 4) as [Dw|Dw].
2:{
cfeed P (PMUGLP.uglNl_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => d6 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (rewrite Y6; f_equal; lia) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7 & W1 & W10 & W11 & _).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37bf0 R7 0x370ac M6 K Mh Ml MS7).
apply (ERRP fx7 R7 M6 1 de6 rem6 sm6 W1); try gl_disp.
}
subst d6.
cfeed P (PMUGLP.uglVl_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37bf0 R7 0x37c24 M6 K Mh Ml MS7).
pose proof (bv_unsigned_in_range 64 (getr R7 (PMK.reg 10))) as B7. change (bv_modulus 64) with (2 ^ 64) in B7.
cfeed P (PMUGLP.uglSl_conc fx7 R7 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx8 & R8 & M8 & MG8 & FR8 & _ & EX8).
assert (M8 = M6) as -> by (apply functional_extensionality; exact FR8).
destruct EX8 as [(MS8 & KS8 & W1 & W2 & W8 & W9 & W18 & W19)|(MS8 & KS8 & W1 & W10 & W11)].
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37c24 R8 0x37c8c M6 K Mh Ml MS8).
rewrite PMPK.word_id in W1, W8, W9, W18, W19.
apply (OKP fx8 R8 M6 de6 rem6 sm6 W1); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite W2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
+ unfold PM.unread in UN2, UN6 |- *. lia.
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37c24 R8 0x370ac M6 K Mh Ml MS8).
apply (ERRP fx8 R8 M6 4 de6 rem6 sm6 W1); try gl_disp.
}
destruct (Z.eq_dec b 76) as [Bt4|Bt4].
{
subst b.
cfeed P (PMUGLP.uglTL_conc fx3 R4 M2 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & KS5 & Z1 & Z10 & Z11 & Z12 & Z19).
assert (M5 = M2) as -> by (apply functional_extensionality; exact FR5).
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x37ae0 R5 0x374b8 M2 K Mh Ml MS5).
apply (RD fx5 R5 M2 de2 rem2 sm2 (sp - 56) 8 228172 Z1 ltac:(split; [lia| reflexivity])); try gl_disp.
intros fx6 R6 M6 de6 rem6 d6 sm6 RP6 Y6 Hd6 UN6 PA6 IA6 BASE6 ERR6 STEP6 E8 E16 E24 E32 E40 EK6 DK6 STK6 HH6. unfold PMSP.cfg.
pose proof STK6 as (_ & _ & _ & _ & SD6). pose proof (L5C.stk_writable RSEGS _ M6 sp 22528 STK6) as WR6.
destruct (Z.eq_dec d6 8) as [Dw|Dw].
2:{
cfeed P (PMUGLP.uglNL_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => d6 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (rewrite Y6; f_equal; lia) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7 & W1 & W10 & W11).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37b4c R7 0x370ac M6 K Mh Ml MS7).
apply (ERRP fx7 R7 M6 1 de6 rem6 sm6 W1); try gl_disp.
}
subst d6.
cfeed P (PMUGLP.uglVL_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx7 & R7 & M7 & MG7 & FR7 & _ & MS7 & KS7).
assert (M7 = M6) as -> by (apply functional_extensionality; exact FR7).
apply (PMK.spiece_ro RSEGS model fx6 fx7 R6 0x37b4c R7 0x37bb8 M6 K Mh Ml MS7).
pose proof (bv_unsigned_in_range 64 (getr R7 (PMK.reg 10))) as B7. change (bv_modulus 64) with (2 ^ 64) in B7.
cfeed P (PMUGLP.uglSL_conc fx7 R7 M6 (fun j => match j with 2%nat => sp | 36%nat => fb + 40 | 37%nat => fb + 8 | 33%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9)) | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | 44%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | (symmetry; apply PMPK.word_id) | unfold PMUGLP.aligned; first [exact A16 | exact AL5 | exact AL1] | (apply (L5.defined_sub M2 (sp - 22528) 22528); [exact SD2|lia|lia]) | (apply (L5.defined_sub M6 (sp - 22528) 22528); [exact SD6|lia|lia])]).
destruct P as (fx8 & R8 & M8 & MG8 & FR8 & _ & EX8).
assert (M8 = M6) as -> by (apply functional_extensionality; exact FR8).
destruct EX8 as [(MS8 & KS8 & W1 & W2 & W8 & W9 & W18 & W19)|(MS8 & KS8 & W1 & W10 & W11)].
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37bb8 R8 0x37c8c M6 K Mh Ml MS8).
rewrite PMPK.word_id in W1, W8, W9, W18, W19.
apply (OKP fx8 R8 M6 de6 rem6 sm6 W1); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [first [ rewrite W2; symmetry; exact Rsp | PMK.rk ] |]). destruct Hx.
+ unfold PM.unread in UN2, UN6 |- *. lia.
- apply (PMK.spiece_ro RSEGS model fx7 fx8 R7 0x37bb8 R8 0x370ac M6 K Mh Ml MS8).
apply (ERRP fx8 R8 M6 4 de6 rem6 sm6 W1); try gl_disp.
}
apply DFLT; assumption.
Qed.
End WithHeap.
End PMUGL.
