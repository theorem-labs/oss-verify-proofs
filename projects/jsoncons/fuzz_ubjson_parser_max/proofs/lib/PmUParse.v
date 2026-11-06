(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith Zwf List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmParSpecs PmParSpecsU PmParKit PmParKit2 PmParStep
PmCertKitG PmUParseP PmUParseD PmUParseK PmUParse1 PmUParse2 PmUParse3 PmUParse4 PmUParse5 Ju0_code_3692c_36930.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUParse () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1None"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"; "0LB"]; ["4Model"; "4m_halted"; "4m_vm_lazy"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M1"; "0R"; "0R1"; "6msteps"; "7credit"; "7hi_heap"; "7hl_sptop"; "8agree_on"; "9SCFG"]; [":p_src"; ":p_stk"; ":pst"; ":stack_shape"; ":strm"; ":unread"; ";lp_mu"; "<ignore_spec"; "<peek_spec"; "=cfg"; "=ec_at"; ">end_array_spec"; ">end_object_spec"; ">make_ec_spec"; ">parse_spec"; ">read_key_spec"]; [">read_value_spec"; ">rtv_spec"; "?FPState"; "?mkst"; "?seg_rom"; "@TSet"; "Asrealizes"; "Bmem_grows"; "Cloaded_segments"; "0SCFG_P"; "DIn"; "Eadd"; "Ele"; "Elt"; "Epow"; "Esub"]; ["0bm"; "0c"; "0cr"; "0fx"; "0fx1"; "0i"; "0m"; "0model"; "0n"; "0o"; "0pc"; "0pc1"; "0s"; "0sm"; "0sp"; "FZ_to_bv"]; ["Fbv"; "0v"; "0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia.
Module PMULP.
Import PMU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Lemma ec_agree : ltac2:(TCodec.tc2 tcn__PmUParse "Q9'R@yR0%211'4y8%511%311p051';&Nr5r4r3+@%544321&QLz%2216&QK%1296&QN+2+R0%3221%9251&Q:&QHr8r6%45321CBr7%655413Ep031p091p0A1p0E1pT4L1pU4M1pTDN1pQ>Q01pQ<Q11").
Proof. intros M M' o v c.
intros AG H1 H2 (E0 & E8 & ED). split; [|split].
- apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
- apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
- apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmUParse "Q4'R@yR0%211'4y8%511%311p051';'7&QLzr1%3221&QM&QN+2+R0%3221%5271%;271'8r3&R?r2%22H1%411r4%113%83G31p0:1pT<G1%;3I8:p021pQ@K1pQ<L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F.
pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B.
Qed.
Lemma tstep : ltac2:(TCodec.tc2 tcn__PmUParse "UL'2'6';%2211%411&K'QB&Dy5'R@yR0%211%5241'4y8%611%311p061'@&QE&Lv<rCrBr;&Cr9%211%8576541'8%A1C&Ar:%211(1%11H%73631%Q42JJ%Q611&B%11@(3%115%>3531&QL+SoonPPPPP0&Mv>%211%5241&QO+XPPP0%2241+T0%42N1%;231r<%=219':z%O3QJQ41'7%B2:6&QK%128Q8%E21A%5241%9271%Q73R2Q49&QJ(5r8%24R6R6Q>1rJ%53R721%O2QAQC%=2QDQ<%>2QC6%Q2221%B241%C261%G2=1'J&QH&QCrIrG&R?rE%22R?1&QD%118%85763R61rHrFrD%92RF1%=5431R:6%@3?61&QG%125R>r1%QJ2Q;1&QM&QN+2+R0%3221%5271%Q@271&9%QM2RIQJr2%R5221%QC23QM%<231%QG231%711r3%R;2S11%QI2S2S1%B231%QM231%=11r4%RA2S61rA%R02S81%I241%R4241%D11r5%Q=2SJ1%Q@11%QM12%S:3SG21p061p0>1p0E1p0N1pT<T:1rNrM%SF1Q@%SL5SK32QH1'QF&OvQI%211&Q9rL%26R41R>QJQIQO%74R541QIp091rK%66R8=1R6R5R3%;4R981QMp041p0B1p0QK1p0QN1p0R@1p0RO1p0S:1p0S=1p0SD1p0SK1p0T31p0T<1pT2U71p2U81pT>U91pU8U:1pTBU;1pU6U<1pTNU=1pLTM1pT@TO1pQ@U11pQ<U21pTHUB1pTFUC1pQDU:1pQBU;1pT:UB1pT8UC1pT6UE1pQ0UG1").
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
Lemma lp_mu_nonneg : ltac2:(TCodec.tc2 tcn__PmUParse "G'Q2'Q4&Q3&Q1r2%211%411&QLz&Q5&Q0r3%211%4219%7261&Q6r4%2216%;2:1p051p0>1pTLD1pTJF1").
Proof. intros s sm. intros SH U. pose proof (PMPK2.lp_X_bound _ SH). unfold PMPK2.lp_mu. nia. Qed.
Theorem parse_ok : ltac2:(TCodec.tc2 tcn__PmUParse "M&QAvQIv>v<%43321&Q@%13543&Q?%13765&Q;%13987&Q<%13;:9&Q8%13=<;&Q7%13?>=&Q=%13A@?&Q>%13CBAp031p061p091p0<1p0?1p0B1p0E1p0H1").
Proof.
intros RTV RV RK EA EO PK IG MKE.
pose proof (PMULP1.parse_iter1 L HI LY HIok RTV RV) as I1. pose proof (PMULP2.parse_iter2 L HI LY HIok RTV RV EA) as I2.
pose proof (PMULP3.parse_iter3 L HI LY HIok RK EO) as I3. pose proof (PMULP4.parse_iter4 L HI LY HIok PK IG RTV EA MKE) as I4.
pose proof (PMULP5.parse_iter5 L HI LY HIok PK IG RK EO MKE) as I5.
unfold PMU.parse_spec, PMSP.parse_spec.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 UNR CRED KONT.
assert (CTX : PMULPD.pctx L HI K R M model LBX cr sp r fb cat s str sm e).
{ split; [exact HH|]. split; [exact MOK|]. split; [exact K0|]. split; [exact ENT|]. split; [exact FOK|]. split; [exact ARGS|].
split; [exact RPRE|]. split; [exact INCS|]. split; [exact INV|]. split; [exact EC0|]. split; [exact UNR|]. split; [exact CRED| exact KONT]. }
assert (LOOP : forall n, 0 <= n -> forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit),
PMULPD.linv L HI R M model LBX cr sp fb cat s str sm e R1 M1 model1 s1 sm1 e1 cr1 -> PMPK2.lp_mu s1 sm1 = n ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x365ec M1 model1) K).
{ intros n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
intros n IHn Hn fx1 R1 M1 model1 s1 sm1 e1 cr1 LI EM.
assert (IH : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (s2 : PM.pst) (sm2 : PM.strm) (e2 : bool) (cr2 : credit),
PMULPD.linv L HI R M model LBX cr sp fb cat s str sm e R2 M2 model2 s2 sm2 e2 cr2 -> PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu s1 sm1 ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x365ec M2 model2) K).
{ intros fx2 R2 M2 model2 s2 sm2 e2 cr2 LI2 LT2.
pose proof LI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INV2 & RPRE2 & _).
pose proof INV2 as (_ & _ & _ & SH2 & _).
destruct (PMULPK.RUNF2 M2 fb s2 str sm2 e2 RPRE2) as (_ & _ & _ & _ & _ & _ & UN2).
pose proof (lp_mu_nonneg s2 sm2 SH2 UN2) as N2.
exact (IHn (PMPK2.lp_mu s2 sm2) ltac:(unfold Zwf; lia) N2 fx2 R2 M2 model2 s2 sm2 e2 cr2 LI2 eq_refl). }
pose proof LI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INV1 & _).
pose proof INV1 as (_ & _ & _ & SH1 & _).
assert (MR : 0 <= PMULPD.top_mode s1 <= 10).
{ unfold PMULPD.top_mode. pose proof SH1 as (L1 & _).
destruct (exists_last (l := PM.p_stk s1) ltac:(intros X; rewrite X in L1; cbn in L1; lia)) as (pre & top & Ep).
rewrite Ep in SH1 |- *. rewrite last_last. destruct (PMPK2.top_of_shape pre top SH1) as (OK & _).
pose proof OK as (_ & [(Hm & _)|[(Hm & _)|(Hm & _)]]); unfold PM.mode_counted, PM.mode_indef, PM.mode_bottom in Hm; lia. }
destruct (PMULPD.lp_split _ MR) as [G|[G|[G|G]]].
- exact (I1 K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI G IH).
- exact (I2 K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI G IH).
- exact (I3 K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI G IH).
- destruct G as [G|G].
+ exact (I4 K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI G IH).
+ exact (I5 K R M model LBX cr sp r fb cat s str sm e CTX fx1 R1 M1 model1 s1 sm1 e1 cr1 LI G IH). }
pose proof CTX as (_ & _ & _ & ENT' & FOK' & _).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD PmLayoutU.ADDR_U] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
rewrite L5K.rl2 in Rsp. change (PMSP.pm_scr 10) with 32768 in *.
destruct ARGS as (A10 & A11 & A12). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
unfold PMSP.o_p, PMSP.o_v, PMSP.o_ec in A10, A11, A12. cbn [pa_off_p pa_off_v pa_off_ec AD PmLayoutU.ADDR_U] in A10, A11, A12.
pose proof (L5C.stk_writable RSEGS _ M sp 32768 STK) as WR.
destruct (PMULPK.RUNF2 M fb s str sm e RPRE) as (VIS0 & P160 & PD0 & IMG0 & PA0 & IA0 & UN0).
pose proof PA0 as (_ & _ & _ & P80 & P90 & _). pose proof INV as (IM0 & ID0 & _ & SH0 & _). rewrite ID0 in P90.
assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
unfold PMSP.cfg. cbn [pa_parse AD PmLayoutU.ADDR_U].
cfeed P (PMULPP.luE_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => (fb + 40) | 37%nat => (fb + 432) | 38%nat => (fb + 8) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMULPP.aligned; first [exact A16 | exact AL5 | exact AL1 | exact AL54 | exact AL36] | unfold PMULPP.aligned; exact A16]).
PMK.pvz_hg ltac:(idtac; destruct P as (fxa & Ra & Ma & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGa & _ & FRZa & MSa & KSa & Xa_2 & Xa_8 & Xa_9 & Xa_10 & Xa_11 & Xa_12 & Xa_18 & Xa_19 & Xa_20 & Xa_21 & Xa_22 & Xa_23 & Xa_24 & Xa_25 & Xa_26 & Xa_27 & Ca_104 & Ca_96 & Ca_88 & Ca_80 & Ca_72 & Ca_64 & Ca_56 & Ca_48 & Ca_40 & Ca_32 & Ca_24 & Ca_16 & Ca_8)); PMK.pvz_clrT.
apply (tstep (PM.parser_own s ++ LBX) cr fx fxa R Ra 0x36574 0x365ec M Ma model K sp 0 0 0 0 0 0 HH Mh Ml ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)
ltac:(left; reflexivity) ltac:(left; reflexivity) MSa MGa (fun i Hi N1 _ _ => FRZa i Hi N1)).
intros HHa.
assert (EKaf : PMK.ek L (PM.parser_own s ++ LBX) sp 32768 [] M Ma).
{ apply (PMFR.ek_of_piece RSEGS L KL (PM.parser_own s ++ LBX) sp 32768 M Ma (fun a => sp - 128 <= a < sp - 128 + 128) ltac:(intros a Ha N; apply FRZa; [exact Ha| exact N]) STK
(PMFR.brange_hi L _ (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH (incl_refl _)))). intros a Pa. lia. }
assert (STKa : L5C.stk (hl_sptop L) Ma sp 32768) by (apply (PMK.stk_grows L M Ma sp 32768 MGa STK)).
assert (AGa : forall a n, sp <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M Ma a n) by (intros a n H1 H2 i Hi; apply FRZa; lia).
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (BR0 : PMFR.brange L (PM.parser_own s ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH); apply incl_refl).
apply (LOOP (PMPK2.lp_mu s sm) (lp_mu_nonneg s sm SH0 UN0) fxa Ra Ma model s sm e cr); [|reflexivity].
unfold PMULPD.linv. do 14 (split; [PMK.rk|]). split; [PMK.rk|]. split; [PMK.rk|]. split; [exact INV|].
destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutU.ADDR_U] in PA, IA, VIS, VREF.
split.
{ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PmLayoutU.ADDR_U].
split; [apply (PMFR.parser_keep RSEGS AD L KL _ sp 32768 [] M Ma EKaf STK ltac:(lia) BR0 WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| apply incl_appl; apply incl_refl| exact PA]|].
split; [apply (PMFR.iss_keep RSEGS AD L KL _ sp 32768 [] M Ma EKaf STK ltac:(lia) BR0 WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| apply incl_appr; exact INCS| exact IA]|].
split; [apply (L5C.u64_at_agree RSEGS M Ma); [apply AGa; lia|lia|lia| exact VIS]|].
split; [apply (L5C.u64_at_agree RSEGS M Ma); [apply AGa; lia|lia|lia| exact VREF]|].
split; [apply (PMKP.base_ok_keep RSEGS AD L KL SF _ sp 32768 [] M Ma EKaf); first [exact BASE | intros a _; apply L5C.outside_nil]|].
split; [apply (PMKP.err_ok_keep RSEGS AD L KL SF _ sp 32768 [] M Ma EKaf); first [exact ERR | intros a _; apply L5C.outside_nil]| exact TBOK]. }
split; [unfold PMSP.o_ec in EC0; cbn [pa_off_ec AD PmLayoutU.ADDR_U] in EC0; apply (PMULPK.ec_agree_gen M Ma); [apply AGa; lia|lia|lia| exact EC0]|].
split; [unfold PMSP.src_step, PM.unread; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros E; exact E| lia]|].
split; [intros X; exact X|].
split.
{ apply (PMK.hpres_of L LBX sp 32768 _ M Ma).
- apply (PMK.ek_weaken L LBX (PM.parser_own s ++ LBX) sp 32768 sp 32768 _ [] M Ma EKaf); [apply incl_appr; apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
- destruct STKa as (_ & _ & _ & _ & D1). exact D1.
- apply (PMK.dk_grows L LBX sp 32768 M Ma MGa). }
split; [unfold PMSP.credit_keep; split; lia|]. split; [apply L5C.model_but_vm_refl|]. split; [exact HHa|].
unfold PMULPD.lslots. repeat split; assumption.
Qed.
End WithHeap.
End PMULP.
