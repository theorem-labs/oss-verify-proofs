(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmTxtKit2 PmASrcKit PmAReset1 PmARsKit PmARdSpanP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARdSpan1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARdSpan1.PMARSP1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepA.PMKA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepAR.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw'"; "0B"; "0BX"; "1app"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0FF"]; ["0H"; "0K"; "0L"; "0LBX"; "0LK"; "0LK'"; "4Model"; "5bvmap"; "0M"; "0M'"; "0MV"; "0R"; "0R'"; "6mrestrict"; "7credit"; "7regs_preserved"]; ["8aclient"; "8ahid"; "8ar_stack_top"; "8fframe"; ":defined"; ":img_clear"; ":in_rng"; ":outside"; ":ra_ok"; ":range"; ":u32_at"; ":u64_at"; ":writable"; "9SCFG"; ";avis"; "<zeros_at"]; ["=U"; "=W0"; "=fields_eq"; "=kept_rs"; "=memrel"; "=ois"; "=op"; "=os"; "=saves9"; "=st_ok"; "=tb"; ">p_b"; ">p_depth"; ">p_done"; ">p_k"; ">p_more"]; [">p_src"; ">p_stk"; ">p_tb"; ">parser_own"; ">pst"; ">pstate"; ">strm"; ">unread"; ">vs_size"; "?accA"; "?aobjA"; "?cfg"; "?consumed"; "?src_step"; "@wapp"; "AFPState"]; ["Agetr"; "Bsrealizes"; "Cahpres"; "Dek"; "Eloaded_segments"; "0S"; "0SCFG_P"; "FIn"; "Gadd"; "Gdiv"; "Gle"; "Glt"; "Gmodulo"; "Gof_nat"; "Gpow"; "Gsub"]; ["0W'"; "0X"; "0a"; "0ar"; "0cr"; "0cr'"; "0d"; "0fb"; "0fx"; "0fx'"; "0k"; "0len"; "0m"; "0model"; "0model'"; "0n"]; ["0ptr"; "0r0"; "0rs"; "0s"; "0s'"; "0s0"; "0scr'"; "0sm"; "0sm'"; "0sm0"; "HZ_to_bv"; "Hbv"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMARSP1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := (fun L ar (s : PM.pst) => PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s) (PM.p_tg s))).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 6 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis SA32 : S mod 32 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 24576) 3072.
Hypothesis FBS : PMA.fill_buffer_spec L ar HI.
Hypothesis SRDS : PMA.srd_read_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (PMSPA.o_tb AD fb + 1 <= ptr /\ ptr + n <= PMSPA.o_tb AD fb + 24)) ->
L5.defined M' ptr n -> PMSPA.accA M' ptr n ->
PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Definition op : Z := PMSPA.o_p AD fb.
Definition os : Z := PMSPA.o_src AD fb.
Definition ois : Z := PMSPA.o_is AD fb.
Definition tb : Z := PMSPA.o_tb AD fb.
Definition W0 : list L5.range := PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)].
Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).
Definition saves9 (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
/\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
/\ L5.u64_at RSEGS M (S - 72) (U 23).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
L5SAR.ek L ar LBX FF S 24576 W0 M0 M /\ L5SAR.dk L ar LBX FF S 24576 M0 M /\ L5CA.astk ar M S 24576.
Definition fields_eq (s : PM.pst) : Prop :=
PM.p_more s = PM.p_more s0 /\ PM.p_done s = PM.p_done s0 /\ PM.p_depth s = PM.p_depth s0 /\ PM.p_b s = PM.p_b s0 /\ PM.p_k s = PM.p_k s0 /\ PM.p_stk s = PM.p_stk s0.
Definition st_ok (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
memrel M /\ saves9 M /\ PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
/\ PMSTA.base_okA RSEGS AD M /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
/\ ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
/\ incl LK LK0 /\ incl Aw0 Aw
/\ PMSPA.credit_le (pot L ar s) cr /\ PMSPA.credit_keep cr0 cr (pot L ar s0) (pot L ar s).
Definition bregs (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 80) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 tb
/\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 19) = Z_to_bv 64 (os + 288) /\ getr R (reg 21) = Z_to_bv 64 2147450880
/\ getr R (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ kept_rs R.
Lemma geo : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "H':';'>&QF&RHvS7+^@%3221%73651&QG+_8%7261%;3:31&QE+S0%;2:1%?3>31&QJ+i0%?2>1%C3B31%E251%F2:1%G2?1").
Proof. unfold op, os, ois, tb, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_p, PMSPA.o_is. cbn [pa_off_p pa_off_is ADDR_A]. repeat split; lia. Qed.
Lemma fbb : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "H':';'>&RLvS7+QP0%3221z%73621'<&RG'9%12::%221;(8+4%24>><1r1%446@21v?%:3721qW6C1%=2D1%G2?1").
Proof. destruct FOK as (X & Y). split; [exact Y| exact X]. Qed.
Lemma inW_W0 : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "M'>'<&Q9':&RGr1&QA%33521&Q6r2%2251%8241qW4:1%<2;1&RJ&RHvS7+S0%3221+Q8%5221%721<&RK+iH%9281%32@1%G251p0>1pV6L1").
Proof using All. intros a.
intros (r0 & Hin & Hr). unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hin.
cbn [pa_off_p pa_off_is AD PMA.AD ADDR_A app] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "D'>'=&RKr1&RHvS7+T8%3221%6251&RJ+iH%7261%3219%<251&Q7&QAr2%3221p051pV6C1").
Proof using All. intros a. intros Ha r0 Hr0 Hin. assert (I : exists r1, In r1 W0 /\ L5.in_rng r1 a) by (exists r0; split; assumption). apply inW_W0 in I. lia. Qed.
Lemma wapp_W0 : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "?'=&RJ&RHvS7+QP0%3221+QoonlP0%6221+`PQoooPP0%8216%:231&R>&QA%211p041").
Proof using All.
intros X r0 Hr. unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hr. cbn [pa_off_p pa_off_is AD PMA.AD ADDR_A app] in Hr.
unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; destruct X; [left|right|left|right|left|right|left|right]; lia.
Qed.
Lemma finish_rs : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "W>'R?&Gy5'SKyR0%211%5241'7y8%611%311p061'F'R4'R6&N'6&Q3%211'9'>%2211%611';&R@r:&SJ&RMu1%211%42L1%7261&Q@%115%82N1%<3N41r;u2%;11%=2Q51%@241vRE%@2Q61%D3Q631r<u8%C11%E2Q=1%H241%A14%H2Q>1%L3Q>31r=u9%K11%M2QE1%Q0241%I14%Q02QF1%Q43QF31r>uB%Q311%Q52QM1%Q8241%Q114%Q82QN1%Q<3QN31r?uC%Q;11%Q=2R51%Q@241%Q914%Q@2R61%QD3R631r@uD%QC11%QE2R=1%QH241%QA14%QH2R>1%QL3R>31rAuE%QK11%QM2RE1%R0241%QI14%R02RF1%R43RF31rBuF%R311%R52RM1%R8241%R114%R82RN1%R<3RN31rCuG%R;11%R=2S51%R@241%R914%R@2S61%RD3S631&QCrD%211rEu:%RF11%RH2S@1%RK241%RJ2S@R0%RN3S@21rFu;%RM11%RO2SG1%S2241%S43SF17':&RJz%221R3vS;%42R51%6231&RK&RN+2+J%3221%52R41'=%SC3SFQF<%SD3SGQO=%@221'<&RG(8r2r1%34SNSN21&R3rH%211%83T141%J27QC&RH%12QEQM%22:9%N221%Q0251%Q1271qVJT:1%B2T;1q6T<1%D2T=1&QJ+1%<221%Q821RA%>2RBRJ+H%@261%Q<231%Q>251%Q22:1%Q32Q01&Q4rI%231RCRK&R9rJ%231R>RF&QIrKrG%37258Q21R0R7&QB%117&R=&R0vSE%211%319vSI%64321>'RA&RD&Q=vRF%211&R;rQ0rO+fQc<rNrM%66:54321vA%=4<921p0?1p0G1p0J1p0O1p0Q31p0Q71p0R<1p0RC1p0RK1p0S21p0S:1p0S>1p0SG1p0T01p0T91p0TB1p0TK1p0U41p0U=1p0UF1p0UO1pW0V?1pW2V@1p2V?1pQ:VD1pV:VH1pW@VJ1pW8VL1pVLVN1pQBW01pQHW61pVBW=1").
Proof using All. intros fx R M model s sm cr LK Aw ptr n.
intros E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 KP E10 E11 Hn Hn2 LOC DEF ACC ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK)
(F1 & F2 & F3 & F4 & F5 & F6) STEP.
pose proof RAok as (Hr1 & Hr2).
assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
unfold PMSPA.cfg.
apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xb066c r (ltac:(oW' 0xb066c%Z)) HH AM (ltac:(oF' 0xb066c%Z)) eq_refl (ltac:(oD' 0xb066c%Z)) RA ltac:(lia) Hr2).
intros model1 MRT1 AM1 HH1.
apply (KONT fx R M model1 LK Aw s sm cr ptr n); try assumption.
- apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx. cbn in Hx.
destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
apply KP. destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; cbn; auto 12.
- change (PMSPA.pm_scr 6) with 24576. apply (L5SAR.ahpres_of L ar LBX FF S 24576 _ M0 M EK); [destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
- eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.
Lemma callee_mem : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "RM'SKyR0%211'7y8%511%311p051'6'9'>%2211%411&Q9%611&QDr5%211&QHr6%211&RJzr4%3221&RH+R@%221;+hP0%8221&Q2vS3%211&RN+2+Q?%3221%@251&RBvB&4r8vC%33Q021v?&ROvRE%221Er7r:r9%=9<D8743Q021&Q0r1%27?G<:8J1&Q7&QAr2%3221r3%52;1p031p081pV6QE1':%Q<2B<&RK%12>E%4231%>2D<p021pV6QM1r<%QJ11%QH12&RCr=%29Q6Q>Q3Q1OQAE15%>241%?261p091p0B1p0O1p0Q>1p0QG1p0QM1p0R21p0R61pV2R:1pW>R?1p8R>1pQDRD1pQBRE1").
Proof using All. intros M M' BX scr' W'.
intros (EK & DK & STK) SV Hs Hs2 TOP HP HW HWS.
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M').
{ apply (L5SAR.ek_callee L ar LBX BX FF [] S 24576 (S - 80) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
assert (DKn : L5SAR.dk L ar LBX FF S 24576 M M') by (apply (L5SAR.dk_callee L ar LBX BX FF [] S 24576 (S - 80) scr' W' M M' HP); lia).
assert (KEEPS : forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
{ intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
- apply (L5SAR.stack_client L ar (BX ++ LBX) FF (S - 80) scr' i); lia.
- apply HWS. lia. }
split; [split; [|split]|].
- exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M' EK EKn).
- exact (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M' DK DKn).
- apply (PMKA.astk_after_ahpres L ar _ FF M M' S 24576 (S - 80) scr' W' STK HP); lia.
- split; [|exact EKn]. destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
repeat split; (apply KEEPS; [lia| assumption]).
Qed.
Lemma call_fill (fx : FPState) R M model s sm cr LK Aw (X : Z) :
getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept_rs R ->
getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 (PM.sr_qc (PM.p_src s)) -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
st_ok M model s sm cr LK Aw ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
(PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
(PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
PMSPA.src_step (PM.p_src s) (PM.p_src s) sm sm' ->
st_ok M' model' s sm' cr LK' Aw' ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xaf7f0 M model) K.
Proof using All.
intros A1 RAX A2 KP A10 A11 A12 SO NEXT.
pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
assert (STKr : L5CA.astk ar M (S - 80) 18432).
{ apply (L5SAR.astk_sub ar M M S 24576 80 18432 STK (fun _ Y => Y)); [lia|lia|lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (WAPP0 : PMKA.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
assert (STKSH : shadow_zero M (S - 80 - 18432) (18432 / 8)).
{ change (18432 / 8) with 2304.
assert (M8a : (S - 24576) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 24576) with (S + (-1536) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
assert (M8b : (S - 80 - 18432) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 80 - 18432) with (S + (-1157) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
apply (PMKA.shadow_zero_sub M (S - 24576) 3072); [exact M8a| exact M8b| lia| lia| lia|].
apply (PMKA.stksh_keepA L ar LBX FF S 24576 W0 M0 M EK WAPP0 (S - 24576) 3072); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
assert (FRM : PMSPA.ffroomA 3 FF LK) by (apply (PMARSK.ffroom_incl 6 3 FF LK0 LK FRM0 ILK NDF); lia).
pose proof FBS as SR. unfold PMA.fill_buffer_spec, PMSPA.fill_buffer_spec, PMSPA.src_spec in SR. cbn [pa_fill_buffer AD PMA.AD ADDR_A] in SR.
apply (SR fx R M model K LBX FF LK Aw cr (S - 80) X fb s str sm [] HH AM K0).
{ unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
change (PMSPA.pm_scr 3) with 18432. split; [exact STKr| exact STKSH]. }
{ exact FRM. }
{ intros f Hf. specialize (FRS f Hf). lia. }
{ exact FOK. }
{ rewrite L5K.rl10. exact A10. }
{ unfold PMSPA.fill_args. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11| exact A12]. }
{ reflexivity. }
{ exact PA. } { exact IA. } { exact BASE. } { exact INCS. }
intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 3) with 18432 in HP. rewrite app_nil_r in HP.
destruct RES as (-> & c & Y10 & Hc & G & ST0 & ST2).
assert (ES : PMSPA.with_src s (PM.p_src s) = s) by (destruct s; reflexivity). rewrite ES in PA'.
apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G ST0 ST2 STEP).
destruct (callee_mem M M' (PM.parser_own s) 18432 (PMSPA.W_src AD fb (PM.p_src s)) MR SV ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & EKn).
{ intros a CA OW r0 Hr0 Hin. unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
- apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
-
apply (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ (PM.sr_qc (PM.p_src s)) PM.CHUNK a S 24576 HH); [left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA]. }
{ intros a Ha r0 Hr0 Hin. unfold PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hr0. cbn [pa_off_p pa_off_is AD PMA.AD ADDR_A app] in Hr0.
unfold L5.in_rng in Hin. destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [lia|lia|lia|].
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold PM.CHUNK in *. lia. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
split.
{ apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M' EKn); [| exact BASE].
intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
split; [exact TBOK|]. split; [exact HH'|]. split; [exact AM'|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
split; [exact CRL| exact CRK].
Qed.
Lemma call_srd : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "W6'R?&Gy5'SKyR0%211%5241'7y8%611%311p061'F'R4'R6&N'6&Q3%211'9'>%2211%611';&R@r9&SJ&RMu1%211%42L1%7261r1%72M1%;3M31&Q8r2%211r;u2%=11%?2Q71%B241&ROvRE+R@%3221%E2Q;1%I3Q;61&QCr<%211r=u:%K11%M2QE1%Q0241&QG%Q02QF1%Q43QF31r>u;%Q311%Q52QM1%Q8241&QJ%Q82QN1%Q<3QN31r?u<%Q;11%Q=2R51%Q@241vS;%Q@2R61%QD3R631&QIr:%27:BJLQ81QE&RK&R7&R0%11F%321O&RN+2+J%3221%9251&RH&R8&R2%11H%311%=1J%?21Q3%7231%B21:&OrM%221R;%R=2HQ>%R<2S2R2%R@3S221':&RJzr3%3221%422Q4%6221&R<%O1=r7%Q111rLr6%645321r4%S03S321r8%N11%Q011rN%Q111%Q311r5%Q6221%S93S<61&QO%11S9rO%311%S>3SA31&QM%11QJrQ0%311%SC3SF31&QL%11S6rQ1%311%SH3SK31&QK%11ROrQ2%311%SM3T031&QN%11S2rQ3%311%T23T531'R5%T;11&R1%11S1rQ4%311%T93531&R=rQ5%RB11%341R66S8rDrCr@rBrA%RN7543S6S>21'RA&RD&Q=vRF%211&R;rGrFrE%46832Q21?vA%;4:721p0=1p0D1p0I1p0Q11p0Q71p0Q=1p0QC1p0QI1p0QO1p0R91p0RC1p0RK1p0RO1pV>U@1pV<UF1pWBUH1pW:UJ1p4UB1pQ<UG1pVNUN1pQDV01pQJV61pVDV=1+fU[4%O6Q3LQ:1Q9Q7%Q54Q4Q11Kp041p0SA1p0SK1p0T61p0T:1p0TC1p0TL1p0U51p0U91p0UE1p0UI1pV4V81p2V71pQ:V<1pV:V@1pW@VB1pW8VD1pVLVF1pQBVH1pQHVN1pVBW51").
Proof using All. intros fx R M model s sm cr LK Aw X.
intros A1 RAX A2 KP A10 A11 A12 SO UN UNS NEXT.
pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in *.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
assert (STKr : L5CA.astk ar M (S - 80) 22528).
{ apply (L5SAR.astk_sub ar M M S 24576 80 22528 STK (fun _ Y => Y)); [lia|lia|lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (WAPP0 : PMKA.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
assert (STKSH : shadow_zero M (S - 80 - 22528) (22528 / 8)).
{ change (22528 / 8) with 2816.
assert (M8a : (S - 24576) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 24576) with (S + (-1536) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
assert (M8b : (S - 80 - 22528) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 80 - 22528) with (S + (-1413) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
apply (PMKA.shadow_zero_sub M (S - 24576) 3072); [exact M8a| exact M8b| lia| lia| lia|].
apply (PMKA.stksh_keepA L ar LBX FF S 24576 W0 M0 M EK WAPP0 (S - 24576) 3072); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
assert (FRM : PMSPA.ffroomA 5 FF LK) by (apply (PMARSK.ffroom_incl 6 5 FF LK0 LK FRM0 ILK NDF); lia).
pose proof SRDS as SR. unfold PMA.srd_read_spec, PMSPA.srd_read_spec in SR. cbn [pa_srd_read AD PMA.AD ADDR_A] in SR.
apply (SR fx R M model K LBX FF LK Aw cr (S - 80) X fb len s str sm HH AM K0).
{ unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
change (PMSPA.pm_scr 5) with 22528. split; [exact STKr| exact STKSH]. }
{ exact FRM. }
{ intros f Hf. specialize (FRS f Hf). lia. }
{ exact FOK. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5SAR.r11. exact A11. }
{ rewrite L5SAR.r12. exact A12. }
{ exact Hlen. }
{ exact PA. } { exact IA. } { exact BASE. } { exact TBOK. } { exact INCS. } { exact UN. } { exact UNS. } { exact CRL. }
intros fx' R' M' model' LK' Aw' s' sm' cr' d RP Y10 Hd CONS SZ PA' IA' TB' G1 G2 G3 G4 G5 G6 STEP HP CK MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 5) with 22528 in HP.
apply (NEXT fx' R' M' model' LK' Aw' s' sm' cr' d RP Y10 Hd CONS SZ G1 G2 G3 G4 G5 G6 STEP).
destruct (callee_mem M M' [] 22528 W0 MR SV ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & EKn).
{ intros a _ O. exact O. }
{ intros a Ha. apply outside_W0. lia. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
split.
{ apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M' EKn); [| exact BASE].
intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
split; [exact TB'|]. split; [exact HH'|]. split; [exact AM'|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
split.
- unfold PMSPA.credit_keep, PMSPA.credit_le in *. destruct CRL as (CL1 & CL2). destruct CK as (CK1 & CK2). split; lia.
- unfold PMSPA.credit_keep, PMSPA.credit_le in *. destruct CRK as (CR1 & CR2). destruct CK as (CK1 & CK2). split; lia.
Qed.
Lemma vpack : ltac2:(TCodec.tc2 tcn__PmARdSpan1 "UC'SKyR0%211'7y8%511%311p051'F'R4'R6&N'6&Q3%211'9'>%2211%611&QIr7r6r5r4r3r2r1%877654321'5p0K1&Q1%126;&Mr9%2281':&Q5+RPP0+QV`P0%33=21&Q;&RD+QW[WH+QoooPP0%443B21&Q:+QW[X0+1%347F21&RJ+SoomohPTR@vRE%3221&RN+2+Q?%3221%8261%G261';&RL+@%22;1z%53Q@21&Q<&RO+R@%22A1%44LQ;12%Q3261%Q42=1+8%H21Q@%I2QA7%Q8221r=%;2JQE%Q64Q521QE%=2LQH%Q84Q7QJ1QHp031p071pWJR31pVFR41+VbTP0&QG%Q6221+SooooooofH%Q8231%QG231%O25C%Q13R<1M'=&RH+QoonlP0+`PPPPPTP0%3221%QA21<+Y8%62>1%QD216%9241%R42;1%R52>1&Q?&RI%=2EQ3%221Q4%?21R2+Q4%63RE21%Q?4R7RFJ=%R02KRH%D2RJRI%R221?&Q>%13S0RNRMp031p061pW0S81pV6S91&QJ%R:2Q61+Soooooooo8%R<231%RK231%R325QG%R53S@1R1%R@2Q07+H%Q5291%RC21Q5%Q8241%S3261%S4291%N2>R0%Q;21RN+3%Q23SA21%R;4S3SBB:%RL2CSD%RM2L;p01Jp031pW0T11pV6T21%S22Q?R?%S32AR@&R:v?%231R1QD%332NF%SF221%SG261%SH281%SI2:1%SJ2A1%SK2C1%SL2H1%SM2Q71%SN2QA1%SO2QC1%T02QK1%T12R@1%T22RN1%T32SF1%T42SK1%T52T11tQFU2T71tQ2T=T;1p0T@1p2TJ1pQ:TO1pV:U31pW@U51pW8U71pVLU91pQBU;1").
Proof using All. intros M model s sm cr LK Aw.
intros (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) H MV.
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 24576 80 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
pose proof (PMASK.src_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s S 24576 HH FOK PA STK)
as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
pose proof (PMARSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA)
as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & AT & TFS1 & TFS2).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VIS & _).
fold os in O1, O8, OBIG, OZ, OW, OCE, OAV, AO. fold tb in T1, T8, TBIG, TZ, TW, TCE, TAV, AT.
split; [exact V0|]. split; [exact V1|]. split; [exact V2|].
split; [split; [lia| split; [exact A16| exact V3]]|].
split.
{ intros k v Hk X. apply (proj2 (L5A.u64_at_vis H M (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
split; [split; [lia| split; [exact O8| exact OBIG]]|]. split; [exact OZ|]. split; [exact OW|]. split; [exact OAV|].
split; [split; [lia| split; [exact T8| exact TBIG]]|]. split; [exact TZ|]. split; [exact TW|]. split; [exact TAV|].
split; [lia|]. split; [lia|]. split; [exact AO| exact AT].
Qed.
End Call.
End WithHeap.
End PMARSP1.
