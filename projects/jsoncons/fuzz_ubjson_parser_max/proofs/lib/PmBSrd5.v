(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmTxtKit2 PmBSrcKit PmBReset1 PmBRsKit PmBSrdP PmBSrd1 PmBSrd2 PmBSrd3 PmBSrd4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrd5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBSrd1.PMBSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw0"; "1app"; "1list"; "1nat"; "1option"; "1prod"; "2and"; "2eq"; "3lt"; "4Z"; "0FF"; "0HI"; "0IH"; "0K"; "0L"]; ["0LBX"; "0LK"; "0LK0"; "5Model"; "6bvmap"; "0M"; "0M0"; "0R"; "0R0"; "7credit"; "8asan_layout"; "8asan_run"; "8fframe"; "8ri_inv"; "8vml_of"; "9SCFG"]; [":IHt"; ":lstate"; ":ois"; ":op"; ":os"; ":tb"; ";ADDR_B"; "<iss_at"; "<mu_src"; "<p_src"; "<p_tb"; "<p_tg"; "<parser_at"; "<parser_own"; "<pot_text"; "<pst"]; ["<srcst"; "<strm"; "<tb_ok"; "=HV"; "=accA"; "=annA"; "=cfg"; "=credit_le"; "=scA"; "=src_step"; ">fill_buffer_tb_spec"; ">src_read_spec"; ">srd_read_spec"; ">str_resize_spec"; "?base_okA"; "@FPState"]; ["@getr"; "Asrealizes"; "Bamodel_ok"; "Bastk"; "Cloaded_segments"; "0S"; "0SCFG_P"; "Dadd"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dopp"; "Dpow"; "Dsub"]; ["Dto_nat"; "0a"; "0ar"; "0cr"; "0cr0"; "0fb"; "0fx"; "0k"; "0len"; "0model"; "0model0"; "0mu0"; "0n"; "0s"; "0s0"; "0sa"]; ["0sm"; "0sm0"; "EZ_to_bv"; "Ebv"; "0str"; "0w"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBSR5.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMB.AD.
Abbreviation pot := PMBSR1.pot.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Lemma subw : ltac2:(TCodec.tc2 tcn__PmBSrd5 "Q3':'7&R8zr2%3221r1%5231%7231&R9&R>+2+R0%3221%52:1'8&R:&R?&R7r3&R;+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pU@Q11pV>Q21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmBSrd5 "G':'7&R9&R=&R>+2+R0%3221%511r1%8221z%:231%<231'8&R:r2%221:&R7%123<%63D31p081pV>F1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmBSrd5 "J':'7&R9&R=&R>+2+R0%3221%511r1%8221&R8z%2241%=241&R:r2%221:+1%A221'8r3%23F1:p041p0:1pV>I1").
Proof. intros x. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size (PM.p_tb s0) + PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PMB.str_resize_spec L ar HI.
Hypothesis SRD : PMB.src_read_spec L ar HI.
Hypothesis FBT : PMB.fill_buffer_tb_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
PMSPA.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s0) + d ->
PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
#[local] Abbreviation op := (PMBSR1.op fb).
#[local] Abbreviation os := (PMBSR1.os fb).
#[local] Abbreviation ois := (PMBSR1.ois fb).
#[local] Abbreviation tb := (PMBSR1.tb fb).
#[local] Abbreviation W0 := (PMBSR1.W0 fb).
#[local] Abbreviation U := (PMBSR1.U R0).
#[local] Abbreviation saves13 := (PMBSR1.saves13 R0 S).
#[local] Abbreviation locals := (PMBSR1.locals S fb len).
#[local] Abbreviation kept_rs := (PMBSR1.kept_rs R0).
#[local] Abbreviation memrel := (PMBSR1.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PMBSR1.fields_eq s0).
#[local] Abbreviation acct := (PMBSR1.acct len s0 sm0).
#[local] Abbreviation st_ok := (PMBSR1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str).
#[local] Abbreviation lregs := (PMBSR1.lregs R0 S fb).
#[local] Abbreviation tbdst := (PMBSR1.tbdst fb).
#[local] Abbreviation lstate := (PMBSR1.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str sm0).
#[local] Abbreviation IHt := (PMBSR1.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S fb len s0 str sm0).
#[local] Abbreviation lregs_keep := (PMBSR1.lregs_keep R0 S fb len Hlen).
#[local] Abbreviation lregs_set := (PMBSR1.lregs_set R0 S fb len Hlen).
#[local] Abbreviation lregs_pres := (PMBSR1.lregs_pres R0 S fb len Hlen).
#[local] Abbreviation geo := (PMBSR1.geo fb).
#[local] Abbreviation fbb := (PMBSR1.fbb FF fb FOK).
#[local] Abbreviation finish := (PMBSR1.finish L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation callee_mem := (PMBSR1.callee_mem L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation centry := (PMBSR1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PMBSR1.call_resize L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PMBSR1.call_srcread L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PMBSR1.call_filltb L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PMBSR1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation vpack := (PMBSR1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation ro_step := (PMBSR1.ro_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation eof_step := (PMBSR1.eof_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation outside_W0 := (PMBSR1.outside_W0 L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.
#[local] Abbreviation rpath := (PMBSR3.rpath L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation dpath := (PMBSR4.dpath L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros x Hx; rewrite (KS x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.
Lemma src_step_refl : ltac2:(TCodec.tc2 tcn__PmBSrd5 "8'Q@'QA&QIr2r1%342211pV051pU471").
Proof. intros a sa. unfold PMSPA.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.
Lemma head : ltac2:(TCodec.tc2 tcn__PmBSrd5 "RG':&Q0vR6v?vRBv<vHvFvRJv>v@v;vBv1vRDvR5vREvRHvRNvS4vS1r1%EDDCBA@?>=<;:987654321'QO&Dy5'S3yR0%211%5241'5y8%611%311p061'C'Q?'QA&I'3&L%211'6%12Q;Q;%511&Q1r9r8r7r6r5r4r3r2%9JQCQBQAQ@Q?Q>Q<Q;Q:Q9Q8Q7Q6Q5Q4Q3Q287654321Q1&R8&Q8&Q9%11:%321:r=%6221'R1&R4&O%11QO&QFr<r;+f\cDr:%5684321I%:4971QOp0<1p0D1pV<R;1p2Q01pQ4Q41pU8Q81pV2Q:1pULQ<1pUDQ>1pQ<Q@1pQ@QF1pU>QM1pLQO1pUHRF1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w.
intros LS MU. pose proof LS as (LR & SO & AC & Hw).
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
destruct SRC as (F240 & _ & _ & _ & F272 & _ & F288 & _).
replace (op + 24 + 240) with (os + 240) in F240 by lia.
replace (op + 24 + 272) with (os + 272) in F272 by lia.
replace (op + 24 + 288) with (os + 288) in F288 by lia.
change PM.CHUNK with 16384 in F272, RM.
pose proof (PMBSK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm S 22528 HH FOK IA STK) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI & IOSB).
fold ois in I1, I8, INSH, Zis, IWR, ICE, IVIS, AOI, IOSB.
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model 0x131ff8 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZOT.
assert (D4 : S - 192 + 192 <= ois \/ ois + 272 <= S - 192) by (right; lia).
assert (D5 : os + 296 <= ois \/ ois + 272 <= os) by (right; lia).
assert (D6 : tb + 24 <= ois \/ ois + 272 <= tb) by (right; lia).
set (MV := mrestrict (ahid Aw model) M) in *.
destruct (Z.eq_dec (PM.sr_rem (PM.p_src s)) 0) as [RZ|RNZ].
-
rewrite RZ in F288.
pose proof IA as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
cbn [pa_vp_iss PMB.AD ADDR_B] in I0.
destruct IOS as (_ & U32 & _).
pose proof (PMTK2.u8_of_u32 RSEGS M (ois + 120 + 32) (PM.sm_st sm) ltac:(lia) U32) as B152.
rewrite Z.mod_small in B152 by lia.
replace (ois + 120 + 32) with (ois + 152) in B152 by lia.
assert (STR : 0 <= PM.sm_st sm <= 2) by lia.
cfeed PP (PMBSRDP.srdH0_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 45%nat => ois | 62%nat => PM.sm_st sm
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
| |- L5.u64_at _ _ ois _ => unfold MV; vis64 IVIS
| |- L5.u8_at _ _ (ois + _) _ => unfold MV; vis8 IVIS
| |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E24 & C0 & C1 & U1) | [(MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E24 & C0 & C1 & U1)
| (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & U1)]]).
+
apply (eof_step fx fx1 R 0xb3274 R1 0xb32b8 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros M1 model1 SO1.
assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
apply (rpath mu0 IH fx1 R1 M1 model1 s sm cr LK Aw w w); try assumption.
* apply (lregs_keep R R1 w LR). ks_tac KS1.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* right. exact ST0.
+
apply (eof_step fx fx1 R 0xb3274 R1 0xb3354 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros M1 model1 SO1.
assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
apply (dpath mu0 IH fx1 R1 M1 model1 s sm cr LK Aw w); try assumption.
* apply (lregs_keep R R1 w LR). ks_tac KS1.
* lia.
+
apply (eof_step fx fx1 R 0xb3274 R1 0xb348c M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros M1 model1 SO1.
apply (finish fx1 R1 M1 model1 s sm cr LK Aw w); try assumption.
all: first [ solve [intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [assumption|]); destruct Hx] | solve [kp_tac KS1 KP]
| solve [rewrite E10; f_equal; lia] | lia ].
-
assert (F256 : True) by exact I.
cfeed PP (PMBSRDP.srdH1_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => PM.sr_rem (PM.p_src s) | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
| |- L5.u64_at _ _ ois _ => unfold MV; vis64 IVIS
| |- L5.u8_at _ _ (ois + _) _ => unfold MV; vis8 IVIS
| |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E24 & C0 & U1) | (MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E24 & C0 & U1)]);
apply (eof_step fx fx1 R 0xb3274 R1 0xb32b8 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1); intros M1 model1 SO1.
+ apply (rpath mu0 IH fx1 R1 M1 model1 s sm cr LK Aw w w); try assumption.
* apply (lregs_keep R R1 w LR). ks_tac KS1.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* left. lia.
+ apply (rpath mu0 IH fx1 R1 M1 model1 s sm cr LK Aw w 16384); try assumption.
* apply (lregs_keep R R1 w LR). ks_tac KS1.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* left. lia.
Qed.
Lemma loop : ltac2:(TCodec.tc2 tcn__PmBSrd5 "RE'4'QO&Dy5'S3yR0%211%5241'5y8%611%311p061'C'Q?'QA&I'3&L%211'6':%2211%611&9&R@&Q8&Q9r6%211r5%5221%711r;%:221&Q1v?vRBv<vHvFvRJv@v;vBv1vRDvR5vREvRHvRNvS4vS1r:r9r8r7r4r3r2%IJHGFEDCBA@?>=<;:987654Q0N321'R1&R4&OvR6%211&QFr<+f\cD%3672Q41@?v>%:49621p0<1p0Q71pV<QE1p2QD1pQ4QI1pU8QM1pV2QO1pULR11pUDR31pQ<R51pQ@R;1pU>RB1pUJRD1").
Proof using All. intros n.
induction n as [|n IHn]; intros fx R M model s sm cr LK Aw w Hn LS; [lia|].
assert (IHm : IHt (PM.mu_src (PM.p_src s) sm)).
{ intros fx' R' M' model' s' sm' cr' LK' Aw' w' Hlt LS'. apply (IHn fx' R' M' model' s' sm' cr' LK' Aw' w'); [|exact LS'].
pose proof LS' as (_ & SO' & _). pose proof (unread_nn _ _ _ _ _ _ _ SO') as (UN' & _).
assert (0 <= PM.mu_src (PM.p_src s') sm') by (unfold PM.mu_src; destruct (Z.eqb _ _); lia). lia. }
exact (head _ IHm fx R M model s sm cr LK Aw w LS ltac:(lia)).
Qed.
Lemma entry_ok : ltac2:(TCodec.tc2 tcn__PmBSrd5 "SN'QO&Mv<&2'6':%2211&Q=vRN%211v@%83521v;vBvRDv1vF&NvRJ%211%C8B9876541&R2%1274&R3vRBvR5+fP0%443;21'8'S3yR0%211&R0vH&S2y5&R<u:%211%5241%8271&Q4vRE%211%:2>1%A3>51u;%;11%>2=1%A2@1&Q5%119%B2F1%I3F41u<%C11%F2E1%I2H1vRH%I2M1%Q03M31&Q<&R4&Q6&QD&QE&Q3%11I&Q2%11K%988765QF31QN&Q7vS4vS1%37<;:QJ521&QN%13>=QL&QB&Q:%11R7&Q;%11R9%5231&QG'J'K'Q?&QHr3&Q>&QCr2%2241r1%@11%?12%73421%:291qUL<1qU6>1qQ0@1v?%231R>RN%D21RI'R1&OvR6%211&QFr<+f\]D%36QA2R>1RORMv>%94QC621p0;1p0Q11p0Q81p0Q;1p0Q@1p0QK1p0R31p0R<1p0RO1p0S51p0S81pU>SM1").
Proof using All. intros fx.
intros HH AM STK A10 A11 A12 PA IA BASE TBOK CRL.
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof geo as (Eop & Eos & Eois & Etb). pose proof fbb as (F1024 & rs & Hfb).
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 22528 192 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
pose proof (PMBSK.src_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb ois s0 S 22528 HH FOK PA STK)
as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
pose proof (PMBRSK.tb_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb ois s0 HH FOK PA)
as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & AT & TFS1 & TFS2).
fold os in O1, O8, OBIG, OZ, OW, OCE, OAV, AO, OFS1, OFS2. fold tb in T1, T8, TBIG, TZ, TW, TCE, TAV, AT, TFS1, TFS2.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
unfold FS_BYTES in OFS2, TFS2, FSCEIL.
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
set (MV := mrestrict (ahid Aw0 model0) M0) in *.
cfeed PP (PMBSRDP.srdA_conc fx R0 MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
set (P := fun a => S - 176 <= a < S - 176 + 176).
assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.parser_own s0 ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x693000)).
{ intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
assert (POST0 : forall M1 model1, ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) ->
mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
memrel M1 /\ PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s0 /\ PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm0 /\ PMSTA.base_okA RSEGS AD M1).
{ intros M1 model1 HH1 VIS1 MGM1 FR1.
assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M0 M1).
{ apply (L5SAR.ek_piece L ar LBX FF S 22528 W0 M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. unfold P in Pa.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 22528 a HH SPT (L5SAR.aclient_appb L ar LBX (PM.parser_own s0) FF S 22528 a CA)) as [X|X]; lia. }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (EKp : L5SAR.ek L ar (PM.parser_own s0 ++ LBX) FF S 22528 [] M0 M1).
{ apply (L5SAR.ek_piece L ar _ FF S 22528 [] M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. unfold P in Pa.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 22528 a HH SPT CA) as [X|X]; lia. }
assert (AOP : PMSPA.aobjA FF op 384).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (AOI : PMSPA.aobjA FF ois 272).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
split; [split; [|split]|].
- exact EKn.
- apply L5SAR.dk_grows. exact MGM1.
- exact (L5SAR.astk_grows ar M0 M1 S 22528 STK MGM1).
- split; [apply (PMKB.parser_keepA RSEGS AD L ar _ FF S 22528 [] M0 M1 EKp PMKB.wapp_nil FRB BRB _ _ _ AOP); [apply incl_appl, incl_refl| intros i _ r0 []| | | |exact PA]|].
{ intros i _ r0 []. } { intros i _ r0 []. } { intros c0 n0 p0 _ i _ r0 []. }
split; [apply (PMKB.iss_keepA RSEGS AD L ar _ FF S 22528 [] M0 M1 EKp PMKB.wapp_nil FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
apply (PMBSK.base_keep L ar C LY LBX FF S 22528 W0 M0 M1 EKn); [intros a Ha; apply outside_W0; pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH); lia| exact BASE]. }
assert (POST : forall M1 model1, ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) -> L5CA.amodel_ok Aw0 model1 -> model_rt model0 model1 ->
mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
saves13 M1v -> locals M1v -> st_ok M1 model1 s0 sm0 cr0 LK0 Aw0).
{ intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 SVv LCv.
destruct (POST0 M1 model1 HH1 VIS1 MGM1 FR1) as (MR1 & PA1 & IA1 & BASE1).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (_ & VIS & _).
assert (BK : forall k v, 8 <= k <= 192 -> L5.u64_at RSEGS M1v (S - k) v -> L5.u64_at RSEGS M1 (S - k) v).
{ intros k v Hk X. apply (proj1 (L5A.u64_at_vis (ahid Aw0 model0) M1 (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
split; [exact MR1|].
split.
{ destruct SVv as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
repeat split; (apply BK; [lia| assumption]). }
split.
{ destruct LCv as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
repeat split; (apply BK; [lia| assumption]). }
split; [exact PA1|]. split; [exact IA1|]. split; [exact BASE1|].
split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [exact MRT1|].
split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact CRL|].
unfold PMSPA.credit_keep. lia. }
bvr.
assert (FE0 : fields_eq s0) by (unfold PMBSR1.fields_eq; repeat split).
assert (AC0 : forall w, w = len -> acct s0 sm0 w).
{ intros w ->. unfold PMBSR1.acct, PMSPA.consumed, PMSPA.src_step. split; [lia|]. split; [lia|].
split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]| exact FE0]. }
unfold PMSPA.cfg.
destruct EX as [(MS & KS1 & E2 & E8 & E9 & E10 & E11 & E13 & E14 & E15 & E18 & E19 & E20 & E21 & E23 & E26 & E27 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21)
| (MS & KS1 & E10 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14)].
-
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb31b4 R1 0xb3274 M1v P K HH AM MS MG1 FZ WOB).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)) as SO1.
rewrite Z.sub_0_r, Z.mod_small in C7 by lia.
pose proof (unread_nn M1 model1 s0 sm0 cr0 LK0 Aw0 SO1) as (UN & _).
apply (loop (Nat.succ (Z.to_nat (PM.mu_src (PM.p_src s0) sm0))) fx1 R1 M1 model1 s0 sm0 cr0 LK0 Aw0 len); [apply Nat.lt_succ_diag_r|].
split; [|split; [exact SO1| split; [exact (AC0 len eq_refl)| lia]]].
unfold PMBSR1.lregs. do 10 (split; [assumption|]).
intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity.
-
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb31b4 R1 0xb348c M1v P K HH AM MS MG1 FZ WOB).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (L0 : len = 0) by (rewrite Z.sub_0_r, Z.mod_small in C0 by lia; lia).
destruct (POST0 M1 model1 HH1 VIS1 MGM1 FR1) as ((EK1 & DK1 & STK1) & PA1 & IA1 & BASE1).
pose proof RAok as (Hr1 & Hr2).
assert (RA : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra0).
apply (PMBSK.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K _ FF LK0 cr0 Aw0 0xb348c r (ltac:(oW' 0xb348c%Z)) HH1 AM1 (ltac:(oF' 0xb348c%Z)) eq_refl (ltac:(oD' 0xb348c%Z)) RA ltac:(lia) Hr2).
intros model2 MRT2 AM2 HH2.
apply (KONT fx1 R1 M1 model2 LK0 Aw0 s0 sm0 cr0 0).
+ apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity.
+ rewrite L5K.rl10, E10. f_equal. lia.
+ lia.
+ unfold PMSPA.consumed. lia.
+ lia.
+ exact PA1.
+ exact IA1.
+ exact TBOK.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ apply src_step_refl.
+ change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M1 EK1); [destruct STK1 as (_ & _ & _ & _ & D & _); exact D| exact DK1].
+ unfold PMSPA.credit_keep. lia.
+ eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
+ apply incl_refl.
+ apply incl_refl.
+ exact AM2.
+ exact HH2.
Qed.
End Call.
Theorem srd_read_ok : ltac2:(TCodec.tc2 tcn__PmBSrd5 "?&QMvR6v?vRBv<%544321&QK%146543&QJ%148765&QL%14:987p031p061p091").
Proof.
intros RSZ SRD FBT. unfold PMB.srd_read_spec, PMSPA.srd_read_spec.
intros fx R M model K LBX FF LK Aw cr sp r fb len s str sm HH AM K0 ENT FRM FRS FOK A10 A11 A12 Hlen PA IA BASE TBOK INCS UN UNS CRL KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 5) with 22528 in *. change (22528 / 8) with 2816 in STKSH.
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12.
exact (entry_ok R M model K LBX FF LK Aw cr sp r fb len s str sm Rra RAok Rsp Rgp Rtp K0 FRM FRS FOK Hlen INCS UNS STKSH RSZ SRD FBT KONT fx HH AM ASTK A10 A11 A12 PA IA BASE TBOK CRL).
Qed.
End WithHeap.
End PMBSR5.
