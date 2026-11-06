(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmTxtKit2 PmASrcKit PmAReset1 PmARsKit PmASrdP PmASrd1 PmASrd2 PmASrd3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmASrd4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmASrd1.PMASR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw0"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0FF"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "0LK"]; ["0LK0"; "4Model"; "5bvmap"; "0M"; "0M0"; "0M1"; "0M1v"; "0R"; "0R0"; "0R1"; "6mrestrict"; "7msteps"; "8credit"; "9ahid"; "9fframe"; ":SCFG"]; [";IHt"; ";acct"; ";fields_eq"; ";lregs"; ";os"; ";st_ok"; "<SRC"; "<mu_src"; "<p_src"; "<p_tb"; "<pst"; "<sm_st"; "<sr_de"; "<sr_qc"; "<sr_rem"; "<strm"]; ["<vs_size"; "=cfg"; "=consumed"; "=src_step"; "=with_src"; ">FPState"; ">getr"; ">mkst"; ">seg_rom"; "?srealizes"; "@mem_grows"; "Aloaded_segments"; "0S"; "0SCFG_P"; "Badd"; "Ble"]; ["Blt"; "Bmodulo"; "Bmul"; "Bof_nat"; "Bopp"; "Bpow"; "Bsub"; "0a"; "0ar"; "0c"; "0cr"; "0cr0"; "0fb"; "0fx"; "0fx1"; "0k"]; ["0len"; "0model"; "0model0"; "0model1"; "0mu0"; "0n"; "0pc"; "0pc1"; "0s"; "0s0"; "0sm"; "0sm0"; "CZ_to_bv"; "Cbv"; "0str"; "0w"]; ["0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMASR4.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PMASR1.pot.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Lemma subw : ltac2:(TCodec.tc2 tcn__PmASrd4 "Q3'8'5&QOzr2%3221r1%5231%7231&R0&R5+2+R0%3221%52:1'6&R1&R6&QNr3&R2+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pU0Q11pV2Q21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmASrd4 "G'8'5&R0&R4&R5+2+R0%3221%511r1%8221z%:231%<231'6&R1r2%221:&QN%123<%63D31p081pV2F1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmASrd4 "J'8'5&R0&R4&R5+2+R0%3221%511r1%8221&QOz%2241%=241&R1r2%221:+1%A221'6r3%23F1:p041p0:1pV2I1").
Proof. intros x. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.
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
Hypothesis FRM0 : PMSPA.ffroomA 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size (PM.p_tb s0) + PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PMA.str_resize_spec L ar HI.
Hypothesis SRD : PMA.src_read_spec L ar HI.
Hypothesis FBT : PMA.fill_buffer_tb_spec L ar HI.
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
#[local] Abbreviation op := (PMASR1.op fb).
#[local] Abbreviation os := (PMASR1.os fb).
#[local] Abbreviation ois := (PMASR1.ois fb).
#[local] Abbreviation tb := (PMASR1.tb fb).
#[local] Abbreviation W0 := (PMASR1.W0 fb).
#[local] Abbreviation U := (PMASR1.U R0).
#[local] Abbreviation saves13 := (PMASR1.saves13 R0 S).
#[local] Abbreviation locals := (PMASR1.locals S fb len).
#[local] Abbreviation kept_rs := (PMASR1.kept_rs R0).
#[local] Abbreviation memrel := (PMASR1.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PMASR1.fields_eq s0).
#[local] Abbreviation acct := (PMASR1.acct len s0 sm0).
#[local] Abbreviation st_ok := (PMASR1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str).
#[local] Abbreviation lregs := (PMASR1.lregs R0 S fb).
#[local] Abbreviation tbdst := (PMASR1.tbdst fb).
#[local] Abbreviation lstate := (PMASR1.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str sm0).
#[local] Abbreviation IHt := (PMASR1.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S fb len s0 str sm0).
#[local] Abbreviation lregs_keep := (PMASR1.lregs_keep R0 S fb len Hlen).
#[local] Abbreviation lregs_set := (PMASR1.lregs_set R0 S fb len Hlen).
#[local] Abbreviation lregs_pres := (PMASR1.lregs_pres R0 S fb len Hlen).
#[local] Abbreviation geo := (PMASR1.geo fb).
#[local] Abbreviation fbb := (PMASR1.fbb FF fb FOK).
#[local] Abbreviation finish := (PMASR1.finish L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation callee_mem := (PMASR1.callee_mem L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation centry := (PMASR1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PMASR1.call_resize L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PMASR1.call_srcread L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PMASR1.call_filltb L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PMASR1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation vpack := (PMASR1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation ro_step := (PMASR1.ro_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation outside_W0 := (PMASR1.outside_W0 L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.
#[local] Abbreviation after_shrink := (PMASR2.after_shrink L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros x Hx; rewrite (KS x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.
Lemma with_src_eta : ltac2:(TCodec.tc2 tcn__PmASrd4 "A'Q:'6&QDr1(Q6&Q=&Q8%114%311&Q<%113&Q>%115%93531%<2;1%>3?1<pUB@1").
Proof. intros s. destruct s as [a b c [q d e] f g h i j]; reflexivity. Qed.
Lemma pos_step : ltac2:(TCodec.tc2 tcn__PmASrd4 "T@'QE&By5'RMyR0%211%5241'8'3y8%711%311p071'A'Q:'Q?&L'2&N%211'4%12>>%511&Q5v=vR8v:vHvDvRBv>v9v@v1vR;vQLvR<vR@vRIvRNr8r7r6r5r4r3r2%HGGFEDCBA@?>=<;:987654321'K&QK&QGr?r=&RLr<%22QC1&J&M%12=Br9%4221&QH%11=%=5<;831r>r;r:%>2QO1%B5431F6%E3D61&QJ%>2K<%@216%321L'5&QOzr1%3221&R0&R5+2+R0%3221%5271%;271&7&QN&Q4%11QE+X0%4221%A21Q>+8%7231%@2QA1%F241%;11'6%Q>2ROQF%QK11%Q<2QMQA%Q>31Q63%53RL31p071p0D1pT@S31%RDGRCRBRAR@R?R>R=R<R;R:R9R8R7R6R5R4QMNQEQ:Q9Q@R3'QI&OvQM%211&QArDrAr@%46R3321R7R6v<%:4R5721p0<1pU8S;1pQ<S=1rC%;6R:198R7R5%@4R;=17p041p0D1p0QF1p0QK1p0RB1pQ>SF1p2S=1pQ0SA1pTFSE1pUFSG1pUBSI1pU4SK1pQ8SM1pU@T31pQDT51pU>T51pQ@T71pTNT>1pTLT?1").
Proof using All. intros fx fx1 R pc R1 pc1 M model s sm cr LK Aw M1v.
intros SO MS MG FRZ NEXT.
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as ((EK & DK & STK) & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof geo as (Eop & Eos & Eois & Etb). pose proof fbb as (F1024 & rs & Hfb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _).
destruct SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
replace (op + 24) with os in F240, F248, F256, F264, F272, F280, F288 by lia.
set (P := fun a => os + 256 <= a < os + 256 + 8).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v P K HH AM MS MG).
{ intros a Ha N. apply FRZ; [exact Ha| exact N]. }
{ intros a Ha Wa. unfold P in Wa. split.
- unfold aclientw, aclient_g. right; right; right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia.
- lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply NEXT.
assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> L5C.agree_on M M1 a n).
{ intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; lia]. }
assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
{ intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= os \/ os + 296 <= q).
{ intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (AGB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> PMFA.agA M M1 q m).
{ intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & VEC & _).
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
destruct (BRB _ VIN) as (VB0 & VB1). destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in VB0, VB1, QB0, QB1.
assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s).
{ rewrite <- (with_src_eta s).
apply (PMASK.parser_src_fieldsA M M1 op ois s (PM.sr_de (PM.p_src s)) (PM.sr_rem (PM.p_src s)) PA);
[lia| lia| | | | lia| cbv [PM.CHUNK] in *; lia| | lia| lia| | | exact MGM1| | | | | lia| lia| cbv [PM.CHUNK] in *; lia].
- split; [apply AGO; lia| apply AGSH; lia].
- split; [apply AGO; lia| apply AGSH; lia].
- apply AGSH; lia.
- exact (AGB _ _ QIN).
- exact (AGB _ _ VIN).
- intros c0 n0 p0 E. apply AGB. apply in_or_app; left. unfold PM.parser_own. rewrite E. right; right; left; reflexivity.
- apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 288) with (os + 264) by lia; exact F264].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 296) with (os + 272) by lia; exact F272].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 304) with (os + 280) by lia; exact F280].
- apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 312) with (os + 288) by lia; exact F288]. }
set (Wp := [(os + 256, 8)]).
assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 22528 Wp M M1).
{ apply (L5SAR.ek_piece L ar _ FF S 22528 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. unfold P in Pa. apply (OWx (os + 256, 8)); [unfold Wp; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (WAPPp : PMKA.wapp Wp) by (unfold Wp; apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKA.wapp_nil]).
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
assert (AOI : PMSPA.aobjA FF ois 272).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
{ apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 22528 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
- intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
- intros c0 n0 p0 E i Hi r0 Hr. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M M1).
{ apply (L5SAR.ek_piece L ar LBX FF S 22528 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PMASR1.W0, PMSPA.W_srcf; left; reflexivity|].
unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2. unfold FS_BYTES in FF2.
split; [split; [|split]|].
- exact (L5SAR.ek_trans L ar LBX FF S 22528 W0 M0 M M1 EK EKn).
- apply (L5SAR.dk_trans L ar LBX FF S 22528 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
- exact (L5SAR.astk_grows ar M M1 S 22528 STK MGM1).
- split.
{ destruct SV as (S8 & S16' & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
split.
{ destruct LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
split; [exact PA1|]. split; [exact IA1|].
split; [apply (PMASK.base_keep L ar C LY LBX FF S 22528 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK].
Qed.
Lemma d_after_fill : ltac2:(TCodec.tc2 tcn__PmASrd4 "U;'8&Q0vQMv=vR8v:vHvDvRBv<v>v9v@v1vR;vQLvR<vR@vRIvRNvRKr1%EDDCBA@?>=<;:987654321'QE&By5'RMyR0%211%5241'3y8%611%311p061'A'Q:'Q?&L'2&N%211'4%12Q;Q;%511&Q3r;r3%35Q:Q1Q021'6&QFr<&RL&R3u:%211%42O1%7261r2%72Q01%;3Q031r=uH%:11%<2Q71%?241+`P0%?2Q81%C3Q831r>uK%B11%D2Q?1%G241r5%G2Q@1%K3Q@31'5&QOz%2216%327?%5221r8%62B1%722R4%9221&Q5r@r?r:%4GRHRGRFRERDRCRAR@R?R>R=R<R;R:R9R832FNQ8Q=1&Q@&Q9%115%311&QNr9%221Q0%QB3S341%F2E:%81RC%:11&R6%12RGQE%9231%QI3S:QL1&QB&Q8%11RKrB%311rA%6442RM1%;2S1QE%C21R5%R33SD31&QCrC%;11%34;1S4:&Q2rD%22S91&R0&Q7rE%C11%3216rK%6221'QI&QK&O%11T4&QArJrI+fUo0rHrG%66954321%;4:81T5p0=1p0E1p0I1p0N1p0Q91p0Q@1p0QB1p0QK1p0R11p0R61p0R=1p0RF1p0RO1p0S<1pTDTM1pU<TN1pV0TO1p2SD1pQ0SH1pTFSL1pUFSN1pUBT01pU4T21pQ8T41pQ@T:1pTLTA1pHTC1pU:U:1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w n c.
intros LR A10 A24 A27 Hc Hw SO SZ Hn0 En CONS STEP FE MU.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
assert (Hn : n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
destruct SRC as (_ & _ & F256 & _). replace (op + 24 + 256) with (os + 256) in F256 by lia.
set (MV := mrestrict (ahid Aw model) M) in *.
cfeed PP (PMASRDP.srdD3_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 44%nat => c | 46%nat => n
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
destruct EX as [(MS1 & KS1 & E1 & E10 & E11 & E12 & E26 & C0) | [(MS1 & KS1 & E11 & E25 & E26 & C0 & C1)
| (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]];
apply (pos_step fx fx1 R 0xb17e0 R1 _ M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1); intros M1 model1 SO1.
-
assert (DK' : c < 16384).
{ destruct (Z.eq_dec c 16384) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
apply (call_resize fx1 R1 M1 model1 s sm cr LK Aw (c + n) 727068 E1 ltac:(split; [lia| reflexivity])); try assumption.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ kp_tac KS1 KP.
+ unfold PM.CHUNK. lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
refine (after_shrink mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w c _ _ ltac:(lia) ltac:(unfold PM.CHUNK; lia) ltac:(lia) SO2 _ MU).
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 26%nat RP2) by inl. exact E26.
* unfold PMASR1.acct. cbn [PMTK2.with_tb PM.p_src PM.p_tb]. split; [lia|]. split; [lia|]. split; [exact STEP|].
destruct FE as (F1 & F2 & F3' & F4 & F5 & F6). unfold PMASR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
-
replace (18446744073709535232) with ((18446744073709551615 * 16384) mod 2 ^ 64) in C0 by reflexivity.
rewrite subw in C0 by lia.
assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
apply (IH fx1 R1 M1 model1 s sm cr LK Aw (w - 16384) MU).
split; [|split; [exact SO1| split; [|lia]]].
+ apply (lregs_set R R1 w (w - 16384) LR); [ks_tac KS1| exact E25].
+ unfold PMASR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
-
replace (18446744073709535232) with ((18446744073709551615 * 16384) mod 2 ^ 64) in C0 by reflexivity.
rewrite subw in C0 by lia.
assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
apply (finish fx1 R1 M1 model1 s sm cr LK Aw 0); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
+ kp_tac KS1 KP.
+ rewrite E10. f_equal. lia.
+ lia.
+ unfold PMASR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.
Lemma d_after_resize : ltac2:(TCodec.tc2 tcn__PmASrd4 "U1'8&Q0vQMv=vR8v:vHvDvRBv<v>v9v@v1vR;vQLvR<vR@vRIvRNvRKr1%EDDCBA@?>=<;:987654321'QE&By5'RMyR0%211%5241'3y8%611%311p061'A'Q:'Q?&L'2&N%211'4%12Q;Q;%511&Q3r:r2%35Q:Q1Q021'6&QFr;&RL&R3uH%211%42O1%7261+`P0%72Q01%;3Q031r<uK%:11%<2Q71%?241r3%?2Q81%C3Q831'5&QOr5%22>1%322QH%5221&Q5r=r9r8r7%5GR=R<R;R:R9R8R6R5R4R3R2R1R0QOQNQM4CMQ2321&Q@&Q9%11F%311&QNr6%221M%Q73RH41z%D21;%91R9%;11&R6%12R=A%:231%Q?3S0B1&QB&Q8%11RAr?%311r>%6442RC1%;2RGQJ%QH3S921&QCr@%:11%34:1RI9&Q2rA%22RN1&Q;%113%R23SC1J&Q7rC%D11rB%4221rI%QD221'QI&QK&O%11SL&QArHrG+fUm4rFrE%66954321%;4:81SMp0=1p0E1p0I1p0M1p0Q21p0Q<1p0QC1p0QF1p0QO1p0R61p0R=1p0RF1p0S31pU<TD1pV0TE1p2S:1pQ0S>1pTFSB1pUFSD1pUBSF1pU4SH1pQ8SJ1pQ@T01pTLT71pHT91pU:U01").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w n.
intros LR A24 A27 Hw SO SZ Hn0 En CONS STEP FE ST0 MU.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
assert (Hn : n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (op + 336) with tb in VS by lia.
set (MV := mrestrict (ahid Aw model) M) in *.
revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ; cbn [PM.vs_size] in SZ.
-
exfalso. destruct VS as (Hn1 & _). lia.
- destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
assert (IN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (WB _ IN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
assert (F256 : True) by exact I.
cfeed PP (PMASRDP.srdD2_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => (c1 + 1) mod 256 | 42%nat => q1 | 46%nat => n
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
apply (ro_step fx fx1 R 0xb17a4 R1 0xaf7f0 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
apply (call_filltb fx1 R1 M model1 s sm cr LK Aw (q1 + n) 727008 c1 n1 q1 E1 ltac:(split; [lia| reflexivity])); try assumption.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ kp_tac KS1 KP.
+ lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 sm2 c RP2 Y10 Hc G2 STF ST2F STEP2 SO2.
destruct (STF ST0) as (Ec & ST2).
pose proof (unread_nn M2 model2 s sm2 cr LK2 Aw2 SO2) as (UN2 & ST2' & RM2 & GE2).
assert (CONS2 : PMSPA.consumed (PM.p_src s) (PM.p_src s) sm sm2 = c).
{ unfold PMSPA.consumed, PM.unread. destruct STEP2 as (_ & E2 & _). lia. }
refine (d_after_fill mu0 IH fx2 R2 M2 model2 s sm2 cr LK2 Aw2 w n c _ Y10 _ _ ltac:(unfold PM.CHUNK in Hc; lia) Hw SO2 _ Hn0 En _ _ FE _).
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
* rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. rewrite (KS1 27%nat) by inl. exact A27.
* rewrite ETB. cbn [PM.vs_size]. exact SZ.
* unfold PMSPA.consumed in *. lia.
* exact (PMASR3.src_step_trans _ _ _ _ _ _ STEP STEP2).
* enough (PM.mu_src (PM.p_src s) sm2 < PM.mu_src (PM.p_src s) sm) by lia.
apply (PMASR3.mu_dec _ _ _ _ STEP2 ST ST2').
destruct (Z.ltb_spec c PM.CHUNK) as [LT|GE']; [right; split; [exact ST0| exact ST2]| left].
unfold PMSPA.consumed in CONS2. unfold PM.CHUNK in *. lia.
Qed.
Lemma dpath : ltac2:(TCodec.tc2 tcn__PmASrd4 "SE'8&Q0vQMv=vR8v:vHvDvRBv<v>v9v@v1vR;vQLvR<vR@vRIvRNvRKr1%EDDCBA@?>=<;:987654321'QE&By5'RMyR0%211%5241'3y8%611%311p061'A'Q:'Q?&L'2&N%211'4%12Q;Q;%511&Q3r9%25Q9Q0O1J'6&QFr:&RL&R3uH%211%42N1%7261+`P0%72O1%;3O31'5&QOr3%2261%322Q?%5221&Q5r;r8r7r6r5%6GR5R4R3R2R1R0QNQMQLQKQJQIQHQGQFQE5FJ4321&Q1%16QIQHQFHL3&Q;%11Jz%N3R>21&Q7&Q8r<%211%421@rB%H221'QI&QK&O%11RG&QArAr@+fUk4r?r>%66954321%;4:81RHp0=1p0E1p0J1p0M1p0Q51p0Q<1p0QI1pV0S91p2QN1pQ0R21pTFR61pUFR81pUBR:1pU4R<1pQ8R>1pQ@RD1pTLRK1pHRM1pU:SD1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w.
intros LR A24 Hw SO (CONS & SZ & STEP & FE) ST0 MU.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (op + 336) with tb in VS by lia.
assert (HSZ : PM.vs_size (PM.p_tb s) < 67108864) by (unfold PMSPA.consumed in CONS; lia).
assert (F256 : True) by exact I.
set (MV := mrestrict (ahid Aw model) M) in *.
revert VS SZ HSZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ HSZ; cbn [PM.vs_size] in SZ, HSZ.
-
destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMASRDP.srdDS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => 2 * n1
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E27)).
apply (ro_step fx fx1 R 0xb1764 R1 0xd1338 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + 16384)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
assert (E27' : getr R1 (reg 27) = Z_to_bv 64 n1) by (rewrite E27; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + 16384) 726948 E1 ltac:(split; [lia| reflexivity])); try assumption.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ kp_tac KS1 KP.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
refine (d_after_resize mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w n1 _ _ _ Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ ST0 MU).
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
* rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. exact E27'.
* destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMASR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
cfeed PP (PMASRDP.srdDL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => (c1 + 1) mod 256 | 41%nat => n1
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E27)).
apply (ro_step fx fx1 R 0xb1764 R1 0xd1338 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + 16384) 726948 E1 ltac:(split; [lia| reflexivity])); try assumption.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ kp_tac KS1 KP.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
refine (d_after_resize mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w n1 _ _ _ Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ ST0 MU).
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
* rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. exact E27.
* destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMASR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
Qed.
End Call.
End WithHeap.
End PMASR4.
