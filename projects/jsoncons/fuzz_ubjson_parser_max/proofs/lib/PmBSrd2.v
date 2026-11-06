(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmTxtKit2 PmBSrcKit PmBReset1 PmBRsKit PmBSrdP PmBSrd1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrd2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBSrd1.PMBSR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw0"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "3Z"; "0FF"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "0LK"; "0LK0"]; ["4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"; "6credit"; "7fframe"; "8SCFG"; "9IHt"; "9acct"; "9fields_eq"; "9lregs"; "9st_ok"; ":CHUNK"; ":mu_src"]; [":p_src"; ":p_tb"; ":pst"; ":strm"; ":vs_size"; ";cfg"; ";consumed"; ";src_step"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"; "0S"; "0SCFG_P"; "?add"; "?le"]; ["?lt"; "?modulo"; "?mul"; "?of_nat"; "?opp"; "?pow"; "?sub"; "0ar"; "0cr"; "0cr0"; "0d"; "0fb"; "0fx"; "0k"; "0len"; "0model"]; ["0model0"; "0mu0"; "0n"; "0s"; "0s0"; "0sm"; "0sm0"; "@Z_to_bv"; "@bv"; "0str"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBSR2.
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
Lemma subw : ltac2:(TCodec.tc2 tcn__PmBSrd2 "Q3'7'5&Q?zr2%3221r1%5231%7231&Q@&QE+2+R0%3221%52:1'6&QA&QF&Q>r3&QB+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pSLQ11pTHQ21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmBSrd2 "G'7'5&Q@&QD&QE+2+R0%3221%511r1%8221z%:231%<231'6&QAr2%221:&Q>%123<%63D31p081pTHF1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmBSrd2 "J'7'5&Q@&QD&QE+2+R0%3221%511r1%8221&Q?z%2241%=241&QAr2%221:+1%A221'6r3%23F1:p041p0:1pTHI1").
Proof. intros x. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
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
#[local] Abbreviation outside_W0 := (PMBSR1.outside_W0 L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Lemma after_shrink : ltac2:(TCodec.tc2 tcn__PmBSrd2 "SO'7&IvQ=v<vQGv9vEvCvR0v;v=v8v?v1vQIvQ<vQKvQNvR4vR9vR6r1%EDDCBA@?>=<;:987654321'Q8&Ay5'R8yR0%211%5241'3y8%611%311p061'@'Q2'Q3&F'2&G%211'4%12Q;Q;%511&Lr:r2%35Q:Q1Q021'6&Q9r;&R7&QCuI%211%42O1%7261%62O;%:3O21'5&Q?zr3%3221r4%5231%7231&N%8241+1r6%;221%<22QH%>221&Mr>r=r<r9r8%6GR>R=R<R;R:R9R7R6R5R4R3R2R1R0QOQN543NQ321&J&QFr7%2251%46R5R4R2981&Q@&O&Q0%11>%321>rD%6221'Q:&Q;&H%11RO&Q5rCrB+f]P@rAr@%66954321%;4:81S0p0=1p0E1p0K1p0Q31p0Q91p0Q<1p0QE1p0R11pSFSB1pTFSC1p2R81pNR<1pSBR@1pT<RB1pT8RD1pT0RF1pQ6RH1pQ:RN1pSJS51pFS71pT4SN1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w d.
intros LR A26 Hd HdC Hw SO AC MU. unfold PM.CHUNK in HdC.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & _).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
set (MV := mrestrict (ahid Aw model) M) in *.
cfeed PP (PMBSRDP.srdF_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 44%nat => d
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E8 & C0) | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0)]).
- apply (ro_step fx fx1 R 0xb3410 R1 0xb3274 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
rewrite subw in C0 by lia.
apply (IH fx1 R1 M model1 s sm cr LK Aw (w - d) MU).
split; [|split; [exact SO1| split; [exact AC| lia]]].
apply (lregs_set R R1 w (w - d) LR); [ks_tac KS1| exact E8].
- apply (ro_step fx fx1 R 0xb3410 R1 0xb348c M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
rewrite subw in C0 by lia.
apply (finish fx1 R1 M model1 s sm cr LK Aw 0); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
+ intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
+ rewrite E10. f_equal. lia.
+ lia.
+ replace 0 with (w - d) by lia. exact AC.
Qed.
Lemma after_read : ltac2:(TCodec.tc2 tcn__PmBSrd2 "UF'7&IvQ=v<vQGv9vEvCvR0v;v=v8v?v1vQIvQ<vQKvQNvR4vR9vR6r1%EDDCBA@?>=<;:987654321'Q8&Ay5'R8yR0%211%5241'3y8%611%311p061'@'Q2'Q3&F'2&G%211'4%12Q;Q;%511&Lr<r4%35Q:Q1Q021'6&Q9r=&R7&QCu:%211%42O1%7261r3%72Q01%;3Q031r>uH%:11%<2Q71%?241r5%?2Q81%C3Q831r?uF%B11%D2Q?1%G241%F2Q?K%J3Q?21'5&Q?zr6%3221r7%5231%7231+1r8%9221r9%;231%=231&N%>241r;%@21R<&MrCrBrAr@%5GS0RORNRMRLRKRIRHRGRFRERDRCRBRAR@4321NQ6Q@&Q4&Q1%116%311&Q>r:%221QL%QJ3S;41%O2N@%81RK%:11&QF%12ROQ;%9231%R13SBR41&Q6&Q0%11S3rE%311rD%6442S51%;2S9H%C21QN%R;3SL31&Q7rF%;11%34;1S<:&KrG%22SA1&Q@&OrH%C11%3216rN%6221'Q:&Q;&H%11T<&Q5rMrL+f\j0rKrJ%66954321%;4:81T=p0=1p0E1p0I1p0N1p0Q91p0Q@1p0QB1p0QK1p0R21p0R51p0R81p0R?1p0RH1p0S01p0S91p0SF1pT6U71pSFU81pSLU91pTFU:1p2SO1pNT31pSBT71pT<T91pT8T;1pT0T=1pQ6T?1pQ:TE1pSJTL1pFTN1pT4UE1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w k d n.
intros LR A10 A24 A27 Hd Hk HkC Hw SO SZ Hn0 En CONS STEP FE MU. unfold PM.CHUNK in HkC.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & _).
assert (Hn : 0 <= n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & _).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
set (MV := mrestrict (ahid Aw model) M) in *.
cfeed PP (PMBSRDP.srdE_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 43%nat => k
| 44%nat => d | 46%nat => n
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E25 & C0) | [(MS1 & KS1 & E8 & E25 & C0 & C1)
| (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]]).
-
apply (ro_step fx fx1 R 0xb3340 R1 0xd3170 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
assert (DK' : d < k).
{ destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
apply (call_resize fx1 R1 M model1 s sm cr LK Aw (d + n) 734224); try assumption.
+ split; [lia| reflexivity].
+ rewrite (KS1 2%nat) by inl. exact A2.
+ intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
+ unfold PM.CHUNK. lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
apply (after_shrink mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w d); try assumption.
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 25%nat RP2) by inl. exact E25.
* lia.
* unfold PM.CHUNK. lia.
* lia.
* unfold PMBSR1.acct. cbn [PMTK2.with_tb PM.p_src PM.p_tb]. split; [lia|]. split; [lia|]. split; [exact STEP|].
destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMBSR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
-
apply (ro_step fx fx1 R 0xb3340 R1 0xb3274 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
rewrite subw in C0 by lia.
assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
apply (IH fx1 R1 M model1 s sm cr LK Aw (w - k) MU).
split; [|split; [exact SO1| split; [|lia]]].
+ apply (lregs_set R R1 w (w - k) LR); [ks_tac KS1| exact E8].
+ unfold PMBSR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
-
apply (ro_step fx fx1 R 0xb3340 R1 0xb348c M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
rewrite subw in C0 by lia.
assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
apply (finish fx1 R1 M model1 s sm cr LK Aw 0); try assumption.
+ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
+ intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
+ rewrite E10. f_equal. lia.
+ lia.
+ unfold PMBSR1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.
End Call.
End WithHeap.
End PMBSR2.
