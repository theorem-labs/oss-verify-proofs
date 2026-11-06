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
PmModelFactsA PmStepA PmStep PmTxtKit2 PmASrcKit PmAReset1 PmARsKit PmASrdP PmASrd1 PmASrd2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmASrd3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmASrd1.PMASR1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw0"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2or"; "3Z"; "0FF"; "0HI"; "0IH"; "0K"; "0L"; "0LBX"; "0LK"]; ["0LK0"; "4Model"; "5bvmap"; "0M"; "0M0"; "0R"; "0R0"; "6credit"; "7fframe"; "8SCFG"; "9IHt"; "9acct"; "9fields_eq"; "9lregs"; "9os"; "9st_ok"]; ["9tbdst"; ":CHUNK"; ":mu_src"; ":p_src"; ":p_tb"; ":pst"; ":sm_st"; ":sr_rem"; ":srcst"; ":strm"; ":unread"; ":vs_size"; ";cfg"; ";consumed"; ";src_step"; "<FPState"]; ["<getr"; "=srealizes"; ">loaded_segments"; "0S"; "0SCFG_P"; "?add"; "?le"; "?lt"; "?modulo"; "?mul"; "?of_nat"; "?opp"; "?pow"; "?sub"; "0a"; "0ar"]; ["0b"; "0c"; "0cr"; "0cr0"; "0fb"; "0fx"; "0k"; "0len"; "0model"; "0model0"; "0mu0"; "0n"; "0p"; "0s"; "0s0"; "0sa"]; ["0sb"; "0sc"; "0sm"; "0sm'"; "0sm0"; "0src"; "0src'"; "@Z_to_bv"; "@bv"; "0str"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMASR3.
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
Lemma subw : ltac2:(TCodec.tc2 tcn__PmASrd3 "Q3'8'5&QFzr2%3221r1%5231%7231&QG&QL+2+R0%3221%52:1'6&QH&QM&QEr3&QI+_oooooooooooOr4%3221%821;%7261%:21=%:21H%<21?%<2:7%?3N21p0A1p0H1pT>Q11pUHQ21").
Proof. intros x k.
intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg : ltac2:(TCodec.tc2 tcn__PmASrd3 "G'8'5&QG&QK&QL+2+R0%3221%511r1%8221z%:231%<231'6&QHr2%221:&QE%123<%63D31p081pUHF1").
Proof. intros x. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 : ltac2:(TCodec.tc2 tcn__PmASrd3 "J'8'5&QG&QK&QL+2+R0%3221%511r1%8221&QFz%2241%=241&QHr2%221:+1%A221'6r3%23F1:p041p0:1pUHI1").
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
#[local] Abbreviation after_read := (PMASR2.after_read L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Lemma src_step_trans : ltac2:(TCodec.tc2 tcn__PmASrd3 "B'Q8'Q9&Q>r6r5r3r2%544321r8%741654p031p041pU4;1pU2<1pU0=1pT4?1pT2@1pSNA1").
Proof. intros a b c sa sb sc.
unfold PMSPA.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Lemma mu_dec : ltac2:(TCodec.tc2 tcn__PmASrd3 "Q>'Q8'Q9&Q>r4r3r2r1%544321'7'6'8&Q6%118z%53421+2%73641%9231&QG&Q:r6%221Br7r5%5221%7241'5%@14%C3B1?%B1J%E3D1?%5231%H271&Q2%12<;r8%321@%C231p061p0F1p0G1p0Q21pU8Q91pU6Q:1pU>Q<1pU<Q=1").
Proof. intros src src' sm sm'.
unfold PM.mu_src. intros (_ & _ & _ & S2 & U) ST ST' H.
destruct ST as [E|E]; destruct ST' as [E'|E']; rewrite ?E, ?E' in *; cbn [Z.eqb]; [lia|lia| specialize (S2 eq_refl); lia| lia].
Qed.
Lemma at_srcread : ltac2:(TCodec.tc2 tcn__PmASrd3 "VD'8&JvQDv=vQOv:vFvDvR9v<v>v9v@v1vR3vQCvR4vR7vR>vRIvRDr1%EDDCBA@?>=<;:987654321'Q?&By5'RHyR0%211%5241'3y8%611%311p061'A'Q5'Q9&G'2&H%211'4%12Q;Q;%511&Mr<r4%35Q:Q1Q021'6&Q@r=&RG&QJu1%211%42O1%7261+fUjD%72Q01%;3Q031r>u:%:11%<2Q71%?241&N%11QC%@2Q91%D3Q941r?u;%C11%E2Q@1%H241%G2Q@L%K3Q@21r@u<%J11%L2QG1%O241r7%O2QH1%Q33QH31rAuH%Q211%Q42QO1%Q7241r8%Q72R01%Q;3R031rBuK%Q:11%Q<2R71%Q?241%QA3R617'5&QF+1r:%3221r;%5231%7231&Q1%8241%92QJRL&Q0rC%24S018QM&OrFrErD%4GSBSAS@S?S>S=S;S:S9S8S7S6S5S4S3S23216HQ0Q8&Q;&Q4%115%311&QE%12QNQE%R;3SL31z%J21QH%81S=%:11&QM%12SAQ5%9231%RC3T4QG1&Q=&Q3%11SErH%311rG%6442SG1%;2SKM%RL3T=21&Q>rI%:11%34:1SM9&LrJ%22T21'7&Q7rK%B11%311%QF2QE1&Q6%119%S<3TM1Q0%9241&Q2rL%K11%321;rQ2%R0221'QA&QB&I%11U6&Q<rQ1rQ0+eliDrOrN%66954321%;4:81U7p0=1p0D1p0O1p0Q31p0Q81p0QB1p0QI1p0QL1p0R41p0R:1p0R>1p0R@1p0RC1p0RL1p0S31p0S<1p0SE1p0SM1p0T71p0TD1pTJV51pTHV61pT>V71pUFV81p2TM1pQ0U11pT6U51pU6U71pTLU91pTBU;1pQ8U=1pQ<UC1pT<UJ1pHUL1pTFVC1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w k n p.
intros LR A1 A10 A11 A12 A24 A27 Hk HkC Hw DST SO SZ Hn0 En CONS STEP FE PRG MU.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
apply (call_srcread fx R M model s sm cr LK Aw p k 0xb1754 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 ltac:(lia) DST SO).
intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 d RP2 Y10 Hd CONS2 POS ZERO STEP2 SO2.
pose proof (unread_nn M2 model2 _ sm2 cr LK2 Aw2 SO2) as (UN2 & ST2 & RM2 & GE2). cbn [PMSPA.with_src PM.p_src] in UN2, RM2.
refine (after_read mu0 IH fx2 R2 M2 model2 (PMSPA.with_src s src2) sm2 cr LK2 Aw2 w k d n (lregs_pres R R2 w RP2 LR) Y10 _ _ Hd Hk HkC Hw SO2 SZ Hn0 En _ _ FE _).
- rewrite (L5SAR.cs_of_preserved R R2 24%nat RP2) by inl. exact A24.
- rewrite (L5SAR.cs_of_preserved R R2 27%nat RP2) by inl. exact A27.
- unfold PMSPA.consumed in *. cbn [PMSPA.with_src PM.p_src]. lia.
- cbn [PMSPA.with_src PM.p_src]. exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
- cbn [PMSPA.with_src PM.p_src]. enough (PM.mu_src src2 sm2 < PM.mu_src (PM.p_src s) sm) by lia.
apply (mu_dec _ _ _ _ STEP2 ST ST2).
unfold PMSPA.consumed in CONS2. destruct (Z.eq_dec d 0) as [D0|D0]; [right| left; lia].
destruct (ZERO D0) as (_ & E2). split; [|exact E2].
destruct PRG as [P1|P1]; [specialize (POS P1); lia| exact P1].
Qed.
Lemma after_resize1 : ltac2:(TCodec.tc2 tcn__PmASrd3 "U='8&JvQDv=vQOv:vFvDvR9v<v>v9v@v1vR3vQCvR4vR7vR>vRIvRDr1%EDDCBA@?>=<;:987654321'Q?&By5'RHyR0%211%5241'3y8%611%311p061'A'Q5'Q9&G'2&H%211'4%12Q;Q;%511&Mr;r3%35Q:Q1Q021'6&Q@r<&RG&QJuH%211%42O1%7261%62O;%:3O21r=uK%911%;2Q61%>241%@3Q517'5&QF+1r5%3221r6%5231%7231&Q1%8241r8%:21QL&Or@r?r>r:%5GR@R?R>R=R<R;R9R8R7R6R5R4R3R2R1R0432GQ0Q51&Q;&Q4%116%311&QEr9%22>1%Q:3RK41z%J214%91R<%;11&QM%12R@Q>%:231%QB3S3A1&Q=&Q3%11RDrB%311rA%6442RF1%;2RJQ?%QK3S<21&Q>rC%:11%34:1RL9&LrD%22S11'7&Q7rE%B11%311%QF2QE1&Q6%119%R;3SL1Q0%9241&Q2rF%K11%321;rL%R0221'QA&QB&I%11T5&Q<rKrJ+fUhHrIrH%66954321%;4:81T6p0=1p0D1p0O1p0Q31p0Q81p0QB1p0QI1p0QL1p0R51p0R<1p0R?1p0RB1p0RK1p0S21p0S>1pTHTO1pT>U01pUFU11p2SF1pQ0SJ1pT6SN1pU6T01pTLT21pTBT41pQ8T61pQ<T<1pT<TC1pHTE1pTFU<1").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w k n.
intros LR A24 A27 Hk HkC Hw SO SZ Hn0 En CONS STEP FE PRG MU.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
assert (Hn : n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (op + 336) with tb in VS by lia.
assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
set (MV := mrestrict (ahid Aw model) M) in *.
revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ; cbn [PM.vs_size] in SZ.
-
destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMASRDP.srdQS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => 2 * n1 | 43%nat => k | 46%nat => n
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
apply (ro_step fx fx1 R 0xb1718 R1 0xaf334 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
refine (at_srcread mu0 IH fx1 R1 M model1 s sm cr LK Aw w k n (tb + n + 1) _ E1 E10 E11 E12 _ _ Hk HkC Hw _ SO1 _ Hn0 En CONS STEP FE PRG MU).
+ apply (lregs_keep R R1 w LR). ks_tac KS1.
+ rewrite (KS1 24%nat) by inl. exact A24.
+ rewrite (KS1 27%nat) by inl. exact A27.
+ unfold PMASR1.tbdst. left. split; [exists n1; exact ETB|]. lia.
+ rewrite ETB. exact SZ.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
assert (IN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (WB _ IN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
cfeed PP (PMASRDP.srdQL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => (c1 + 1) mod 256 | 42%nat => q1 | 43%nat => k | 46%nat => n
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
apply (ro_step fx fx1 R 0xb1718 R1 0xaf334 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
refine (at_srcread mu0 IH fx1 R1 M model1 s sm cr LK Aw w k n (q1 + n) _ E1 E10 E11 E12 _ _ Hk HkC Hw _ SO1 _ Hn0 En CONS STEP FE PRG MU).
+ apply (lregs_keep R R1 w LR). ks_tac KS1.
+ rewrite (KS1 24%nat) by inl. exact A24.
+ rewrite (KS1 27%nat) by inl. exact A27.
+ unfold PMASR1.tbdst. right. exists c1, n1, q1. split; [exact ETB|]. lia.
+ rewrite ETB. exact SZ.
Qed.
Lemma rpath : ltac2:(TCodec.tc2 tcn__PmASrd3 "T4'8&JvQDv=vQOv:vFvDvR9v<v>v9v@v1vR3vQCvR4vR7vR>vRIvRDr1%EDDCBA@?>=<;:987654321'Q?&By5'RHyR0%211%5241'3y8%611%311p061'A'Q5'Q9&G'2&H%211'4%12Q;Q;%511&Mr:r2%35Q:Q1Q021'6&Q@r;&RG&QJuH%211%42O1%7261%62O;%:3O21'5&QF+1r3%3221r4%5231%7231&Q1%8241r6%:21QF&Or>r=r<r9r8%6GR;R:R9R8R7R6R4R3R2R1R0QOQNQMQLQK543KQ021&K%16QOQNQL653'7&Q7&Q3%11;%311%I2H1&Q6%11>z%Q93RJ21%:251&Q2r?%;11%321FrE%Q4221'QA&QB&I%11S3&Q<rDrC+fUfHrBrA%66954321%;4:81S4p0=1p0D1p0Q01p0Q31p0Q;1p0Q>1p0QA1p0QJ1p0R61pT>SG1pUFSH1p2R=1pQ0RA1pT6RE1pU6RG1pTLRI1pTBRK1pQ8RM1pQ<S31pT<S:1pHS<1pTFT31").
Proof using All. intros mu0 IH fx R M model s sm cr LK Aw w k.
intros LR A24 Hk HkC Hw SO (CONS & SZ & STEP & FE) PRG MU.
pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
pose proof geo as (Eop & Eos & Eois & Etb).
assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
bvr.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
replace (op + 336) with tb in VS by lia.
assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
assert (HSZ : PM.vs_size (PM.p_tb s) < 67108864) by (unfold PMSPA.consumed in CONS; lia).
set (MV := mrestrict (ahid Aw model) M) in *.
revert VS SZ HSZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ HSZ; cbn [PM.vs_size] in SZ, HSZ.
-
destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
cfeed PP (PMASRDP.srdRS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => 2 * n1 | 43%nat => k
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E27)).
apply (ro_step fx fx1 R 0xb16d8 R1 0xd1338 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + k)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
assert (E27' : getr R1 (reg 27) = Z_to_bv 64 n1) by (rewrite E27; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + k) 726808 E1 ltac:(split; [lia| reflexivity])); try assumption.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
refine (after_resize1 mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w k n1 _ _ _ Hk HkC Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ PRG MU).
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
* rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. exact E27'.
* destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMASR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
-
destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
cfeed PP (PMASRDP.srdRL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
| 40%nat => (c1 + 1) mod 256 | 41%nat => n1 | 43%nat => k
| 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
| 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
| |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
| |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
| |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
| |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
| |- _ => lia end]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E27)).
apply (ro_step fx fx1 R 0xb16d8 R1 0xd1338 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + k) 726808 E1 ltac:(split; [lia| reflexivity])); try assumption.
+ rewrite (KS1 2%nat) by inl. exact A2.
+ intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
+ rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
+ unfold PM.CHUNK. lia.
+ intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
refine (after_resize1 mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w k n1 _ _ _ Hk HkC Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ PRG MU).
* apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
* rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
* rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. exact E27.
* destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PMASR1.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
repeat split; assumption.
Qed.
End Call.
End WithHeap.
End PMASR3.
