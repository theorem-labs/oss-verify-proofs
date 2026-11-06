(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmFrame PmKitS PmCertKitS L5KnA PmIssStmts PmIssSP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmIss1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmIssSP.PMISP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmIssStmts.PMIS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"; "0K"; "0L"]; ["0LB"; "0LBc"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"; "0M1"; "0R0"; "0R1"; "6credit"; "6hl_sptop"; "7hpres"; "7stk"; "9defined"; "9outside"]; ["9range"; "8SCFG"; ":KS_icA"; ":KS_icB"; ";CSK"; ";WF"; ";mid"; ";pre"; "<vstr"; "=cfg"; ">locale_ctor_spec"; "?cs_all"; "?dk"; "?inW"; "@FPState"; "ATSet"]; ["Bsrealizes"; "Cloaded_segments"; "0SCFG_P"; "DIn"; "Eadd"; "Ele"; "Elt"; "Epow"; "0W'"; "0a"; "0b"; "0cr"; "0fx"; "0fx1"; "0k"; "0model0"]; ["0model1"; "0n"; "0ois"; "0os"; "0r"; "0s"; "0scr"; "0scr'"; "0sp"; "0sp'"; "FZ_to_bv"; "Fbv"]]).
Local Ltac lia := L5FastLia.plia.
Module PMIS1.
Import PMS.
Lemma csk_icA : ltac2:(TCodec.tc2 tcn__PmIss1 ":'3&QCr1&Q4%33421r2&Q2%63721p041pSN91"). Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icB : ltac2:(TCodec.tc2 tcn__PmIss1 ":'3&QCr1&Q4%33421r2&Q3%63721p041pSN91"). Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_cs : ltac2:(TCodec.tc2 tcn__PmIss1 ":'3&QCr1&Q4%33421r2&Q;%63721p041pSN91"). Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma locW_low (b : bool) a : PMK.inW (if b then [] else PMSP.loc_W AD) a -> 0xc6492 <= a < 0xc7350.
Proof.
destruct b; intros (rg & Hin & Hr); [destruct Hin|]. unfold PMSP.loc_W in Hin. cbn [map pa_loc_foot AD PmLayoutS.ADDR_S fst snd] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma WF_inv : ltac2:(TCodec.tc2 tcn__PmIss1 "N'<'0&Q=&Q5r3r2%3221r1%6221';'8&QEr4%2218&QF&QD+X@%2251%42=1%9261+hiTB%:21@+hlj@%92B1%>231%@261p0B1pSDK1pSFK1pT6M1").
Proof. intros ois b a.
unfold PMIS.WF. intros (rg & [<-|Hin] & Hr); [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
right. apply (locW_low b a). exists rg. split; assumption.
Qed.
Lemma W1_inv (o : Z) (b : bool) (a : Z) : PMK.inW ((o, 8) :: (if b then [] else PMSP.loc_W AD)) a -> (o <= a < o + 8) \/ 0xc6492 <= a < 0xc7350.
Proof.
intros (rg & [<-|Hin] & Hr); [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
right. apply (locW_low b a). exists rg. split; assumption.
Qed.
Lemma outside_WF : ltac2:(TCodec.tc2 tcn__PmIss1 "N'<'0';&QFr1r3%3221&QE&QD+X@%2251%4217%:261r2+hiTB%<221+hlj@%:214%@231&O&Q5r5r4%3221%521Cp071p0>1pSDK1pSFK1pT6M1").
Proof. intros ois b a.
intros H1 H2. apply PMFR.outside_of_not_inW. intros I. destruct (WF_inv ois b a I); lia.
Qed.
Lemma outside_WF_ois : ltac2:(TCodec.tc2 tcn__PmIss1 "H'<'0&O&Q5r3r2%3221r1%6221(1'7%12;;(6r4+X@%34??21(4%116%93731%A21>p0<1pSDE1pSFE1pT6G1").
Proof. intros ois b a.
intros O. unfold PMIS.WF in O. apply L5C.outside_cons_inv in O. apply L5C.outside_cons; [exact (proj1 O)| apply L5C.outside_nil].
Qed.
Ltac t14 AG C := lazymatch type of C with
| L5.u64_at _ ?Ms _ _ => apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | exact C]
| L5.u32_at _ ?Ms _ _ => apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | exact C]
| L5.u8_at _ ?Ms _ _ => apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | exact C]
| L5.defined ?Ms _ _ => apply (L5C.defined_agree Ms); [intros i Hi; apply AG; lia | exact C]
| L5KA.zeros_at ?Ms _ _ => apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
| PM.zeros_at ?Ms _ _ => apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
end.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma callee_ag : ltac2:(TCodec.tc2 tcn__PmIss1 "R1'2'7'<%2211%411&Q0%611'R;yR0%211'5y8%511%311p051&Lv?r6r5r4r3r2r1%877654321&M&K%11:%3417:9&QEz%221='8r9%521;&QF&QG+2+R0%3221%52A1%9271&:&Q=r8%221G%411'9r7&R:%12Q9M%311%812%63Q721p081p0>1pSDQE1p0J1p0N1p0Q31pQ<Q=1pQ:Q>1pSBQG1pT@QL1pTDQM1pQ4QL1").
Proof. intros LBc sp' scr' W' M M'.
intros HP STK S0 a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
apply (PMKP.kept_stack RSEGS L KL LBc M sp' scr' W' a STK S0 Ha). apply PMFR.outside_of_not_inW. exact N.
Qed.
Lemma defined_dk : ltac2:(TCodec.tc2 tcn__PmIss1 "QF'2'7'<%2211%411'R;yR0%211'5y8%511%311p051&Q<v?r7r6r5r4r3%76654321&M&K%119%341798&QEz%221<r9%421<&QD%12?>&QG+2+R0%3221%;251&N%13:GFr8%33<1Ip031p061p0>1p0A1p0E1p0J1pT4Q=1pSDQ>1pQ<Q51pQ:Q61pT>QA1pTBQB1pQ2QA1").
Proof. intros LB sp scr M M' a n.
intros DK (S16 & SB & SC & SD & SW) S0 Ha Hn D i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
apply DK; [lia| | unfold in_errno; lia| apply D; exact Hi]. right. left. unfold hl_ceil. split; lia.
Qed.
Lemma head : ltac2:(TCodec.tc2 tcn__PmIss1 "R@&Q:vQBv?v=%43321'Q>&Cy5'R;yR0%211%5241'5y8%611%311p061'B&Q?'2'7'<%2211%411&J'Q8'0&Q7r<r;r:r9r8r7r6r5r4r3r2r1%=>Q6Q5<;:987654321&Q6rAr@r?r=%5?Q<Q;4321BA@?=<987'Q@&QA&Q1%11QA&Q9+VePD%265BA1@?%74641:p091pT2Q71pQ@Q91pQDQ?1pSLQF1r>+V`g4%;6>B21AQ2%@4?=1Q2p051p0I1pSFQ81pT<Q:1pT:Q?1pTBQ@1pT8QA1pT6QB1pSHQ@1pQ2QB1pNQH1pT0QJ1pQ>QL1pQBR21pSJR91p0R;1").
Proof.
intros LOC fx R0 M0 model0 K LB cr ois os sp r s b PRE KONT.
destruct PRE as (HH & MOK & K0 & ENT & A10 & A11 & A12 & Hspo & Hoos & Hostop & Ho8 & Hos8 & DEFO & VS & INCL & SZ & LNG & BASE & LOCb & CRED).
pose proof MOK as (Mh & Ml & Mm).
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
cbn [pa_gp pa_tp AD PmLayoutS.ADDR_S] in Rgp, Rtp.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M0 sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *. change (12288 + 2048 * 4) with 20480 in *.
assert (WRO : L5.writable RSEGS M0 ois 272) by (apply (L5C.writable_of_defined RSEGS M0 ois 272 DEFO); lia).
pose proof (PMCK.lb_hi L HI HIok LB cr M0 _ HH) as LBhi.
pose proof BASE as (RO0 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO0.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M0 _ HH (incl_refl _))).
cfeed P (PMISP.icA_conc fx R0 M0 (fun j => match j with 2%nat => sp | 33%nat => ois | 39%nat => os - ois | _ => 0 end)) ltac:(first [ PMK.sc | exact RO0 ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & B1 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & B21 & B22 & B23
& Z176 & C152 & C144 & C136 & C128 & C160 & C156 & C8 & C120 & C0 & C168 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
clear FR1 C144 C136 C128 C8 C120 C0 C168.
unfold PMSP.cfg.
set (P1 := fun a => sp - 208 <= a < sp \/ ois <= a < ois + 16 \/ ois + 120 <= a < ois + 256).
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P1 in NP. apply FRZ1; [exact Ha| | |]; intros X; apply NP; lia. }
assert (CW1 : forall a, P1 a -> PMK.cwr L LB a).
{ intros a Ha. apply (PMK.cwr_stack L LB M0 sp 20480 a STK). unfold P1 in Ha. lia. }
assert (DEC1 : forall a, {P1 a} + {~ P1 a}) by (intros a; unfold P1; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model0 fx fx1 R0 0x342e4 R1 0x7f8bc M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 AG1 CW1 DEC1).
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (L5C.stk_grows _ M0 M1 _ _ MG1 STK)).
assert (E01n : PMK.ek L LB sp 20480 [(ois, 272)] M0 M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M0 M1 P1 AG1 STK LBhi). intros a X. unfold P1 in X.
destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M0 M1 E01n); [..| exact BASE]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (LOC1 : PMST.loc_ok RSEGS AD M1 b).
{ apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M0 M1 E01n b); [|exact LOCb].
intros iv a Hin Ha. cbn [pa_loc_foot AD PmLayoutS.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
assert (STKl1 : L5C.stk (hl_sptop L) M1 (sp - 80) (PMSP.pm_scr 2)).
{ apply (PMK.stk_call L M1 sp 20480 (sp - 80) (PMSP.pm_scr 2) STK1); unfold PMSP.pm_scr; lia. }
unfold PMS.locale_ctor_spec, PMSP.locale_ctor_spec in LOC. cbn [pa_locale_ctor AD PmLayoutS.ADDR_S] in LOC.
apply (LOC fx1 R1 M1 model0 K LB cr (ois + 168) (sp - 80) 213868 b HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [split; [lia| reflexivity]|]. split; [exact B2|].
cbn [pa_gp pa_tp AD PmLayoutS.ADDR_S]. split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl1. }
{ rewrite L5K.rl10. exact B10. } { lia. } { lia. } { lia. }
{ apply (L5.defined_grows M0 M1 _ _ MG1). apply (L5.defined_sub M0 ois 272); [exact DEFO| lia| lia]. }
{ exact BASE1. } { exact LOC1. }
intros fx2 R2 M2 RP2 C168 LOC2 HP2 HH2.
set (W2 := (ois + 168, 8) :: (if b then [] else PMSP.loc_W AD)) in HP2.
assert (AG2 : forall a, sp - 80 <= a < 2 ^ 64 -> ~ (ois + 168 <= a < ois + 176) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N. apply (callee_ag LB (sp - 80) (PMSP.pm_scr 2) W2 M1 M2 HP2 STKl1 ltac:(unfold PMSP.pm_scr; lia) a Ha).
intros I. destruct (W1_inv (ois + 168) b a I); lia. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480).
{ apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 80) (PMSP.pm_scr 2) W2 STK1 HP2); unfold PMSP.pm_scr; lia. }
assert (E12 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M1 M2).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB sp 20480 (sp - 80) (PMSP.pm_scr 2) (PMIS.WF ois b) W2 M1 M1 M2 HP2 (incl_refl _));
[unfold PMSP.pm_scr; lia| lia| exact STK1| exact LBhi|].
intros a I. right. unfold W2 in I. destruct I as (rg & [<-|Hin] & Hr).
- unfold PMIS.WF. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia.
- unfold PMIS.WF. apply PMK.inW_next. exists rg. split; assumption. }
assert (DK12 : PMK.dk L LB sp 20480 M1 M2).
{ apply (PMK.dk_callee L LB LB sp 20480 (sp - 80) (PMSP.pm_scr 2) W2 M1 M2 HP2 (incl_refl _)); unfold PMSP.pm_scr; lia. }
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 (PMIS.WF ois b) M1 M2 E12); [..| exact BASE1];
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S]; intros a Ha; apply outside_WF; lia. }
assert (SP80 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 80)) by (rewrite (PMK.cs_of_preserved R1 R2 2 RP2 ltac:(PMK.inl)); exact B2).
assert (WR2 : L5.writable RSEGS M2 (sp - 20480) 20480) by (apply (L5C.stk_writable RSEGS _ M2 sp _ STK2)).
assert (DEFO2 : L5.defined M2 ois 272).
{ apply (defined_dk LB sp 20480 M1 M2 ois 272 DK12 STK1); [lia| lia| lia|]. apply (L5.defined_grows M0 M1 _ _ MG1). exact DEFO. }
assert (WRO2 : L5.writable RSEGS M2 ois 272) by (apply (L5C.writable_of_defined RSEGS M2 ois 272 DEFO2); lia).
pose proof BASE2 as (RO2 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO2.
cfeed P (PMISP.icB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => ois | 39%nat => os - ois | _ => 0 end)) ltac:(first [ PMK.sc | exact RO2 ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & D1 & D2 & D8 & D9 & D10 & D11 & D12 & D19 & D20 & D21 & D23
& E16 & T136 & T128 & T120 & T112 & T104 & T96 & T88 & E120 & E0 & F266 & F265 & F264 & F256 & F267)); PMK.pvz_clrT.
clear FR3 F266 F265 F264 F256 F267 E16.
set (P3 := fun a => sp - 144 <= a < sp - 80 \/ ois <= a < ois + 8 \/ ois + 16 <= a < ois + 24 \/ ois + 120 <= a < ois + 128 \/ ois + 256 <= a < ois + 268).
assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P3 in NP. apply FRZ3; [exact Ha| | | | |]; intros X; apply NP; lia. }
assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
{ intros a Ha. apply (PMK.cwr_stack L LB M2 sp 20480 a STK2). unfold P3 in Ha. lia. }
assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model0 fx2 fx3 R2 0x3436c R3 0x7f8bc M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 AG3 CW3 DEC3).
intros HH3.
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (L5C.stk_grows _ M2 M3 _ _ MG3 STK2)).
assert (E23n : PMK.ek L LB sp 20480 [(ois, 272)] M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M2 M3 P3 AG3 STK2 LBhi). intros a X. unfold P3 in X.
destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (E23 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M2 M3).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 (PMIS.WF ois b) [(ois, 272)] M2 M3 E23n (incl_refl _)); [intros x Hx; exact Hx|].
apply outside_WF_ois. }
assert (BASE3 : PMST.base_ok RSEGS AD M3).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M2 M3 E23n); [..| exact BASE2]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (LOC3 : PMST.loc_ok RSEGS AD M3 true).
{ apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M2 M3 E23n true); [|exact LOC2].
intros iv a Hin Ha. cbn [pa_loc_foot AD PmLayoutS.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
assert (STKl2 : L5C.stk (hl_sptop L) M3 (sp - 144) (PMSP.pm_scr 2)).
{ apply (PMK.stk_call L M3 sp 20480 (sp - 144) (PMSP.pm_scr 2) STK3); unfold PMSP.pm_scr; lia. }
apply (LOC fx3 R3 M3 model0 K LB cr (ois + 24) (sp - 144) 218132 true HH3 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact D1|]. split; [split; [lia| reflexivity]|]. split; [exact D2|].
cbn [pa_gp pa_tp AD PmLayoutS.ADDR_S].
split; [rewrite (KS3 3%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 3 RP2 ltac:(PMK.inl)); rewrite (KS1 3%nat) by PMK.inl; exact Rgp|].
split; [rewrite (KS3 4%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 4 RP2 ltac:(PMK.inl)); rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl2. }
{ rewrite L5K.rl10. exact D10. } { lia. } { lia. } { lia. }
{ apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 ois 272); [exact DEFO2| lia| lia]. }
{ exact BASE3. } { exact LOC3. }
intros fx4 R4 M4 RP4 C24 LOC4 HP4 HH4. change ((ois + 24, 8) :: (if true then [] else PMSP.loc_W AD)) with [(ois + 24, 8)] in HP4.
assert (AG4 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (ois + 24 <= a < ois + 32) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
{ intros a Ha N. apply (callee_ag LB (sp - 144) (PMSP.pm_scr 2) [(ois + 24, 8)] M3 M4 HP4 STKl2 ltac:(unfold PMSP.pm_scr; lia) a Ha).
intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (STK4 : L5C.stk (hl_sptop L) M4 sp 20480).
{ apply (PMK.stk_after RSEGS L KL LB M3 M4 sp 20480 (sp - 144) (PMSP.pm_scr 2) [(ois + 24, 8)] STK3 HP4); unfold PMSP.pm_scr; lia. }
assert (E34 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M3 M4).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB sp 20480 (sp - 144) (PMSP.pm_scr 2) (PMIS.WF ois b) [(ois + 24, 8)] M3 M3 M4 HP4 (incl_refl _));
[unfold PMSP.pm_scr; lia| lia| exact STK3| exact LBhi|].
intros a (rg & [<-|[]] & Hr). right. unfold PMIS.WF. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (DK34 : PMK.dk L LB sp 20480 M3 M4).
{ apply (PMK.dk_callee L LB LB sp 20480 (sp - 144) (PMSP.pm_scr 2) [(ois + 24, 8)] M3 M4 HP4 (incl_refl _)); unfold PMSP.pm_scr; lia. }
assert (E01 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M0 M1).
{ apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 (PMIS.WF ois b) [(ois, 272)] M0 M1 E01n (incl_refl _)); [intros x Hx; exact Hx|].
apply outside_WF_ois. }
assert (E04 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M0 M4).
{ apply (PMK.ek_trans L LB sp 20480 _ M0 M1 M4 E01). apply (PMK.ek_trans L LB sp 20480 _ M1 M2 M4 E12).
apply (PMK.ek_trans L LB sp 20480 _ M2 M3 M4 E23 E34). }
assert (DK04 : PMK.dk L LB sp 20480 M0 M4).
{ apply (PMK.dk_trans L LB sp 20480 M0 M1 M4); [apply PMK.dk_grows; exact MG1|].
apply (PMK.dk_trans L LB sp 20480 M1 M2 M4 DK12). apply (PMK.dk_trans L LB sp 20480 M2 M3 M4); [apply PMK.dk_grows; exact MG3| exact DK34]. }
assert (AG14 : forall a, sp - 80 <= a < 2 ^ 64 -> ~ (ois + 168 <= a < ois + 176) -> ~ (sp - 144 <= a < sp - 80) -> ~ (ois <= a < ois + 8)
-> ~ (ois + 16 <= a < ois + 32) -> ~ (ois + 120 <= a < ois + 128) -> ~ (ois + 256 <= a < ois + 268) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4 N5 N6. rewrite (AG4 a) by lia. rewrite (AG3 a) by (unfold P3; lia). apply AG2; lia. }
assert (AG24 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (sp - 144 <= a < sp - 80) -> ~ (ois <= a < ois + 8)
-> ~ (ois + 16 <= a < ois + 32) -> ~ (ois + 120 <= a < ois + 128) -> ~ (ois + 256 <= a < ois + 268) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N2 N3 N4 N5 N6. rewrite (AG4 a) by lia. apply AG3; [lia|]. unfold P3; lia. }
apply (KONT fx4 R4 M4 model0).
unfold PMIS.mid.
assert (V1 : 0 <= bv_unsigned (getr R0 (PMK.reg 1)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr R0 (PMK.reg 1))) as X; exact X).
split; [rewrite (PMK.cs_of_preserved R3 R4 2 RP4 ltac:(PMK.inl)); exact D2|].
split; [rewrite (PMK.cs_of_preserved R3 R4 8 RP4 ltac:(PMK.inl)); exact D8|].
split; [rewrite (PMK.cs_of_preserved R3 R4 9 RP4 ltac:(PMK.inl)); exact D9|].
split; [rewrite (PMK.cs_of_preserved R3 R4 19 RP4 ltac:(PMK.inl)); exact D19|].
split; [rewrite (PMK.cs_of_preserved R3 R4 20 RP4 ltac:(PMK.inl)); rewrite D20; f_equal; lia|].
split; [rewrite (PMK.cs_of_preserved R3 R4 21 RP4 ltac:(PMK.inl)); exact D21|].
split.
{ intros k Hk. rewrite (PMK.cs_of_preserved R3 R4 k RP4 (csk_cs k Hk)). rewrite (KS3 k (csk_icB k Hk)).
rewrite (PMK.cs_of_preserved R1 R2 k RP2 (csk_cs k Hk)). apply KS1. apply csk_icA. exact Hk. }
split.
{ unfold PMIS.saves_iss. split; [t14 AG14 S8|]. split; [t14 AG14 S16b|]. split; [t14 AG14 S24|]. split; [t14 AG14 S32|].
split; [t14 AG14 S40|]. split; [t14 AG14 S48|]. split; [t14 AG14 S56|]. split; [t14 AG14 S64| t14 AG14 S72]. }
split.
{ unfold PMIS.saves_sb. split; [t14 AG4 T88|]. split; [t14 AG4 T96|].
split; [replace os with (ois + (os - ois)) by lia; t14 AG4 T104|]. split; [t14 AG4 T112|]. split; [t14 AG4 T120|].
split; [t14 AG4 T128| t14 AG4 T136]. }
split.
{ unfold PMIS.head_cells. cbn [pa_vp_iss pa_classic_imp pa_vp_iss_ios AD PmLayoutS.ADDR_S].
split; [t14 AG4 E0|]. split; [exact C24|]. split; [t14 AG4 E120|].
split; [t14 AG14 C152|]. split; [t14 AG14 C156|]. split; [t14 AG14 C160|].
split; [cbn [pa_classic_imp AD PmLayoutS.ADDR_S] in C168; t14 AG24 C168| t14 AG14 Z176]. }
split; [apply (defined_dk LB sp 20480 M0 M4 ois 272 DK04 STK); [lia|lia|lia|exact DEFO]|].
split.
{ apply (PMFR.vstr_keep RSEGS L KL LB sp 20480 (PMIS.WF ois b) M0 M4 E04 STK ltac:(lia) BR); [| lia| lia| | exact INCL| exact VS].
- intros a I. destruct (WF_inv ois b a I); [left; lia| right; pose proof (ly_img_lo L LY); pose proof (ly_img_hi L LY); lia].
- intros i Hi I. destruct (WF_inv ois b i I); lia. }
split; [exact STK4|].
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 (PMIS.WF ois b) M3 M4 E34); [..| exact BASE3];
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S]; intros a Ha; apply outside_WF; lia. }
split; [exact LOC4|].
split; [exact HH4|]. split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|].
split; [exact E04| exact DK04].
Qed.
End Stage.
End PMIS1.
