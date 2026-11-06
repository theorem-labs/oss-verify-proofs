(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmFrame PmKitS PmCertKitS PmCertKitG L5KnA PmReadSP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmReadS () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmReadS.PMRD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmReadSP.PMRDP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1cons"; "1fst"; "1list"; "1nat"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0HI"]; ["0KS"; "0L"; "0LB"; "0LBc"; "0M"; "0M'"; "0P"; "4blocks_apart"; "4hl_img_hi"; "4hl_img_lo"; "4hl_sptop"; "5hpres"; "5stk"; "6defined"; "6range"; "7CSR"]; ["8KS_rcA"; "8KS_rcB"; "8KS_rcC"; "8KS_rcD"; "8KS_rcE"; "9locale_ctor_spec"; "9opnew_spec"; "9reader_ctor_spec"; ":cs_all"; ":dk"; ":ek"; ":inW"; "0SCFG_P"; ";eqb"; "<In"; "<existsb"]; ["<forallb"; "=add"; "=le"; "=lt"; "=pow"; "=sub"; "0W"; "0W'"; "0a"; "0b"; "0k"; "0n"; "0scr"; "0scr'"; "0sp"; "0sp'"]; [">Z_to_bv"; ">bv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMRD.
Import PMS.
Definition CSR : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma CSR_in : ltac2:(TCodec.tc2 tcn__PmReadS "I'4'5%211';'1&Q@&Q?&Q=r1%211r2%53:21qSF;1&O%93=21(9%=3<21&Q>%13A:5r4%33C:1p031pSFE1p071pQ2F1").
Proof. intros KS.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma csr_rcA : ltac2:(TCodec.tc2 tcn__PmReadS ":'5&Q>r1&O%33421r2&Q0%63721p041pSF91"). Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcB : ltac2:(TCodec.tc2 tcn__PmReadS ":'5&Q>r1&O%33421r2&Q1%63721p041pSF91"). Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcC : ltac2:(TCodec.tc2 tcn__PmReadS ":'5&Q>r1&O%33421r2&Q2%63721p041pSF91"). Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcD : ltac2:(TCodec.tc2 tcn__PmReadS ":'5&Q>r1&O%33421r2&Q3%63721p041pSF91"). Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcE : ltac2:(TCodec.tc2 tcn__PmReadS ":'5&Q>r1&O%33421r2&Q4%63721p041pSF91"). Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_cs : ltac2:(TCodec.tc2 tcn__PmReadS ":'5&Q>r1&O%33421r2&Q8%63721p041pSF91"). Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Ltac t14 AG C := lazymatch type of C with
| L5.u64_at _ ?Ms _ _ => apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
| L5.u32_at _ ?Ms _ _ => apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
| L5.u8_at _ ?Ms _ _ => apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
| L5.defined ?Ms _ _ => apply (L5C.defined_agree Ms); [intros i Hi; apply AG; lia | first [exact C | PMK.gmem]]
| L5KA.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
| PM.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
end.
Ltac gx AG :=
lazymatch goal with
| |- L5.u64_at ?sg ?M2 ?a ?v => match goal with H : L5.u64_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
(first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
| |- L5.u32_at ?sg ?M2 ?a ?v => match goal with H : L5.u32_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
(first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
| |- L5.u8_at ?sg ?M2 ?a ?v => match goal with H : L5.u8_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
(first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
apply (L5C.u8_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
end.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma callee_ag : ltac2:(TCodec.tc2 tcn__PmReadS "R1'4'7'>%2211%411&N%611'R1yR0%211'6y8%511%311p051&KvAr6r5r4r3r2r1%877654321&L&J%11:%3417:9&QBz%221=':r9%521;&QC&QD+2+R0%3221%52A1%9271&<&Q;r8%221G%411';r7&R0%12Q9M%311%812%63Q721p081p0>1pSBQE1p0J1p0N1p0Q31pQ<Q=1pQ:Q>1pS@QG1pSLQL1pT0QM1pQ8QL1").
Proof. intros LBc sp' scr' W' M M'.
intros HP STK S0 a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
apply (PMKP.kept_stack RSEGS L KL LBc M sp' scr' W' a STK S0 Ha). apply PMFR.outside_of_not_inW. exact N.
Qed.
Lemma defined_dk : ltac2:(TCodec.tc2 tcn__PmReadS "QF'4'7'>%2211%411'R1yR0%211'6y8%511%311p051&Q9vAr7r6r5r4r3%76654321&L&J%119%341798&QBz%221<r9%421<&QA%12?>&QD+2+R0%3221%;251&M%13:GFr8%33<1Ip031p061p0>1p0A1p0E1p0J1pSHQ=1pSBQ>1pQ<Q51pQ:Q61pSJQA1pSNQB1pQ6QA1").
Proof. intros LB sp scr M M' a n.
intros DK (S16 & SB & SC & SD & SW) S0 Ha Hn D i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
apply DK; [lia| | unfold in_errno; lia| apply D; exact Hi]. right. left. unfold hl_ceil. split; lia.
Qed.
Lemma ek_piece_blk : ltac2:(TCodec.tc2 tcn__PmReadS "SI'4'7'>%2211%411&N%611'R1yR0%211'6y8%511%311pT651!p0>1':&QBzr1%3221&QC&QD+2+R0%3221%5271%;271&<r5r2%211%411';r7&R0r3%22N1%411r8%113%83M31p0:1p0@1pSBQ;1&L&JvA%211r6r9%64321<&Q>r<%23QDQ31&QA&3%13QHQHK&8%13QJQJM%5231&QE+XPPP0%22?1%Q?241p0;1pSDR01&Gr4%23Q81@'=%@2FQ:&I%11J%QI231&H%11M%QL21L%8241%H2Q=N%QO21Ar:%11QOr@r?%H221%R521QH%R22QI4%R8221&Q;r>%221QM%R;2;QN%Q62<Q;%R92R01%R?231%J251%K291p0@1pSBS21&Q:r=r;%37QHDC=2QB1p051p0I1p0L1p0Q61p0Q:1p0QJ1p0R21pSHS>1p2S?1pQ>S21pQ<S51pQ:S61pS>S?1pSJSD1pSNSE1pQ6SD1").
Proof. intros LB sp scr W M M' P B n.
intros E STK HLB FAP FBH FBC FP a KA. pose proof KA as (Ha & CA & NE & OW). apply E; [exact Ha|]. intros Pa.
destruct (FP a Pa) as [S|[I|Bk]].
- pose proof STK as (_ & Hc & _ & Hw & _). pose proof (PMK.kl_img RSEGS L KL) as KI.
destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]]; [pose proof (HLB b Hb); unfold hl_ceil in *; lia| exact (S2 S)| lia].
- exact (PMK.inW_not_outside W a I OW).
- exact (L5C.kept_not_fresh L LB sp scr W a B n KA FAP FBH FBC HLB Bk).
Qed.
Lemma apart_tl : ltac2:(TCodec.tc2 tcn__PmReadS "D'>'7%1222'4%112&Gr4r3(2r2r1%33921%73651r5%93185p031pQ6<1pSD?1pSHB1p2C1").
Proof. intros B n b LB. intros H x Hx. apply H. right. exact Hx. Qed.
Theorem reader_ctor_ok : ltac2:(TCodec.tc2 tcn__PmReadS ";&Q5vQ<vAv?%43321&Q6%13543&Q7%13765p031p061").
Proof.
intros LOC OPNEW. unfold PMS.reader_ctor_spec, PMSP.reader_ctor_spec.
intros fx R0 M0 model0 K LB cr sp r fb oo oa str sm HH MOK K0 ENT FRM A10 A11 A12 A13 Hfo Hop Hoo8 DEFO OVP OMI ODP ISS BASE LOC0 CRED KONT.
unfold PMSP.o_p, PMSP.o_is, PMSP.frame_ok in *. cbn [pa_off_p pa_off_is pa_frame pa_vp_opts AD PmLayoutS.ADDR_S] in *.
set (op := fb + 40) in *. assert (Eis : fb + 440 = op + 400) by (unfold op; lia). rewrite Eis in *.
destruct FRM as (Hspfb & Hfbtop & Hfb16).
pose proof MOK as (Mh & Ml & Mm).
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
rewrite L5K.rl12 in A12. cbn [pa_gp pa_tp AD PmLayoutS.ADDR_S] in Rgp, Rtp.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M0 sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *. change (12288 + 2048 * 6) with 24576 in *.
assert (Hop8 : op mod 8 = 0) by (unfold op; lia).
assert (WRO : L5.writable RSEGS M0 op 384) by (apply (L5C.writable_of_defined RSEGS M0 op 384 DEFO); lia).
pose proof (PMCK.lb_hi L HI HIok LB cr M0 _ HH) as LBhi.
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M0 _ HH (incl_refl _))).
pose proof BASE as (RO0 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO0.
assert (CEIL : hl_ceil L <= sp - 24576) by (unfold hl_ceil; lia).
destruct ISS as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
destruct IOS as (_ & _ & _ & I160 & _). cbn [pa_vp_iss AD PmLayoutS.ADDR_S] in I0.
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
cfeed P (PMRDP.rcA_conc fx R0 M0 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | _ => 0 end)) ltac:(first [ PMK.sc | exact RO0 ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10' & A18
& Z168 & C144 & C136 & C128 & C120 & C152 & C148 & C40 & C32 & C160 & C112 & S136 & S128 & S120 & S112 & S104 & S96 & S88
& C16 & C12 & (C8 & C9) & C0 & C20 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
clear FR1 C136 C128 C120 C40 C32 C160 C112.
unfold PMSP.cfg.
set (P1 := fun a => sp - 160 <= a < sp \/ op <= a < op + 24 \/ op + 32 <= a < op + 48 \/ op + 112 <= a < op + 248).
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P1 in NP. apply FRZ1; [exact Ha| | | |]; intros X; apply NP; lia. }
assert (CW1 : forall a, P1 a -> PMK.cwr L LB a).
{ intros a Ha. apply (PMK.cwr_stack L LB M0 sp 24576 a STK). unfold P1 in Ha. lia. }
assert (DEC1 : forall a, {P1 a} + {~ P1 a}) by (intros a; unfold P1; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model0 fx fx1 R0 0x355f8 R1 0x7f8bc M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 AG1 CW1 DEC1).
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 24576) by (apply (L5C.stk_grows _ M0 M1 _ _ MG1 STK)).
assert (EK01 : PMK.ek L LB sp 24576 [(op, 384)] M0 M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 384)] M0 M1 P1 AG1 STK LBhi). intros a X. unfold P1 in X.
destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
assert (BASE1 : PMST.base_ok RSEGS AD M1).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M0 M1 EK01); [..| exact BASE]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (LOC1 : PMST.loc_ok RSEGS AD M1 true).
{ apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M0 M1 EK01 true); [|exact LOC0].
intros iv a Hin Ha. cbn [pa_loc_foot AD PmLayoutS.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
unfold PMS.locale_ctor_spec, PMSP.locale_ctor_spec in LOC. cbn [pa_locale_ctor AD PmLayoutS.ADDR_S] in LOC.
assert (STKl1 : L5C.stk (hl_sptop L) M1 (sp - 144) (PMSP.pm_scr 2)).
{ apply (PMK.stk_call L M1 sp 24576 (sp - 144) (PMSP.pm_scr 2) STK1); unfold PMSP.pm_scr; lia. }
apply (LOC fx1 R1 M1 model0 K LB cr (op + 160) (sp - 144) 219188 true HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
cbn [pa_gp pa_tp AD PmLayoutS.ADDR_S]. split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl1. }
{ rewrite L5K.rl10. exact A10'. } { lia. } { lia. } { lia. }
{ apply (L5.defined_grows M0 M1 _ _ MG1). apply (L5.defined_sub M0 op 384); [exact DEFO| lia| lia]. }
{ exact BASE1. } { exact LOC1. }
intros fx2 R2 M2 RP2 L160 LOC2 HP2 HH2. change ((op + 160, 8) :: (if true then [] else PMSP.loc_W AD)) with [(op + 160, 8)] in HP2.
assert (AG2 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (op + 160 <= a < op + 168) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N. apply (callee_ag LB (sp - 144) (PMSP.pm_scr 2) [(op + 160, 8)] M1 M2 HP2 STKl1 ltac:(unfold PMSP.pm_scr; lia) a Ha).
intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 24576).
{ apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 24576 (sp - 144) (PMSP.pm_scr 2) [(op + 160, 8)] STK1 HP2); unfold PMSP.pm_scr; lia. }
assert (EK12 : PMK.ek L LB sp 24576 [(op, 384)] M1 M2).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB sp 24576 (sp - 144) (PMSP.pm_scr 2) [(op, 384)] [(op + 160, 8)] M1 M1 M2 HP2 (incl_refl _));
[unfold PMSP.pm_scr; lia| lia| exact STK1| exact LBhi|].
intros a (rg & [<-|[]] & Hr). right. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (DK12 : PMK.dk L LB sp 24576 M1 M2).
{ apply (PMK.dk_callee L LB LB sp 24576 (sp - 144) (PMSP.pm_scr 2) [(op + 160, 8)] M1 M2 HP2 (incl_refl _)); unfold PMSP.pm_scr; lia. }
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M1 M2 EK12); [..| exact BASE1]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (LOC2' : PMST.loc_ok RSEGS AD M2 true) by exact LOC2.
assert (DEFO2 : L5.defined M2 op 384).
{ apply (defined_dk LB sp 24576 M1 M2 op 384 DK12 STK1); [lia| lia| lia|]. apply (L5.defined_grows M0 M1 _ _ MG1). exact DEFO. }
assert (WRO2 : L5.writable RSEGS M2 op 384) by (apply (L5C.writable_of_defined RSEGS M2 op 384 DEFO2); lia).
pose proof (L5C.stk_writable RSEGS _ M2 sp _ STK2) as WR2.
pose proof BASE2 as (RO2 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO2.
cfeed P (PMRDP.rcB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => op | _ => 0 end)) ltac:(first [ PMK.sc | exact RO2 ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & B1 & B10 & B11 & B12 & D48 & D32 & D112 & D256 & D248)); PMK.pvz_clrT.
clear FR3 B11 B12 D48 D256 D248.
set (P3 := fun a => op + 32 <= a < op + 40 \/ op + 48 <= a < op + 56 \/ op + 112 <= a < op + 120 \/ op + 248 <= a < op + 260).
assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P3 in NP. apply FRZ3; [exact Ha| | | |]; intros X; apply NP; lia. }
assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
{ intros a Ha. apply (PMK.cwr_stack L LB M2 sp 24576 a STK2). unfold P3 in Ha. lia. }
assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model0 fx2 fx3 R2 0x35834 R3 0x7f8bc M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 AG3 CW3 DEC3).
intros HH3.
assert (STK3 : L5C.stk (hl_sptop L) M3 sp 24576) by (apply (L5C.stk_grows _ M2 M3 _ _ MG3 STK2)).
assert (EK23 : PMK.ek L LB sp 24576 [(op, 384)] M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 384)] M2 M3 P3 AG3 STK2 LBhi). intros a X. unfold P3 in X. right; apply PMK.inW_here; lia. }
assert (BASE3 : PMST.base_ok RSEGS AD M3).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M2 M3 EK23); [..| exact BASE2]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (LOC3 : PMST.loc_ok RSEGS AD M3 true).
{ apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M2 M3 EK23 true); [|exact LOC2].
intros iv a Hin Ha. cbn [pa_loc_foot AD PmLayoutS.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
assert (STKl2 : L5C.stk (hl_sptop L) M3 (sp - 144) (PMSP.pm_scr 2)).
{ apply (PMK.stk_call L M3 sp 24576 (sp - 144) (PMSP.pm_scr 2) STK3); unfold PMSP.pm_scr; lia. }
assert (R3sp : getr R3 (PMK.reg 2) = Z_to_bv 64 (sp - 144)).
{ rewrite (KS3 2%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R1 R2 2 RP2 ltac:(PMK.inl)). exact A2. }
apply (LOC fx3 R3 M3 model0 K LB cr (op + 56) (sp - 144) 219248 true HH3 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [split; [lia| reflexivity]|]. split; [exact R3sp|].
cbn [pa_gp pa_tp AD PmLayoutS.ADDR_S].
split; [rewrite (KS3 3%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 3 RP2 ltac:(PMK.inl)); rewrite (KS1 3%nat) by PMK.inl; exact Rgp|].
split; [rewrite (KS3 4%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 4 RP2 ltac:(PMK.inl)); rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl2. }
{ rewrite L5K.rl10. exact B10. } { lia. } { lia. } { lia. }
{ apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 op 384); [exact DEFO2| lia| lia]. }
{ exact BASE3. } { exact LOC3. }
intros fx4 R4 M4 RP4 L56 LOC4 HP4 HH4. change ((op + 56, 8) :: (if true then [] else PMSP.loc_W AD)) with [(op + 56, 8)] in HP4.
assert (AG4 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (op + 56 <= a < op + 64) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
{ intros a Ha N. apply (callee_ag LB (sp - 144) (PMSP.pm_scr 2) [(op + 56, 8)] M3 M4 HP4 STKl2 ltac:(unfold PMSP.pm_scr; lia) a Ha).
intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (STK4 : L5C.stk (hl_sptop L) M4 sp 24576).
{ apply (PMK.stk_after RSEGS L KL LB M3 M4 sp 24576 (sp - 144) (PMSP.pm_scr 2) [(op + 56, 8)] STK3 HP4); unfold PMSP.pm_scr; lia. }
assert (EK34 : PMK.ek L LB sp 24576 [(op, 384)] M3 M4).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB sp 24576 (sp - 144) (PMSP.pm_scr 2) [(op, 384)] [(op + 56, 8)] M3 M3 M4 HP4 (incl_refl _));
[unfold PMSP.pm_scr; lia| lia| exact STK3| exact LBhi|].
intros a (rg & [<-|[]] & Hr). right. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (DK34 : PMK.dk L LB sp 24576 M3 M4).
{ apply (PMK.dk_callee L LB LB sp 24576 (sp - 144) (PMSP.pm_scr 2) [(op + 56, 8)] M3 M4 HP4 (incl_refl _)); unfold PMSP.pm_scr; lia. }
assert (BASE4 : PMST.base_ok RSEGS AD M4).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M3 M4 EK34); [..| exact BASE3]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (DEFO4 : L5.defined M4 op 384).
{ apply (defined_dk LB sp 24576 M3 M4 op 384 DK34 STK3); [lia| lia| lia|]. apply (L5.defined_grows M2 M3 _ _ MG3). exact DEFO2. }
assert (WRO4 : L5.writable RSEGS M4 op 384) by (apply (L5C.writable_of_defined RSEGS M4 op 384 DEFO4); lia).
pose proof (L5C.stk_writable RSEGS _ M4 sp _ STK4) as WR4.
pose proof BASE4 as (RO4 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO4.
assert (AG14 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (op + 160 <= a < op + 168) -> ~ P3 a -> ~ (op + 56 <= a < op + 64) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N1 N3 N4. rewrite (AG4 a Ha N4). rewrite (AG3 a ltac:(lia) N3). apply AG2; assumption. }
assert (AG14r : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (op + 32 <= a < op + 64) -> ~ (op + 112 <= a < op + 120) -> ~ (op + 160 <= a < op + 168)
-> ~ (op + 248 <= a < op + 260) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4. apply AG14; [exact Ha| exact N3| unfold P3; lia| lia]. }
assert (AG04 : forall a, sp <= a < 2 ^ 64 -> ~ (op <= a < op + 384) -> M4 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
{ intros a Ha N. rewrite (AG14r a) by lia. apply AG1; [lia| unfold P1; lia]. }
assert (I0' : L5.u64_at RSEGS M4 (op + 400) 731800) by t14 AG04 I0.
assert (I160' : L5.u64_at RSEGS M4 (op + 560) (op + 416)).
{ apply (L5C.u64_at_agree RSEGS M0); [intros i Hi; apply AG04; lia| lia| lia|]. PMK.gmem. }
assert (R4sp : getr R4 (PMK.reg 2) = Z_to_bv 64 (sp - 144)) by (rewrite (PMK.cs_of_preserved R3 R4 2 RP4 ltac:(PMK.inl)); exact R3sp).
cfeed P (PMRDP.rcC_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => op | _ => 0 end)) ltac:(first [ PMK.sc | exact RO4 | gx AG14r ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG5 & FR5 & FRZ5 & MS5 & KS5 & E1 & E2 & E9 & E10 & E11 & F312 & F304 & F296 & F288 & F280 & F272 & F264 & F48 & Z64)); PMK.pvz_clrT.
clear FR5 E11 F304 F288.
set (P5 := fun a => op + 48 <= a < op + 56 \/ op + 64 <= a < op + 112 \/ op + 264 <= a < op + 320).
assert (AG5 : forall a, 0 <= a < 2 ^ 64 -> ~ P5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P5 in NP. apply FRZ5; [exact Ha| | |]; intros X; apply NP; lia. }
assert (CW5 : forall a, P5 a -> PMK.cwr L LB a).
{ intros a Ha. apply (PMK.cwr_stack L LB M4 sp 24576 a STK4). unfold P5 in Ha. lia. }
assert (DEC5 : forall a, {P5 a} + {~ P5 a}) by (intros a; unfold P5; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M4 model0 fx4 fx5 R4 0x35870 R5 0xae098 M5 P5 K HH4 Mh Ml ltac:(lia) MS5 MG5 AG5 CW5 DEC5).
intros HH5.
assert (STK5 : L5C.stk (hl_sptop L) M5 sp 24576) by (apply (L5C.stk_grows _ M4 M5 _ _ MG5 STK4)).
assert (EK45 : PMK.ek L LB sp 24576 [(op, 384)] M4 M5).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 384)] M4 M5 P5 AG5 STK4 LBhi). intros a X. unfold P5 in X. right; apply PMK.inW_here; lia. }
assert (SCn : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
assert (STKn1 : L5C.stk (hl_sptop L) M5 (sp - 112) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M5 sp 24576 (sp - 112) PMSP.OPNEW_SCR STK5); unfold PMSP.OPNEW_SCR; lia. }
unfold PMS.opnew_spec, PMSP.opnew_spec in OPNEW. cbn [pa_opnew pa_tp AD PmLayoutS.ADDR_S] in OPNEW.
assert (R5tp : getr R5 (PMK.reg 4) = Z_to_bv 64 0xc7c60).
{ rewrite (KS5 4%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R3 R4 4 RP4 ltac:(PMK.inl)). rewrite (KS3 4%nat) by PMK.inl.
rewrite (PMK.cs_of_preserved R1 R2 4 RP2 ltac:(PMK.inl)). rewrite (KS1 4%nat) by PMK.inl. exact Rtp. }
destruct CRED as (CR1 & CR2). unfold PM.credit_add, PM.cost1, PM.CHUNK in CR1, CR2. cbn [fst snd] in CR1, CR2.
apply (OPNEW fx5 R5 M5 model0 K LB cr 16384 (sp - 112) 219068 HH5 MOK K0).
{ rewrite L5K.rl10. exact E10. } { lia. } { unfold credit_ok. lia. }
{ rewrite L5K.rl1. exact E1. } { split; [lia| reflexivity]. } { rewrite L5K.rl2. exact E2. }
{ rewrite L5K.rl4. exact R5tp. } { exact STKn1. }
intros fx6 R6 M6 model6 qc A10q RP6 FRESHq HP6 MB6 HH6. rewrite L5K.rl10 in A10q.
destruct (L5C.fresh_block_bounds L LB M6 qc 16384 FRESHq) as (FQ0 & FQH & FQ16 & _ & FQC).
destruct FRESHq as (_ & FAPq & FDEFq).
pose proof (PMFR.model_ok_but_vm model0 model6 MOK MB6) as MOK6. pose proof MOK6 as (Mh6 & Ml6 & Mm6).
assert (AG6 : forall a, sp - 112 <= a < 2 ^ 64 -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
{ intros a Ha. apply (L5C.hpres_kept L LB (sp - 112) PMSP.OPNEW_SCR [] M5 M6 a HP6).
apply (PMKP.kept_stack RSEGS L KL LB M5 (sp - 112) PMSP.OPNEW_SCR [] a STKn1 SCn Ha). apply L5C.outside_nil. }
assert (STK6 : L5C.stk (hl_sptop L) M6 sp 24576).
{ apply (PMK.stk_after RSEGS L KL LB M5 M6 sp 24576 (sp - 112) PMSP.OPNEW_SCR [] STK5 HP6); unfold PMSP.OPNEW_SCR; lia. }
assert (EK56 : PMK.ek L LB sp 24576 [(op, 384)] M5 M6).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB sp 24576 (sp - 112) PMSP.OPNEW_SCR [(op, 384)] [] M5 M5 M6 HP6 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia| exact STK5| exact LBhi|].
intros a X. destruct (PMFR.inW_nil a X). }
assert (DK56 : PMK.dk L LB sp 24576 M5 M6).
{ apply (PMK.dk_callee L LB LB sp 24576 (sp - 112) PMSP.OPNEW_SCR [] M5 M6 HP6 (incl_refl _)); unfold PMSP.OPNEW_SCR; lia. }
set (LB6 := (qc, 16384) :: LB) in *.
assert (BASE5 : PMST.base_ok RSEGS AD M5).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M4 M5 EK45); [..| exact BASE4]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
assert (BASE6 : PMST.base_ok RSEGS AD M6).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M5 M6 EK56); [..| exact BASE5]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S];
intros a Ha; PMKP.outW. }
pose proof BASE6 as (RO6 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO6.
assert (AG16 : forall a, sp - 112 <= a < 2 ^ 64 -> ~ (op + 32 <= a < op + 120) -> ~ (op + 160 <= a < op + 168) -> ~ (op + 248 <= a < op + 320) ->
M6 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3. rewrite (AG6 a) by lia. rewrite (AG5 a) by (unfold P5; lia). apply AG14r; lia. }
assert (AG06 : forall a, sp <= a < 2 ^ 64 -> ~ (op <= a < op + 384) -> M6 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
{ intros a Ha N. rewrite (AG6 a) by lia. rewrite (AG5 a) by (unfold P5; lia). apply AG04; lia. }
assert (DK46 : PMK.dk L LB sp 24576 M4 M6) by (apply (PMK.dk_trans L LB sp 24576 M4 M5 M6); [apply PMK.dk_grows; exact MG5| exact DK56]).
assert (DEFO6 : L5.defined M6 op 384) by (apply (defined_dk LB sp 24576 M4 M6 op 384 DK46 STK4); [lia| lia| lia| exact DEFO4]).
assert (WRO6 : L5.writable RSEGS M6 op 384) by (apply (L5C.writable_of_defined RSEGS M6 op 384 DEFO6); lia).
pose proof (L5C.stk_writable RSEGS _ M6 sp _ STK6) as WR6.
unfold PM.MAX_ITEMS, PM.MAX_DEPTH in OMI, ODP.
cfeed P (PMRDP.rcD_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | 35%nat => qc | _ => 0 end)) ltac:(first [ PMK.sc | exact RO6 | gx AG16 | gx AG06 ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx7 & R7 & M7 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG7 & FR7 & FRZ7 & MS7 & KS7 & G1 & G2 & G8 & G10 & G11 & G18 & G19 & H96 & H88 & H48 & Z336 & H328 & H320 & H304 & H288)); PMK.pvz_clrT.
clear FR7 G11 H48.
set (P7 := fun a => sp - 96 <= a < sp - 80 \/ sp - 48 <= a < sp - 40 \/ op + 288 <= a < op + 296 \/ op + 304 <= a < op + 312 \/ op + 320 <= a < op + 384).
assert (AG7 : forall a, 0 <= a < 2 ^ 64 -> ~ P7 a -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P7 in NP. apply FRZ7; [exact Ha| | | | |]; intros X; apply NP; lia. }
assert (CW7 : forall a, P7 a -> PMK.cwr L LB6 a).
{ intros a Ha. apply (PMK.cwr_stack L LB6 M6 sp 24576 a STK6). unfold P7 in Ha. lia. }
assert (DEC7 : forall a, {P7 a} + {~ P7 a}) by (intros a; unfold P7; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB6 (debit L cr 16384) M6 model6 fx6 fx7 R6 0x357bc R7 0xae098 M7 P7 K HH6 Mh6 Ml6 ltac:(lia) MS7 MG7 AG7 CW7 DEC7).
intros HH7.
assert (STK7 : L5C.stk (hl_sptop L) M7 sp 24576) by (apply (L5C.stk_grows _ M6 M7 _ _ MG7 STK6)).
assert (EK67 : PMK.ek L LB sp 24576 [(op, 384)] M6 M7).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 384)] M6 M7 P7 AG7 STK6 LBhi). intros a X. unfold P7 in X.
destruct X as [X|[X|X]]; [left; lia| left; lia| right; apply PMK.inW_here; lia]. }
assert (STKn2 : L5C.stk (hl_sptop L) M7 (sp - 96) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M7 sp 24576 (sp - 96) PMSP.OPNEW_SCR STK7); unfold PMSP.OPNEW_SCR; lia. }
assert (R7tp : getr R7 (PMK.reg 4) = Z_to_bv 64 0xc7c60).
{ rewrite (KS7 4%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R5 R6 4 RP6 ltac:(PMK.inl)). exact R5tp. }
apply (OPNEW fx7 R7 M7 model6 K LB6 (debit L cr 16384) 32 (sp - 96) 219500 HH7 MOK6 K0).
{ rewrite L5K.rl10. exact G10. } { lia. } { unfold credit_ok, debit. cbn [fst snd]. lia. }
{ rewrite L5K.rl1. exact G1. } { split; [lia| reflexivity]. } { rewrite L5K.rl2. exact G2. }
{ rewrite L5K.rl4. exact R7tp. } { exact STKn2. }
intros fx8 R8 M8 model8 bb A10bb RP8 FRESHb HP8 MB8 HH8. rewrite L5K.rl10 in A10bb.
destruct (L5C.fresh_block_bounds L LB6 M8 bb 32 FRESHb) as (FB0 & FBH & FB16 & _ & FBC).
destruct FRESHb as (_ & FAPb & FDEFb).
pose proof (PMFR.model_ok_but_vm model6 model8 MOK6 MB8) as MOK8. pose proof MOK8 as (Mh8 & Ml8 & Mm8).
assert (AG8 : forall a, sp - 96 <= a < 2 ^ 64 -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
{ intros a Ha. apply (L5C.hpres_kept L LB6 (sp - 96) PMSP.OPNEW_SCR [] M7 M8 a HP8).
apply (PMKP.kept_stack RSEGS L KL LB6 M7 (sp - 96) PMSP.OPNEW_SCR [] a STKn2 SCn Ha). apply L5C.outside_nil. }
assert (LBhi6 : forall b, In b LB6 -> fst b + snd b <= hl_ceil L) by (intros b0 [<-|Hb0]; [cbn; lia| apply LBhi; exact Hb0]).
assert (BR6 : PMFR.brange L LB6) by (intros B0 m0 [E0|Hin]; [injection E0 as <- <-; lia| apply BR; exact Hin]).
assert (AGq : L5C.agree_on M7 M8 qc 16384).
{ apply (PMFR.ag_block RSEGS L KL LB6 (sp - 96) PMSP.OPNEW_SCR [] M7 M8 (PMK.ek_of_hpres L LB6 _ _ _ M7 M8 HP8) STKn2 SCn BR6); [| left; reflexivity].
intros a X. destruct (PMFR.inW_nil a X). }
assert (STK8 : L5C.stk (hl_sptop L) M8 sp 24576).
{ apply (PMK.stk_after RSEGS L KL LB6 M7 M8 sp 24576 (sp - 96) PMSP.OPNEW_SCR [] STK7 HP8); unfold PMSP.OPNEW_SCR; lia. }
assert (INC6 : incl LB LB6) by (intros x Hx; right; exact Hx).
assert (EK78 : PMK.ek L LB sp 24576 [(op, 384)] M7 M8).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB6 sp 24576 (sp - 96) PMSP.OPNEW_SCR [(op, 384)] [] M7 M7 M8 HP8 INC6); [unfold PMSP.OPNEW_SCR; lia| lia| exact STK7| exact LBhi|].
intros a X. destruct (PMFR.inW_nil a X). }
assert (DK78 : PMK.dk L LB sp 24576 M7 M8).
{ apply (PMK.dk_callee L LB LB6 sp 24576 (sp - 96) PMSP.OPNEW_SCR [] M7 M8 HP8 INC6); unfold PMSP.OPNEW_SCR; lia. }
set (LB8 := (bb, 32) :: LB6) in *.
assert (V1 : 0 <= bv_unsigned (getr R0 (PMK.reg 1)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
assert (V8 : 0 <= bv_unsigned (getr R0 (PMK.reg 8)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
assert (V9 : 0 <= bv_unsigned (getr R0 (PMK.reg 9)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
assert (V18 : 0 <= bv_unsigned (getr R0 (PMK.reg 18)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
assert (V19 : 0 <= bv_unsigned (getr R0 (PMK.reg 19)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
change (bv_modulus 64) with (2 ^ 64) in *.
assert (AG18 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 32 <= a < op + 120) -> ~ (op + 160 <= a < op + 168) -> ~ (op + 248 <= a < op + 384) ->
~ (sp - 96 <= a < sp - 40) -> M8 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4. rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). apply AG16; lia. }
assert (Z3608 : L5.u64_at RSEGS M8 (op + 360) 0 /\ L5.u64_at RSEGS M8 (op + 368) 0 /\ L5.u64_at RSEGS M8 (op + 376) 0).
{ split; [|split]; (apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply AG8; lia| lia| lia|]; apply (PMCG.u64_of_zeros RSEGS M7); [|lia|lia];
apply (PMCG.zeros_sub M7 (op + 336) 48); [exact Z336|lia|lia]). }
destruct Z3608 as (Y360 & Y368 & Y376).
assert (DEFO8 : L5.defined M8 op 384).
{ apply (defined_dk LB sp 24576 M6 M8 op 384); [apply (PMK.dk_trans L LB sp 24576 M6 M7 M8); [apply PMK.dk_grows; exact MG7| exact DK78]| exact STK6| lia| lia| lia| exact DEFO6]. }
assert (WRO8 : L5.writable RSEGS M8 op 384) by (apply (L5C.writable_of_defined RSEGS M8 op 384 DEFO8); lia).
pose proof (L5C.stk_writable RSEGS _ M8 sp _ STK8) as WR8.
assert (BASE8 : PMST.base_ok RSEGS AD M8).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 384)] M6 M8 (PMK.ek_trans L LB sp 24576 _ M6 M7 M8 EK67 EK78)); [..| exact BASE6];
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S]; intros a Ha; PMKP.outW. }
pose proof BASE8 as (RO8 & _ & _ & _). cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in RO8.
cfeed P (PMRDP.rcE_conc fx8 R8 M8 (fun j => match j with 2%nat => sp | 33%nat => op | 36%nat => bb
| 43%nat => bv_unsigned (getr R0 (PMK.reg 1)) | 44%nat => bv_unsigned (getr R0 (PMK.reg 8)) | 45%nat => bv_unsigned (getr R0 (PMK.reg 9))
| 46%nat => bv_unsigned (getr R0 (PMK.reg 18)) | 47%nat => bv_unsigned (getr R0 (PMK.reg 19)) | _ => 0 end)) ltac:(first [ PMK.sc | exact RO8 | gx AG18 | gx AG8 | (apply (L5C.writable_of_defined RSEGS M8 bb 32); [exact FDEFb|lia|lia]) ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx9 & R9 & M9 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG9 & FR9 & FRZ9 & MS9 & KS9 & H1 & H2 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H18 & H19 & V368 & V376 & V360 & Q24 & Q16 & Q8 & Q0)); PMK.pvz_clrT.
clear FR9 H10 H11 H12 H13 H14 H15.
set (P9 := fun a => sp - 80 <= a < sp - 48 \/ op + 360 <= a < op + 384 \/ bb <= a < bb + 32).
assert (AG9 : forall a, 0 <= a < 2 ^ 64 -> ~ P9 a -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P9 in NP. apply FRZ9; [exact Ha| | |]; intros X; apply NP; lia. }
assert (CW9 : forall a, P9 a -> PMK.cwr L LB8 a).
{ intros a Ha. unfold P9 in Ha. destruct Ha as [X|[X|X]]; [apply (PMK.cwr_stack L LB8 M8 sp 24576 a STK8); lia| apply (PMK.cwr_stack L LB8 M8 sp 24576 a STK8); lia|].
apply (PMK.cwr_block L LB8 bb 32 a); [left; reflexivity| lia]. }
assert (DEC9 : forall a, {P9 a} + {~ P9 a}) by (intros a; unfold P9; repeat apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB8 (debit L (debit L cr 16384) 32) M8 model8 fx8 fx9 R8 0x3596c R9 0x3570c M9 P9 K HH8 Mh8 Ml8 ltac:(lia) MS9 MG9 AG9 CW9 DEC9).
intros HH9.
eapply (L5.cps_of_msteps RSEGS); [exact Mh8| exact Ml8| apply (PMK.ret_to RSEGS fx9 R9 M9 0x3570c (ltac:(oW' 0x3570c%Z)) r (ltac:(oF' 0x3570c%Z)) ltac:(reflexivity) (ltac:(oD' 0x3570c%Z)))|].
{ rewrite H1, Z_to_bv_bv_unsigned. exact Rra. } { exact RA1. } { exact RA2. }
assert (STK9 : L5C.stk (hl_sptop L) M9 sp 24576) by (apply (L5C.stk_grows _ M8 M9 _ _ MG9 STK8)).
assert (EK89 : PMK.ek L LB sp 24576 [(op, 384)] M8 M9).
{ apply (ek_piece_blk LB sp 24576 [(op, 384)] M8 M9 P9 bb 32 AG9 STK8 LBhi (apart_tl bb 32 _ LB FAPb) FBH FBC).
intros a X. unfold P9 in X. destruct X as [X|[X|X]]; [left; lia| right; left; apply PMK.inW_here; lia| right; right; lia]. }
assert (AG19 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 32 <= a < op + 120) -> ~ (op + 160 <= a < op + 168) -> ~ (op + 248 <= a < op + 384) ->
~ (sp - 96 <= a < sp - 40) -> M9 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4. rewrite (AG9 a) by (unfold P9; lia). apply AG18; lia. }
assert (AG29 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 32 <= a < op + 120) -> ~ (op + 248 <= a < op + 384) -> ~ (sp - 96 <= a < sp - 40) ->
M9 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). rewrite (AG6 a) by lia.
rewrite (AG5 a) by (unfold P5; lia). rewrite (AG4 a) by lia. apply AG3; [lia| unfold P3; lia]. }
assert (AG39 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 48 <= a < op + 112) -> ~ (op + 264 <= a < op + 384) -> ~ (sp - 96 <= a < sp - 40) ->
M9 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). rewrite (AG6 a) by lia.
rewrite (AG5 a) by (unfold P5; lia). apply AG4; lia. }
assert (AG49 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 48 <= a < op + 56) -> ~ (op + 64 <= a < op + 112) -> ~ (op + 264 <= a < op + 384) ->
~ (sp - 96 <= a < sp - 40) -> M9 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). rewrite (AG6 a) by lia.
apply AG5; [lia| unfold P5; lia]. }
assert (AG59 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 288 <= a < op + 296) -> ~ (op + 304 <= a < op + 312) -> ~ (op + 320 <= a < op + 384) ->
~ (sp - 96 <= a < sp - 40) -> M9 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). apply AG6; lia. }
assert (AG79 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp - 48) -> ~ (op + 360 <= a < op + 384) -> M9 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
{ intros a Ha N1 N2. rewrite (AG9 a) by (unfold P9; lia). apply AG8; lia. }
assert (EK09 : PMK.ek L LB sp 24576 [(op, 384)] M0 M9).
{ apply (PMK.ek_trans L LB sp 24576 _ M0 M1 M9 EK01). apply (PMK.ek_trans L LB sp 24576 _ M1 M2 M9 EK12).
apply (PMK.ek_trans L LB sp 24576 _ M2 M3 M9 EK23). apply (PMK.ek_trans L LB sp 24576 _ M3 M4 M9 EK34).
apply (PMK.ek_trans L LB sp 24576 _ M4 M5 M9 EK45). apply (PMK.ek_trans L LB sp 24576 _ M5 M6 M9 EK56).
apply (PMK.ek_trans L LB sp 24576 _ M6 M7 M9 EK67). apply (PMK.ek_trans L LB sp 24576 _ M7 M8 M9 EK78 EK89). }
assert (DK09 : PMK.dk L LB sp 24576 M0 M9).
{ apply (PMK.dk_trans L LB sp 24576 M0 M1 M9); [apply PMK.dk_grows; exact MG1|].
apply (PMK.dk_trans L LB sp 24576 M1 M2 M9 DK12). apply (PMK.dk_trans L LB sp 24576 M2 M3 M9); [apply PMK.dk_grows; exact MG3|].
apply (PMK.dk_trans L LB sp 24576 M3 M4 M9 DK34). apply (PMK.dk_trans L LB sp 24576 M4 M6 M9 DK46).
apply (PMK.dk_trans L LB sp 24576 M6 M7 M9); [apply PMK.dk_grows; exact MG7|].
apply (PMK.dk_trans L LB sp 24576 M7 M8 M9 DK78). apply PMK.dk_grows. exact MG9. }
assert (DEFO9 : L5.defined M9 op 384) by (apply (defined_dk LB sp 24576 M0 M9 op 384 DK09 STK); [lia|lia|lia|exact DEFO]).
assert (DEFQ9 : L5.defined M9 qc 16384).
{ apply (L5.defined_grows M8 M9 _ _ MG9). apply (L5C.defined_agree M7 M8 qc 16384 AGq). apply (L5.defined_grows M6 M7 _ _ MG7). exact FDEFq. }
assert (DEFB9 : L5.defined M9 bb 32) by (apply (L5.defined_grows M8 M9 _ _ MG9); exact FDEFb).
cbn [pa_vp_parser pa_vp_nullis pa_vp_nullbuf pa_vp_nullis_ios pa_classic_imp AD PmLayoutS.ADDR_S] in *.
apply (KONT fx9 R9 M9 model8 qc bb (debit L (debit L cr 16384) 32)).
- apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
assert (CH : forall j, In j CSR -> getr R9 (PMK.reg j) = getr R0 (PMK.reg j)).
{ intros j Hj. rewrite (KS9 j (csr_rcE j Hj)), (PMK.cs_of_preserved R7 R8 j RP8 (csr_cs j Hj)), (KS7 j (csr_rcD j Hj)).
rewrite (PMK.cs_of_preserved R5 R6 j RP6 (csr_cs j Hj)), (KS5 j (csr_rcC j Hj)), (PMK.cs_of_preserved R3 R4 j RP4 (csr_cs j Hj)).
rewrite (KS3 j (csr_rcB j Hj)), (PMK.cs_of_preserved R1 R2 j RP2 (csr_cs j Hj)). apply KS1. apply csr_rcA. exact Hj. }
destruct Hk as [<-|Hk]; [rewrite H2, Rsp; reflexivity|].
destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
destruct Hk as [<-|Hk]; [rewrite H8; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite H9; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite H18; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite H19; apply Z_to_bv_bv_unsigned|].
repeat (destruct Hk as [<-|Hk]; [apply CH; PMK.inl|]). destruct Hk.
- unfold PM.parser_at, PMSP.parser_init. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem].
split; [t14 AG19 C0|]. split; [exact DEFO9|]. split; [exact I|].
split; [t14 AG19 C8|]. split; [t14 AG19 C9|]. split; [t14 AG19 C12|]. split; [t14 AG19 C16|]. split; [t14 AG19 C20|].
split.
{ unfold PM.nullis_at. split; [t14 AG39 D32|]. split; [apply (L5.defined_sub M9 op 384); [exact DEFO9|lia|lia]|]. split; [exact I|].
split; [t14 AG59 F48|]. split; [t14 AG49 L56|].
unfold PM.iosb_at. split; [t14 AG39 D112|]. split; [t14 AG19 C144|]. split; [t14 AG19 C148|]. split; [t14 AG19 C152|].
split; [t14 AG29 L160|]. split; [t14 AG19 Z168|]. split; [apply (L5.defined_sub M9 op 384); [exact DEFO9|lia|lia]|]. split; [exact I| left; reflexivity]. }
split.
{ unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
split; [t14 AG59 F264|]. split; [t14 AG59 F272|]. split; [apply (L5.defined_sub M9 op 384); [exact DEFO9|lia|lia]|].
split; [t14 AG79 H288|]. split; [unfold PM.CHUNK; t14 AG59 F296|]. split; [t14 AG79 H304|]. split; [t14 AG59 F312|].
split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact FQ16|]. split; [unfold PM.CHUNK; exact DEFQ9|]. split; exact I. }
split; [unfold PM.MAX_DEPTH; t14 AG79 H320|]. split; [unfold PM.MAX_ITEMS; t14 AG79 H328|]. split; [exact I|].
split.
{ unfold PM.vstr_at. split; [apply (L5.defined_sub M9 op 384); [exact DEFO9|lia|lia]|]. split; [exact I|]. split; [lia|].
apply (L5C.u8_at_agree RSEGS M7); [intros i Hi; apply AG79; lia| lia| lia|]. apply (PMCG.u8_of_zeros RSEGS M7); [|lia|lia].
apply (PMCG.zeros_sub M7 (op + 336) 48); [exact Z336|lia|lia]. }
split.
{ unfold PM.vec_at. cbn [length Z.of_nat Pos.of_succ_nat]. change (2 ^ 0) with 1.
split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem|]. split; [lia|]. split; [lia|]. split; [exact FB16|].
split; [exact DEFB9|]. split; [exact I|]. split; [exact I|].
intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn [nth PM.ps_root PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. unfold PM.pstate_at.
cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem| PMK.gmem]. }
split; [right; reflexivity|]. split; [left; reflexivity|]. unfold PM.MAX_DEPTH. lia.
- apply PMK.hpres_of; [exact EK09| destruct STK9 as (_ & _ & _ & _ & X); exact X| exact DK09].
- unfold PMSP.credit_keep, PMSP.cr0, PM.credit_add, PM.cost1, PM.CHUNK, debit. cbn [fst snd]. lia.
- apply (L5C.model_but_vm_trans _ _ _ MB6 MB8).
- unfold PM.parser_own, PMSP.parser_init, PM.src_own, PM.vec_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc PM.vs_own app]. change (32 * 2 ^ 0) with 32.
apply (hio_perm L SCFG HI HIok LB8 _ _ M9 _ HH9).
+ intros x. unfold LB8, LB6. cbn [In]. split; (intros [E|[E|E]]; [right; left; exact E| left; exact E| right; right; exact E]).
+ pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LB8 _ M9 _ HH9))) as ND. unfold LB8, LB6 in ND. cbn [map fst] in ND |- *.
apply PMCG.nodup_swap. exact ND.
Qed.
End Stage.
End PMRD.
