(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmTopS PmSHarnessStmts PmSHarnessKit PmSHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSHarness3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["1list"; "1nil"; "1option"; "2Z"; "0HI"; "0K"; "0L"; "0LB0"; "3Model"; "3event"; "4bvmap"; "0M"; "0M0"; "0M1"; "0R"; "0R0"]; ["0R1"; "5credit"; "6SCFG"; "7strm"; "7vstr"; "8H2"; "8H3"; "9cfg"; ":reader_ctor_spec"; ";FPState"; "<srealizes"; "=loaded_segments"; "0SCFG_P"; "0b"; "0cr"; "0cr0"]; ["0cr1"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0qc"; "0ra"; "0s"; "0s2"; "0sm"; "0sp"; ">bv"; "0x"]]).
Module PMH3.
Import PMS. Import PMH.
Local Ltac lia := PMK.alia.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (512, 2 ^ 29 + 8 * n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Lemma stage3 : ltac2:(TCodec.tc2 tcn__PmSHarness3 "RH&HvLv6v4%43321'I&:y5'Q>yR0%211%5241'2y8%611%311p061'8&A'D'C'0'9%211!pS021&Ev?v<vQ5vQ=vQ9vQ7v7vOvQ3r8r7r6r5r4r3r2%ABQ9Q8@?>=<;:987654321(1%11G%411'3&Fr=r<r;r1%5DQCQBJIHGFEDCB?>=<432;1'J&K&B%11QH&G+V`V4%265HG1FE%74641:p091pQL@1pRBA1pR2Q?1pR>QA1pLQC1pQ2QI1pR6R01+V`SHr:r9%?6BGF321%D4CA1Q2p061p0N1p0Q21p<QE1pRJQK1pRHQM1pRFQN1pQNR01pR:R21pHR41pNR:1pR4RA1p0RC1").
Proof using All.
intros RDR fx R M model cr s s2 sm K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & HST & HH & CK) K0 KONT.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (_ & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & LBhi & BASE & MBV & (Mh & Ml & Mm)).
set (LBc := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
assert (LBhic : forall b, In b LBc -> fst b + snd b <= hl_ceil L).
{ intros b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBc cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
cfeed P (PMSHP.hnC_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & A11 & A12 & A13 & C0 & C1 & C2 & C3 & C4 & C5)); PMK.pvz_clrT.
set (P := fun a => (sp - 744 <= a < sp - 744 + 32) \/ (sp - 320 <= a < sp - 320 + 8)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
assert (PF : forall a, P a -> PMH.fb sp <= a < PMH.fb sp + 752) by (intros a [X|X]; unfold PMH.fb, FRAME; lia).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34078 R1 0x355f8 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply PF in Pa. unfold PMH.fb, FRAME in Pa. left. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (CORE1 : PMH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PMH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
assert (SCx : 0 <= 65536 - 752) by lia.
assert (BRc : PMHK.brange L LBc) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
assert (VS1 : PM.vstr_at RSEGS PMH.T3 M1 (PMH.fb sp + 712) s).
{ eapply (PMHK.vstr_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS].
- intros i Hi [X|X]; unfold PMH.fb, FRAME in Hi; lia.
- unfold LBc. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (IA1 : PM.iss_at RSEGS AD PMH.T3 M1 (PMH.fb sp + 440) s2 sm).
{ eapply (PMHK.iss_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact IA].
- intros i Hi [X|X]; unfold PMH.fb, FRAME in Hi; lia.
- unfold LBc. apply incl_appl. apply incl_refl. }
assert (HST1 : PMH.hstat M1 true (PMST.st_sys g) (PMST.st_err g)).
{ apply (PMHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST). }
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _ & _ & _ & _ & _ & _ & _ & BASE1 & _).
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PMF.pot_call_le L n HK HB Hn) as (PC1 & PC2).
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 752) (PMSP.pm_scr 6)).
{ apply (PMK.stk_call L M1 (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 6) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|]. destruct STK1 as (X & _). exact X. }
unfold PMS.reader_ctor_spec, PMSP.reader_ctor_spec in RDR.
apply (RDR fx1 R1 M1 model K LBc cr (sp - 752) 213188 (sp - 752) (sp - 744) (sp - 745) s2 sm HH1).
- repeat split; assumption.
- exact K0.
- unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc.
- unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia|]. destruct STK1 as (X & _). exact X.
- rewrite L5K.rl10. unfold PMSP.o_p. cbn [pa_off_p AD]. replace (sp - 752 + 40) with (sp - 712) by lia. exact A10.
- rewrite L5K.rl11. unfold PMSP.o_is. cbn [pa_off_is AD]. replace (sp - 752 + 440) with (sp - 312) by lia. exact A11.
- rewrite L5K.rl12. exact A12.
- rewrite L5K.rl13. exact A13.
- lia.
- unfold PMSP.o_p. cbn [pa_off_p AD]. lia.
- destruct STK1 as (X & _). lia.
- unfold PMSP.o_p. cbn [pa_off_p AD]. pose proof CORE1 as (_ & _ & _ & _ & _ & DFR1 & _). unfold PMH.fb, FRAME in DFR1. apply (L5.defined_sub M1 (sp - 752) 752 (sp - 752 + 40) 384 DFR1); lia.
- exact C4.
- replace (sp - 744 + 8) with (sp - 736) by lia. exact C3.
- replace (sp - 744 + 24) with (sp - 720) by lia. exact C0.
- unfold PMSP.o_is. cbn [pa_off_is AD]. exact IA1.
- exact BASE1.
- destruct HST1 as (X & _). exact X.
- destruct CK as (CK1 & CK2). destruct Hcr0 as (C6 & C7).
unfold PMSP.credit_le, PMSP.credit_keep, PMH.P0, PMH.rest2, PM.pot_call, PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text, PM.vs_cap in *. cbn [fst snd] in *. lia.
- intros fx2 R2 M2 model2 qc b cr2 RP PA HP CK2 MB HH2.
apply (KONT fx2 R2 M2 model2 cr2 qc b). unfold PMH.H3.
unfold PMSP.o_p, PMSP.o_is in *. cbn [pa_off_p pa_off_is AD] in *.
set (W' := [(sp - 752 + 40, 384)]) in *.
assert (WC : forall a, PMK.inW W' a -> sp - 712 <= a < sp - 328).
{ intros a (r & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (EKc : PMK.ek L LBc (sp - 752) (PMSP.pm_scr 6) W' M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (SC6 : 0 <= PMSP.pm_scr 6) by (unfold PMSP.pm_scr; lia).
assert (WSTD : forall a, PMK.inW W' a -> PMH.fb sp <= a \/ 65536 <= a < 954368) by (intros a I; apply WC in I; left; unfold PMH.fb, FRAME; lia).
split. { apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LBc (PMSP.pm_scr 6) W' CORE1 RP HP);
[unfold LBc; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
intros a I. apply WC in I. left. unfold PMH.fb, FRAME. lia. }
split. { eapply (PMHK.vstr_keep L LY sp LBc (PMSP.pm_scr 6) W' M1 M2 EKc STKc SC6 BRc WSTD);
[unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS1].
- intros i Hi I. apply WC in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold LBc. apply incl_appr. apply incl_appl. apply incl_refl. }
split; [exact SZ|].
split. { eapply (PMHK.iss_keep L LY sp LBc (PMSP.pm_scr 6) W' M1 M2 EKc STKc SC6 BRc WSTD);
[unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact IA1].
- intros i Hi I. apply WC in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold LBc. apply incl_appl. apply incl_refl. }
split; [exact SZ2|]. split; [exact SG|]. split; [exact ST0|].
split. { unfold PMH.fb, FRAME. exact PA. }
split. { eapply (PMHK.u64_keep L LY sp LBc (PMSP.pm_scr 6) W' M1 M2 EKc STKc SC6); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |].
- intros i Hi I. apply WC in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold PMH.fb, FRAME. replace (sp - 752 + 432) with (sp - 320) by lia. exact C5. }
split. { apply (PMHK.hstat_keep L LY LBc (sp - 752) (PMSP.pm_scr 6) W' M1 M2 EKc); [|exact HST1]. intros a I. apply WC in I. left. lia. }
split; [exact HH2|].
destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4).
unfold PMSP.credit_keep, PMH.P0, PMH.rest2, PMH.rest3, PM.pot_call, PM.credit_add, PM.cost1, PMSP.cr0 in *. cbn [fst snd] in *. lia.
Qed.
End Stage.
End PMH3.
