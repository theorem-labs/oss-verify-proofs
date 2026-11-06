(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmTopU PmUHarnessStmts PmUHarnessKit PmUHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUHarness2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUHarnessStmts.PMUH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "stdpp.bitvector.definitions."], [["1list"; "1nil"; "1option"; "2Z"; "0HI"; "0K"; "0L"; "0LB0"; "3Model"; "3event"; "4bvmap"; "0M"; "0M0"; "0M1"; "0R"; "0R0"]; ["0R1"; "5credit"; "6SCFG"; "7ADDR_U"; "8strm"; "8vstr"; "9cfg"; "9loc_W"; ":iss_ctor_spec"; ";inW"; "<H1"; "<H2"; "<WF"; "=FPState"; ">srealizes"; "?loaded_segments"]; ["0SCFG_P"; "0a"; "0cr"; "0cr0"; "0cr1"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0ra"; "0s"; "0s2"; "0sm"]; ["0sp"; "@bv"; "0x"]]).
Module PMUH2.
Import PMU. Import PMUH.
Local Ltac lia := PMK.alia.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
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
Lemma locW_in_WF : ltac2:(TCodec.tc2 tcn__PmUHarness2 "<'3&I&G&C%211r1%5221&Lr2%8221p041pR4;1").
Proof. intros a.
intros (r & Hin & Hr). unfold PMSP.loc_W in Hin. cbn in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr.
- exists (0xc74e2, 0xc7c20 - 0xc74e2). split; [unfold WF, pm_foot; cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
- exists (0xc8348, 0xc83a0 - 0xc8348). split; [unfold WF, pm_foot; cbn; auto 6| unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma stage2 : ltac2:(TCodec.tc2 tcn__PmUHarness2 "RC&HvQ0v6v4%43321'M&:y5'QAyR0%211%5241'2y8%611%311p061'8&A'E'0'9%211!pS621&Jv?v<vQ9vQ@vQ<vQ;v7vQ3vQ7r6r5r4r3r2%?@Q6Q5>=<;:987654321(1%11E%411'D&Kr;r1%3BQ>Q=FEDCBA@?>=<;:291'N&O&B%11QC&Fr8r7+V`g8%467321FE%94861<p0;1pS0@1pRNQ:1pR:Q<1pRFQ>1pLQ@1pQ2QF1pR>QM1r:r9+V`fH%A6D321@?%F4EC1Q2p061p0N1p0Q21p<QC1pRLQI1pR6QK1pRBQM1pHQO1pNR51pR<R<1p0R>1").
Proof using All.
intros ISS fx R M model cr s K (CORE & VS & SZ & (SLOC & SSYS & SERR) & HH & CK & LONG) K0 KONT.
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (_ & _ & _ & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & _ & _ & LBhi & BASE & MBV & (Mh & Ml & Mm)).
cfeed P (PMUHP.huB_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10 & A11 & A12)); PMK.pvz_clrT.
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok (PM.vs_own s ++ LB0) cr M model fx fx1 R 0x342d8 R1 0x34550 M1 (fun _ => False) K HH Mh Ml ltac:(lia) MS MG).
{ intros a Ha _. apply FRZ. exact Ha. }
{ intros a []. }
{ intros a. right. tauto. }
intros HH1.
assert (CORE1 : PMUH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
{ apply (PMUHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 (fun _ => False) CORE MG); [intros a Ha _; apply FRZ; exact Ha| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMUH.CSK_in. vm_compute. reflexivity. }
assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & _).
pose proof CORE1 as (_ & Hcs1 & _).
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PMF.pot_call_le L n HK HB Hn) as (PC1 & PC2).
assert (A8a : (sp - 312) mod 8 = 0).
{ clear - A16. apply Z.mod_divide in A16; [|lia]. destruct A16 as (q & ->). replace (q * 16 - 312) with ((2 * q - 39) * 8) by lia. apply Z.mod_mul. lia. }
assert (A8b : (sp - 40) mod 8 = 0).
{ clear - A16. apply Z.mod_divide in A16; [|lia]. destruct A16 as (q & ->). replace (q * 16 - 40) with ((2 * q - 5) * 8) by lia. apply Z.mod_mul. lia. }
assert (STKc : L5C.stk (hl_sptop L) M (sp - 752) (PMSP.pm_scr 4)).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 4) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|]. destruct STK as (X & _). exact X. }
pose proof CORE1 as (_ & _ & _ & _ & _ & _ & SPT & _).
unfold PMU.iss_ctor_spec, PMSP.iss_ctor_spec in ISS.
apply (ISS fx1 R1 M model K (PM.vs_own s ++ LB0) cr (sp - 312) (sp - 40) (sp - 752) 213736 s (PMST.st_loc g) HH1).
- repeat split; assumption.
- exact K0.
- unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc.
- rewrite L5K.rl10. exact A10.
- rewrite L5K.rl11. exact A11.
- rewrite L5K.rl12. exact A12.
- lia.
- lia.
- lia.
- exact A8a.
- exact A8b.
- pose proof CORE1 as (_ & _ & _ & _ & _ & DFR1 & _). unfold PMUH.fb, FRAME in DFR1. apply (L5.defined_sub M (sp - 752) 752 (sp - 312) 272 DFR1); lia.
- unfold PMUH.fb, FRAME in VS. replace (sp - 752 + 712) with (sp - 40) in VS by lia. exact VS.
- apply incl_appl. apply incl_refl.
- rewrite SZ. lia.
- exact LONG.
- destruct CORE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B & _). exact B.
- exact SLOC.
- destruct CK as (CK1 & CK2). destruct Hcr0 as (C1 & C2). rewrite SZ.
unfold PMSP.credit_le, PMSP.credit_keep, PMUH.P0, PMUH.rest1, PM.pot_call, PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text, PM.vs_cap in *. cbn [fst snd] in *. lia.
- intros fx2 R2 M2 model2 s2 sm cr2 RP IA SZ2 SG ST0 LOC2 HP CK2 MB HH2.
apply (KONT fx2 R2 M2 model2 cr2 s2 sm). unfold PMUH.H2.
set (W' := (sp - 312, 272) :: (if PMST.st_loc g then [] else PMSP.loc_W AD)) in *.
assert (WC : forall a, PMK.inW W' a -> (sp - 312 <= a < sp - 40) \/ PMK.inW (PMSP.loc_W AD) a).
{ intros a (r & Hin & Hr). unfold W' in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
right. destruct (PMST.st_loc g); [destruct Hin| exists r; split; assumption]. }
assert (WL : forall a, PMK.inW (PMSP.loc_W AD) a -> PMUHK.loc_dom a).
{ intros a (r & Hin & Hr). unfold PMSP.loc_W in Hin. cbn in Hin. unfold L5.in_rng in Hr. unfold PMUHK.loc_dom.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
assert (EKc : PMK.ek L (PM.vs_own s ++ LB0) (sp - 752) (PMSP.pm_scr 4) W' M M2) by (apply (PMK.ek_of_hpres L); exact HP).
split. { apply (PMUHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 (PM.vs_own s ++ LB0) (PMSP.pm_scr 4) W' CORE1 RP HP);
[apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
intros a I. destruct (WC a I) as [F|F]; [left; unfold PMUH.fb, FRAME; lia| right; apply locW_in_WF; exact F]. }
split. { apply (PMUHK.vstr_keep L LY sp (PM.vs_own s ++ LB0) (PMSP.pm_scr 4) W' M M2 EKc STKc ltac:(unfold PMSP.pm_scr; lia) (PMUHK.brange_of_heap L HI LY HIok _ _ cr M _ HH1 (incl_refl _)));
[|unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |apply incl_appl; apply incl_refl|exact VS].
- intros a I. destruct (WC a I) as [F|F]; [left; unfold PMUH.fb, FRAME; lia| right; apply WL in F; unfold PMUHK.loc_dom in F; lia].
- intros i Hi I. unfold PMUH.fb, FRAME in Hi. destruct (WC i I) as [F|F]; [lia| apply WL in F; unfold PMUHK.loc_dom in F; lia]. }
split; [exact SZ|].
split. { unfold PMUH.fb, FRAME. replace (sp - 752 + 440) with (sp - 312) by lia. exact IA. }
split; [rewrite SZ2; exact SZ|].
split. { unfold PMUH.fb, FRAME. replace (sp - 752 + 520) with (sp - 312 + 80) by lia. exact SG. }
split; [exact ST0|].
split. { split; [exact LOC2|]. split.
- apply (PMUHK.sys_keep L LY (PM.vs_own s ++ LB0) (sp - 752) (PMSP.pm_scr 4) W' M M2 EKc); [|exact SSYS].
intros a I D. unfold PMUHK.sys_dom in D. destruct (WC a I) as [F|F]; [lia| apply WL in F; unfold PMUHK.loc_dom in F; lia].
- apply (PMUHK.err_keep L LY (PM.vs_own s ++ LB0) (sp - 752) (PMSP.pm_scr 4) W' M M2 EKc); [|exact SERR].
intros a I D. unfold PMUHK.err_dom in D. destruct (WC a I) as [F|F]; [lia| apply WL in F; unfold PMUHK.loc_dom in F; lia]. }
split; [exact HH2|].
destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4). rewrite SZ in CK3, CK4.
unfold PMSP.credit_keep, PMUH.P0, PMUH.rest1, PMUH.rest2, PM.pot_call, PM.credit_add, PM.cost1, PMSP.cr0 in *. cbn [fst snd] in *. lia.
Qed.
End Stage.
End PMUH2.
