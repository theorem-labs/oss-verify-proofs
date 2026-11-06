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
Ltac2 tcn__PmSHarness5 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nil"; "1option"; "2Z"; "0HI"; "0K"; "0L"; "0LB0"; "3Model"; "3event"; "4bvmap"; "0M"; "0M0"; "0M1"; "0R"]; ["0R0"; "0R1"; "5credit"; "6SCFG"; "7pst"; "7strm"; "7vstr"; "8H4"; "8H5"; "9cfg"; ":parse_spec"; ";FPState"; "<srealizes"; "=loaded_segments"; "0SCFG_P"; "0b"]; ["0be"; "0cr"; "0cr0"; "0cr1"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0p"; "0qc"; "0ra"; "0s"; "0s2"]; ["0sm"; "0sm1"; "0sp"; ">bv"; "0x"]]).
Module PMH5.
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
Lemma stage5 : ltac2:(TCodec.tc2 tcn__PmSHarness5 "S0&JvNv7v5%43321'K&;y5'QCyR0%211%5241'3y8%611%311p061'9&B'F'E'4'1':%211!pS:21&Gv@v=vQ8vQBvQ=vQ:v8vQ2vQ6r:r9r8r7r6r5r4r3r2%CDQ<Q;BA@?>=<;:987654321(2%11I%411'D'0&Hr@r?r1%4DQFQELKJIHGFED@?>=32<;1'L&M&C%11QK&I+V`W@%265IH1GFr<%847521p0:1pR2@1pS4Q@1pRHC1pR8QD1pRDQF1pNQH1pQ4QN1pR<R51r>r=+V`W0r;%B6E432?1%G4FD1Q5p071p0Q11p0Q51p>QJ1pR0R01pRJR11pS2R31pS0R51pRNR61pR4R81pR@R:1pJR<1pQ0RB1pR:RI1p0RK1").
Proof using All.
intros PARSE fx R M model cr s s2 sm qc b K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & PA & VV & HST & HH & CK & EC & VREF) K0 KONT.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
set (p0 := PMSP.parser_init qc b) in *.
set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
set (LBc := PM.parser_own p0 ++ LBX) in *.
assert (VREF' : L5.u64_at RSEGS M (sp - 328) (sp - 320)).
{ unfold PMH.fb, FRAME in VREF. replace (sp - 752 + 424) with (sp - 328) in VREF by lia. replace (sp - 752 + 432) with (sp - 320) in VREF by lia. exact VREF. }
cfeed P (PMSHP.hnF_conc fx R M (fun j => match j with 2%nat => sp | 40%nat => sp - 320 | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10 & A11 & A12)); PMK.pvz_clrT.
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x340e0 R1 0x35aac M1 (fun _ => False) K HH Mh Ml ltac:(lia) MS MG).
{ intros a Ha _. apply FRZ. exact Ha. }
{ intros a []. }
{ intros a. right. tauto. }
intros HH1.
assert (CORE1 : PMH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 (fun _ => False) CORE MG); [intros a Ha _; apply FRZ; exact Ha| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & _).
pose proof CORE1 as (_ & Hcs1 & _).
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PMF.pot_call_le L n HK HB Hn) as (PC1 & PC2).
assert (SC10 : 0 <= PMSP.pm_scr 10) by (unfold PMSP.pm_scr; lia).
assert (STKc : L5C.stk (hl_sptop L) M (sp - 752) (PMSP.pm_scr 10)).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 10) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
destruct HST as (SLOC & SSYS & SERR).
pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IAE & _).
unfold PMS.parse_spec, PMSP.parse_spec in PARSE.
apply (PARSE fx1 R1 M model K LBX cr (sp - 752) 213232 (sp - 752) (pa_syscat_obj AD) p0 s2 sm (PMST.st_err g) HH1).
- repeat split; assumption.
- exact K0.
- unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc.
- unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact A16f].
- unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD]. rewrite L5K.rl10, L5K.rl11, L5K.rl12.
split; [replace (sp - 752 + 40) with (sp - 712) by lia; exact A10|]. split; [replace (sp - 752 + 432) with (sp - 320) by lia; exact A11|].
replace (sp - 752 + 8) with (sp - 744) by lia. exact A12.
- unfold PMSP.run_pre, PMSP.visitor_at, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD].
split; [exact PA|]. split; [exact IA|]. split; [exact VV|].
split; [unfold PMH.fb, FRAME in VREF; replace (sp - 752 + 40 + 384) with (sp - 752 + 424) by lia; exact VREF|].
split; [exact BASE|]. split; [exact SERR|]. unfold PM.tb_ok. cbn. split; [lia|]. split; [lia| reflexivity].
- unfold LBX. apply incl_appl. apply incl_refl.
- unfold PM.inv, p0, PMSP.parser_init. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg length].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split. { unfold PM.stack_shape. cbn [length nth]. split; [lia|]. split; [unfold PM.MAX_DEPTH; lia|]. split; [left; reflexivity|].
split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PM.pstate_ok, PM.ps_root. cbn. split; [lia|]. right. right. split; [left; reflexivity| split; reflexivity]. }
unfold PM.tb_ok. cbn. split; [lia|]. split; [lia| reflexivity].
- unfold PMSP.o_ec. cbn [pa_off_ec AD]. exact EC.
- unfold PM.unread, p0, PMSP.parser_init. cbn [PM.p_src PM.sr_rem]. unfold PMH.fb, FRAME in IAE, SG. rewrite IAE, SG, SZ2.
replace (sp - 752 + 440 + 80) with (sp - 752 + 520) by lia. lia.
- destruct CK as (CK1 & CK2). destruct Hcr0 as (C6 & C7).
unfold PMSP.credit_le, PMSP.credit_keep, PMH.P0, PMH.rest3, PM.pot_call, PM.pot_parser, p0, PMSP.parser_init, PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text, PM.vs_cap in *. cbn [fst snd PM.p_k PM.p_tb PM.p_tg] in *. lia.
- intros fx2 R2 M2 model2 p sm2 be cr2 RP (RPRE & SSTEP & EMONO & ECD) HP CK2 MB HH2.
destruct RPRE as (PA2 & IA2 & _ & _ & _ & SERR2 & _).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.o_ec, PMSP.o_src, PMSP.o_tb, PMSP.o_vec in *. cbn [pa_off_p pa_off_is pa_off_v pa_off_ec AD] in *.
apply (KONT fx2 R2 M2 model2 cr2 p sm2 be). unfold PMH.H5.
assert (WC : forall a, PMK.inW (PMSP.W_run AD (sp - 752)) a -> (sp - 752 + 8 <= a < sp - 752 + 600) \/ PMHK.err_dom a).
{ intros a (r & Hin & Hr). unfold PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_tb, PMSP.o_vec, PMSP.o_is, PMSP.o_ec, PMSP.o_p in Hin.
cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit AD app] in Hin. unfold L5.in_rng in Hr. unfold PMHK.err_dom.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Hr; lia. }
assert (EKc : PMK.ek L LBX (sp - 752) (PMSP.pm_scr 10) (PMSP.W_run AD (sp - 752)) M M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (BRx : PMHK.brange L LBX) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBX cr M _ HH); unfold LBc; apply incl_appr; apply incl_refl).
assert (WSTD : forall a, PMK.inW (PMSP.W_run AD (sp - 752)) a -> PMH.fb sp <= a \/ 65536 <= a < 954368).
{ intros a I. destruct (WC a I) as [F|F]; [left; unfold PMH.fb, FRAME; lia| right; unfold PMHK.err_dom in F; lia]. }
split. { apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 LBX (PMSP.pm_scr 10) (PMSP.W_run AD (sp - 752)) CORE1 RP HP);
[unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
intros a I. destruct (WC a I) as [F|F]; [left; unfold PMH.fb, FRAME; lia|]. right. unfold PMHK.err_dom in F.
destruct F as [F|F]; [exists (0xc6260, 2)| exists (0xe7ca8, 544)]; (split; [unfold WF, pm_foot; cbn; auto 7| unfold L5.in_rng; cbn [fst snd]; lia]). }
split. { eapply (PMHK.vstr_keep L LY sp LBX (PMSP.pm_scr 10) (PMSP.W_run AD (sp - 752)) M M2 EKc STKc SC10 BRx WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS].
- intros i Hi I. unfold PMH.fb, FRAME in Hi. destruct (WC i I) as [F|F]; [lia| unfold PMHK.err_dom in F; lia].
- unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
split; [exact SZ|].
split; [unfold PMH.fb, FRAME; exact IA2|].
split; [unfold PMH.fb, FRAME; exact PA2|].
split. { split; [|split; [|exact SERR2]].
- apply (PMHK.loc_keep L LY LBX (sp - 752) (PMSP.pm_scr 10) (PMSP.W_run AD (sp - 752)) M M2 EKc); [|exact SLOC].
intros a I D. unfold PMHK.loc_dom in D. destruct (WC a I) as [F|F]; [lia| unfold PMHK.err_dom in F; lia].
- apply (PMHK.sys_keep L LY LBX (sp - 752) (PMSP.pm_scr 10) (PMSP.W_run AD (sp - 752)) M M2 EKc); [|exact SSYS].
intros a I D. unfold PMHK.sys_dom in D. destruct (WC a I) as [F|F]; [lia| unfold PMHK.err_dom in F; lia]. }
split; [exact EMONO|].
split; [exact HH2|].
destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4).
unfold PMSP.credit_keep, PMH.P0, PMH.rest3, PM.pot_call, PM.pot_parser, p0, PMSP.parser_init, PM.credit_add, PM.cost1, PMSP.cr0 in *. cbn [fst snd PM.p_k PM.p_tb PM.p_tg] in *. lia.
Qed.
End Stage.
End PMH5.
