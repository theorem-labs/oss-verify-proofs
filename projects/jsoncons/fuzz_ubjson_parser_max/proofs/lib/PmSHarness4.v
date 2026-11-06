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
Ltac2 tcn__PmSHarness4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["1list"; "1nil"; "1option"; "2Z"; "0HI"; "0K"; "0L"; "0LB0"; "3Model"; "3event"; "4bvmap"; "0M"; "0M0"; "0M1"; "0R"; "0R0"]; ["0R1"; "5credit"; "6SCFG"; "7strm"; "7vstr"; "8H3"; "8H4"; "9cfg"; ":reset_spec"; ":syscat_spec"; ";FPState"; "<srealizes"; "=loaded_segments"; "0SCFG_P"; "0b"; "0cr"]; ["0cr0"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0qc"; "0ra"; "0s"; "0s2"; "0sm"; "0sp"; ">bv"; "0x"]]).
Module PMH4.
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
Lemma stage4 : ltac2:(TCodec.tc2 tcn__PmSHarness4 "RK&IvMv6v4%43321&H%13543'J&:y5'Q>yR0%211%5241'2y8%611%311p061'8&A'D'C'3'0'9%211!pS021&Ev?v<vQ5vQ=vQ9vQ7v7vQ0vQ3r:r9r8r7r6r5r4r3r2%CDQ>Q=BA@?>=<;:987654321(1%11I%411&Fr1r=r<r;%5DQGQFKJIHGFEDC;:4321BA@'K&L&B%11QL&G+V`W0%265DC1BA%74641Hp091pR>Q@1pLQB1pQ2QH1pR6QO1r>+V`V4%;6>2C1BA%@4?=1Mp051p0I1p0M1p<QB1pQNQH1pRBQI1pRJQK1pRHQM1pRFQN1pR0R01pR:R21pHR41pNR:1pR4RA1p0RC1p0RF1").
Proof using All.
intros SYS RST fx R M model cr s s2 sm qc b K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & PA & VV & HST & HH & CK) K0 KONT.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & SPT & _ & _ & _ & _ & (Mh & Ml & Mm)).
set (p0 := PMSP.parser_init qc b) in *.
set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
set (LBc := PM.parser_own p0 ++ LBX) in *.
assert (BRc : PMHK.brange L LBc) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
assert (SCx : 0 <= 65536 - 752) by lia.
assert (INCo : incl (PM.parser_own p0 ++ PM.vs_own s2 ++ PM.vs_own s) LBc).
{ unfold LBc, LBX. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|]. apply in_or_app. right.
apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx| apply in_or_app; right; apply in_or_app; left; exact Hx]. }
assert (OB : PMHK.hobjs sp M s s2 sm p0) by (split; [exact VS| split; [exact IA| split; [exact PA| exact VV]]]).
cfeed P (PMSHP.hnD_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & C0 & C1)); PMK.pvz_clrT.
set (P := fun a => (sp - 328 <= a < sp - 328 + 8) \/ (sp - 744 <= a < sp - 744 + 4)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
assert (PF : forall a, P a -> PMH.fb sp <= a < PMH.fb sp + 752) by (intros a [X|X]; unfold PMH.fb, FRAME; lia).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x340c4 R1 0x59f60 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply PF in Pa. unfold PMH.fb, FRAME in Pa. left. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (CORE1 : PMH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PMH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
assert (OB1 : PMHK.hobjs sp M1 s s2 sm p0).
{ apply (PMHK.hobjs_piece L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc s s2 sm p0); [|exact INCo|exact OB]. intros a [X|X]; unfold PMH.fb, FRAME; lia. }
assert (HST1 : PMH.hstat M1 true (PMST.st_sys g) (PMST.st_err g)) by (apply (PMHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST)).
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _ & _ & _ & _ & _ & _ & _ & BASE1 & _).
assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 752) (PMSP.pm_scr 1)).
{ apply (PMK.stk_call L M1 (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 1) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
unfold PMS.syscat_spec, PMSP.syscat_spec in SYS.
apply (SYS fx1 R1 M1 model K LBc cr (sp - 752) 213204 (PMST.st_sys g) HH1).
{ repeat split; assumption. }
{ exact K0. }
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc. }
{ exact BASE1. }
{ destruct HST1 as (_ & X & _). exact X. }
intros fx2 R2 M2 RP2 A10s SYS2 HP2 HH2.
set (W2 := if PMST.st_sys g then [] else [(pa_syscat_guard AD, 2)]) in *.
assert (WC2 : forall a, PMK.inW W2 a -> PMHK.sys_dom a).
{ intros a (r & Hin & Hr). unfold W2 in Hin. destruct (PMST.st_sys g); [destruct Hin|]. destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn in Hr. unfold PMHK.sys_dom. lia. }
assert (EK2 : PMK.ek L LBc (sp - 752) (PMSP.pm_scr 1) W2 M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (WSTD2 : forall a, PMK.inW W2 a -> PMH.fb sp <= a \/ 65536 <= a < 954368) by (intros a I; apply WC2 in I; unfold PMHK.sys_dom in I; right; lia).
assert (CORE2 : PMH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model).
{ apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model LBc (PMSP.pm_scr 1) W2 CORE1 RP2 HP2);
[unfold LBc, LBX; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
intros a I. right. apply WC2 in I. unfold PMHK.sys_dom in I. exists (0xc6490, 2). split; [unfold WF, pm_foot; cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (OB2 : PMHK.hobjs sp M2 s s2 sm p0).
{ apply (PMHK.hobjs_call L LY sp LBc (PMSP.pm_scr 1) W2 M1 M2 EK2 STKc SC1 BRc WSTD2 s s2 sm p0); [|exact INCo|exact OB1].
intros a I. apply WC2 in I. unfold PMHK.sys_dom in I. unfold PMH.fb, FRAME. lia. }
assert (C0b : L5.u32_at RSEGS M2 (sp - 744) 0).
{ eapply (PMHK.u32_keep L LY sp LBc (PMSP.pm_scr 1) W2 M1 M2 EK2 STKc SC1); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact C0].
intros i Hi I. apply WC2 in I. unfold PMHK.sys_dom in I. lia. }
assert (C1b : L5.u64_at RSEGS M2 (sp - 328) (sp - 320)).
{ eapply (PMHK.u64_keep L LY sp LBc (PMSP.pm_scr 1) W2 M1 M2 EK2 STKc SC1); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact C1].
intros i Hi I. apply WC2 in I. unfold PMHK.sys_dom in I. lia. }
assert (HST2 : PMH.hstat M2 true true (PMST.st_err g)).
{ destruct HST1 as (X1 & _ & X3). split; [|split; [exact SYS2|]].
- apply (PMHK.loc_keep L LY LBc (sp - 752) (PMSP.pm_scr 1) W2 M1 M2 EK2); [|exact X1]. intros a I D. apply WC2 in I. unfold PMHK.sys_dom in I. unfold PMHK.loc_dom in D. lia.
- apply (PMHK.err_keep L LY LBc (sp - 752) (PMSP.pm_scr 1) W2 M1 M2 EK2); [|exact X3]. intros a I D. apply WC2 in I. unfold PMHK.sys_dom in I. unfold PMHK.err_dom in D. lia. }
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model CORE2) as (_ & Rsp2 & _ & _ & WR2 & STK2).
cfeed PE (PMSHP.hnE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PE as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1e & A10e & C2)); PMK.pvz_clrT.
set (PE := fun a => sp - 736 <= a < sp - 736 + 8).
assert (PFE : forall a, PE a -> PMH.fb sp <= a < PMH.fb sp + 752) by (intros a X; unfold PE in X; unfold PMH.fb, FRAME; lia).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M2 model fx2 fx3 R2 0x340d4 R3 0x35984 M3 PE K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3).
{ intros a Pa. apply PFE in Pa. unfold PMH.fb, FRAME in Pa. left. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH3.
assert (CORE3 : PMH.hcore L R0 M0 model0 sp ra LB0 R3 M3 model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R2 M2 model R3 M3 PE CORE2 MG3 FRZ3); [intros a X; unfold PE in X; unfold PMH.fb, FRAME; lia| rewrite (KS3 2%nat) by PMK.inl; exact Rsp2|].
intros k Hk. apply KS3. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
assert (OB3 : PMHK.hobjs sp M3 s s2 sm p0).
{ apply (PMHK.hobjs_piece L sp LBc M2 M3 PE (65536 - 752) FRZ3 PFE STK2 SCx BRc s s2 sm p0); [|exact INCo|exact OB2]. intros a X; unfold PE in X; unfold PMH.fb, FRAME; lia. }
assert (HST3 : PMH.hstat M3 true true (PMST.st_err g)) by (apply (PMHK.hstat_piece L LY sp LBc M2 M3 PE FRZ3 PFE true _ _ STK2 LBhic HST2)).
assert (C0c : L5.u32_at RSEGS M3 (sp - 744) 0) by (apply (PMHK.u32_keep_p M2 M3 PE FRZ3); [lia|lia| intros i Hi X; unfold PE in X; lia| exact C0b]).
assert (C1c : L5.u64_at RSEGS M3 (sp - 328) (sp - 320)) by (apply (PMHK.u64_keep_p M2 M3 PE FRZ3); [lia|lia| intros i Hi X; unfold PE in X; lia| exact C1b]).
rewrite L5K.rl10 in A10s. rewrite A10s, L5.unsigned_lit in C2 by (cbn; lia).
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R3 M3 model CORE3) as (_ & Rsp3 & _ & _ & _ & STK3).
pose proof CORE3 as (_ & Hcs3 & _).
assert (STKr : L5C.stk (hl_sptop L) M3 (sp - 752) (PMSP.pm_scr 1)).
{ apply (PMK.stk_call L M3 (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 1) STK3); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
destruct OB3 as (VS3 & IA3 & PA3 & VV3).
unfold PMS.reset_spec, PMSP.reset_spec in RST.
apply (RST fx3 R3 M3 model K LBX cr (sp - 752) 213216 (sp - 752) p0 HH3).
{ repeat split; assumption. }
{ exact K0. }
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1e|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp3|].
split; [rewrite (Hcs3 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs3 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKr. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact A16f]. }
{ rewrite L5K.rl10. unfold PMSP.o_p. cbn [pa_off_p AD]. replace (sp - 752 + 40) with (sp - 712) by lia. exact A10e. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD]. exact PA3. }
{ cbn. lia. }
intros fx4 R4 M4 RP4 PA4 HP4 HH4.
unfold PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec in *. cbn [pa_off_p pa_off_is AD] in *.
set (W4 := [(sp - 752 + 40 + 8, 8); (sp - 752 + 40 + 336, 24); (sp - 752 + 40 + 360, 24)]) in *.
assert (WC4 : forall a, PMK.inW W4 a -> sp - 712 <= a < sp - 328).
{ intros a (r & Hin & Hr). unfold W4 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
assert (EK4 : PMK.ek L LBX (sp - 752) (PMSP.pm_scr 1) W4 M3 M4) by (apply (PMK.ek_of_hpres L); exact HP4).
assert (BRx : PMHK.brange L LBX) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBX cr M _ HH); unfold LBc; apply incl_appr; apply incl_refl).
assert (WSTD4 : forall a, PMK.inW W4 a -> PMH.fb sp <= a \/ 65536 <= a < 954368) by (intros a I; apply WC4 in I; left; unfold PMH.fb, FRAME; lia).
apply (KONT fx4 R4 M4 model). unfold PMH.H4.
assert (CORE4 : PMH.hcore L R0 M0 model0 sp ra LB0 R4 M4 model).
{ apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R3 M3 model R4 M4 model LBX (PMSP.pm_scr 1) W4 CORE3 RP4 HP4);
[unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
intros a I. apply WC4 in I. left. unfold PMH.fb, FRAME. lia. }
split; [exact CORE4|].
split. { eapply (PMHK.vstr_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1 BRx WSTD4); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS3].
- intros i Hi I. apply WC4 in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
split; [exact SZ|].
split. { eapply (PMHK.iss_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1 BRx WSTD4); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact IA3].
- intros i Hi I. apply WC4 in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold LBX. apply incl_appl. apply incl_refl. }
split; [exact SZ2|]. split; [exact SG|]. split; [exact ST0|].
split. { unfold PMH.fb, FRAME. exact PA4. }
split. { eapply (PMHK.u64_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact VV3].
intros i Hi I. apply WC4 in I. unfold PMH.fb, FRAME in Hi. lia. }
split. { apply (PMHK.hstat_keep L LY LBX (sp - 752) (PMSP.pm_scr 1) W4 M3 M4 EK4); [|exact HST3]. intros a I. apply WC4 in I. left. lia. }
split; [exact HH4|]. split; [exact CK|].
assert (C0d : L5.u32_at RSEGS M4 (sp - 744) 0).
{ eapply (PMHK.u32_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact C0c].
intros i Hi I. apply WC4 in I. lia. }
assert (C2d : L5.u64_at RSEGS M4 (sp - 736) (pa_syscat_obj AD)).
{ eapply (PMHK.u64_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact C2].
intros i Hi I. apply WC4 in I. lia. }
assert (C1d : L5.u64_at RSEGS M4 (sp - 328) (sp - 320)).
{ eapply (PMHK.u64_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact C1c].
intros i Hi I. apply WC4 in I. lia. }
split.
- unfold PMSP.ec_at, PMH.fb, FRAME. replace (sp - 752 + 8) with (sp - 744) by lia. split; [exact C0d|]. split; [replace (sp - 744 + 8) with (sp - 736) by lia; exact C2d|].
destruct CORE4 as (_ & _ & _ & _ & _ & DFR & _). unfold PMH.fb, FRAME in DFR. apply (L5.defined_sub M4 (sp - 752) 752); [exact DFR|lia|lia].
- unfold PMH.fb, FRAME. replace (sp - 752 + 424) with (sp - 328) by lia. replace (sp - 752 + 432) with (sp - 320) by lia. exact C1d.
Qed.
End Stage.
End PMH4.
