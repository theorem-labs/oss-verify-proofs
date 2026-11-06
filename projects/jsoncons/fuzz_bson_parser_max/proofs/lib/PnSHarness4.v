(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout PnLayoutS PmModel PmModelFacts PmStatics PmSpecs PnSpecsS PmStep PmKeep PnKitS
     PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnRunS PnTopS PnSHarnessStmts PnSHarnessKit PnSHarnessP.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH4.
Import PMS. Import PNH.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
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
Variable g : PNST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (PNTS.TOPK, PNTS.TOPB n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).

Lemma stage4 :
  PMS.syscat_spec L HI -> PNRS.reset_spec L HI ->
  forall (fx : FPState) R M model cr s s2 sm qc b K,
    PNH.H3 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 sm qc b -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        PNH.H4 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr s s2 sm qc b ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34480 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34464 M model) K.
Proof using All.
  intros SYS RST fx R M model cr s s2 sm qc b K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & PA & VV & HST & HH & CK) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & _ & _ & _ & _ & _ & SPT & _ & _ & _ & _ & (Mh & Ml & Mm)).
  set (p0 := PNR.bparser_init qc b) in *.
  set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  set (LBc := PNM.bparser_own p0 ++ LBX) in *.
  assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
  assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
  assert (SCx : 0 <= 65536 - 784) by lia.
  assert (INCo : incl (PNM.bparser_own p0 ++ PM.vs_own s2 ++ PM.vs_own s) LBc).
  { unfold LBc, LBX. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|]. apply in_or_app. right.
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx| apply in_or_app; right; apply in_or_app; left; exact Hx]. }
  assert (OB : PNHK.hobjs sp M s s2 sm p0) by (split; [exact VS| split; [exact IA| split; [exact PA| exact VV]]]).
  LeanFeed.pfeed P (PNSHP.bhnD_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & C0 & C1)); PMK.pvz_clrT.
  set (P := fun a => (sp - 328 <= a < sp - 328 + 8) \/ (sp - 768 <= a < sp - 768 + 4)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
  assert (PF : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a [X|X]; unfold PNH.fb, FRAME; lia).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34464 R1 0x5ac98 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
  { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PNH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
    intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
  assert (OB1 : PNHK.hobjs sp M1 s s2 sm p0).
  { apply (PNHK.hobjs_piece L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc s s2 sm p0); [|exact INCo|exact OB]. intros a [X|X]; unfold PNH.fb, FRAME; lia. }
  assert (HST1 : PNH.hstat M1 true (PNST.st_sys g) (PNST.st_ax g)) by (apply (PNHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST)).
  (* [comment removed for export] *)
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
  pose proof CORE1 as (_ & Hcs1 & _ & _ & _ & _ & _ & _ & _ & BASE1 & _).
  assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
  assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 784) (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 1) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  unfold PMS.syscat_spec, PMSP.syscat_spec in SYS.
  apply (SYS fx1 R1 M1 model K LBc cr (sp - 784) 214132 (PNST.st_sys g) HH1).
  { repeat split; assumption. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
    split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc. }
  { exact BASE1. }
  { destruct HST1 as (_ & X & _). exact X. }
  intros fx2 R2 M2 RP2 A10s SYS2 HP2 HH2.
  set (W2 := if PNST.st_sys g then [] else [(pa_syscat_guard AD, 2)]) in *.
  assert (WC2 : forall a, PMK.inW W2 a -> PNHK.sys_dom a).
  { intros a (r & Hin & Hr). unfold W2 in Hin. destruct (PNST.st_sys g); [destruct Hin|]. destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn in Hr. unfold PNHK.sys_dom. lia. }
  assert (EK2 : PMK.ek L LBc (sp - 784) (PMSP.pm_scr 1) W2 M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (WSTD2 : forall a, PMK.inW W2 a -> PNH.fb sp <= a \/ 65536 <= a < 958464) by (intros a I; apply WC2 in I; unfold PNHK.sys_dom in I; right; lia).
  assert (CORE2 : PNH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model).
  { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model LBc (PMSP.pm_scr 1) W2 CORE1 RP2 HP2);
      [unfold LBc, LBX; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
    intros a I. right. apply WC2 in I. unfold PNHK.sys_dom in I. exists (0xc7210, 2). split; [unfold WF, PNST.pn_foot, pm_foot; cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (OB2 : PNHK.hobjs sp M2 s s2 sm p0).
  { apply (PNHK.hobjs_call L LY sp LBc (PMSP.pm_scr 1) W2 M1 M2 EK2 STKc SC1 BRc WSTD2 s s2 sm p0); [|exact INCo|exact OB1].
    intros a I. apply WC2 in I. unfold PNHK.sys_dom in I. unfold PNH.fb, FRAME. lia. }
  assert (C0b : L5.u32_at RSEGS M2 (sp - 768) 0).
  { eapply (PNHK.u32_keep L LY sp LBc (PMSP.pm_scr 1) W2 M1 M2 EK2 STKc SC1); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact C0].
    intros i Hi I. apply WC2 in I. unfold PNHK.sys_dom in I. lia. }
  assert (C1b : L5.u64_at RSEGS M2 (sp - 328) (sp - 320)).
  { eapply (PNHK.u64_keep L LY sp LBc (PMSP.pm_scr 1) W2 M1 M2 EK2 STKc SC1); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact C1].
    intros i Hi I. apply WC2 in I. unfold PNHK.sys_dom in I. lia. }
  assert (HST2 : PNH.hstat M2 true true (PNST.st_ax g)).
  { destruct HST1 as (X1 & _ & X3). split; [|split; [exact SYS2|]].
    - apply (PNHK.loc_keep L LY LBc (sp - 784) (PMSP.pm_scr 1) W2 M1 M2 EK2); [|exact X1]. intros a I D. apply WC2 in I. unfold PNHK.sys_dom in I. unfold PNHK.loc_dom in D. lia.
    - apply (PNHK.err_keep L LY LBc (sp - 784) (PMSP.pm_scr 1) W2 M1 M2 EK2); [|exact X3]. intros a I D. apply WC2 in I. unfold PNHK.sys_dom in I. unfold PNHK.err_dom in D. lia. }
  (* [comment removed for export] *)
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model CORE2) as (_ & Rsp2 & _ & _ & WR2 & STK2).
  LeanFeed.pfeed PE (PNSHP.bhnE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PE as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1e & A10e & C2)); PMK.pvz_clrT.
  set (PE := fun a => sp - 760 <= a < sp - 760 + 8).
  assert (PFE : forall a, PE a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a X; unfold PE in X; unfold PNH.fb, FRAME; lia).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr M2 model fx2 fx3 R2 0x34474 R3 0x35e4c M3 PE K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3).
  { intros a Pa. apply PFE in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
  { intros a. apply PMK.rng_dec. }
  intros HH3.
  assert (CORE3 : PNH.hcore L R0 M0 model0 sp ra LB0 R3 M3 model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R2 M2 model R3 M3 PE CORE2 MG3 FRZ3); [intros a X; unfold PE in X; unfold PNH.fb, FRAME; lia| rewrite (KS3 2%nat) by PMK.inl; exact Rsp2|].
    intros k Hk. apply KS3. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
  assert (OB3 : PNHK.hobjs sp M3 s s2 sm p0).
  { apply (PNHK.hobjs_piece L sp LBc M2 M3 PE (65536 - 784) FRZ3 PFE STK2 SCx BRc s s2 sm p0); [|exact INCo|exact OB2]. intros a X; unfold PE in X; unfold PNH.fb, FRAME; lia. }
  assert (HST3 : PNH.hstat M3 true true (PNST.st_ax g)) by (apply (PNHK.hstat_piece L LY sp LBc M2 M3 PE FRZ3 PFE true _ _ STK2 LBhic HST2)).
  assert (C0c : L5.u32_at RSEGS M3 (sp - 768) 0) by (apply (PNHK.u32_keep_p M2 M3 PE FRZ3); [lia|lia| intros i Hi X; unfold PE in X; lia| exact C0b]).
  assert (C1c : L5.u64_at RSEGS M3 (sp - 328) (sp - 320)) by (apply (PNHK.u64_keep_p M2 M3 PE FRZ3); [lia|lia| intros i Hi X; unfold PE in X; lia| exact C1b]).
  rewrite L5K.rl10 in A10s. rewrite A10s, L5.unsigned_lit in C2 by (cbn; lia).
  (* [comment removed for export] *)
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R3 M3 model CORE3) as (_ & Rsp3 & _ & _ & _ & STK3).
  pose proof CORE3 as (_ & Hcs3 & _).
  assert (STKr : L5C.stk (hl_sptop L) M3 (sp - 784) (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M3 (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 1) STK3); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  destruct OB3 as (VS3 & IA3 & PA3 & VV3).
  unfold PNRS.reset_spec, PNR.reset_spec in RST.
  apply (RST fx3 R3 M3 model K LBX cr (sp - 784) 214144 (sp - 784) p0 HH3).
  { repeat split; assumption. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1e|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp3|].
    split; [rewrite (Hcs3 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs3 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKr. }
  { unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact A16f]. }
  { rewrite L5K.rl10. unfold PNR.o_p, PMSP.o_p. cbn [pa_off_p AD]. replace (sp - 784 + 40) with (sp - 744) by lia. exact A10e. }
  { unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD]. exact PA3. }
  intros fx4 R4 M4 RP4 PA4 HP4 HH4.
  unfold PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *. cbn [pa_off_p pa_off_is AD] in *.
  match type of HP4 with L5C.hpres _ _ _ _ ?W _ _ => set (W4 := W) in * end.
  assert (WC4 : forall a, PMK.inW W4 a -> sp - 744 <= a < sp - 328).
  { intros a (r & Hin & Hr). unfold W4 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }
  assert (EK4 : PMK.ek L LBX (sp - 784) (PMSP.pm_scr 1) W4 M3 M4) by (apply (PMK.ek_of_hpres L); exact HP4).
  assert (BRx : PNHK.brange L LBX) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBX cr M _ HH); unfold LBc; apply incl_appr; apply incl_refl).
  assert (WSTD4 : forall a, PMK.inW W4 a -> PNH.fb sp <= a \/ 65536 <= a < 958464) by (intros a I; apply WC4 in I; left; unfold PNH.fb, FRAME; lia).
  apply (KONT fx4 R4 M4 model). unfold PNH.H4.
  assert (CORE4 : PNH.hcore L R0 M0 model0 sp ra LB0 R4 M4 model).
  { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R3 M3 model R4 M4 model LBX (PMSP.pm_scr 1) W4 CORE3 RP4 HP4);
      [unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
    intros a I. apply WC4 in I. left. unfold PNH.fb, FRAME. lia. }
  split; [exact CORE4|].
  split. { eapply (PNHK.vstr_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1 BRx WSTD4); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS3].
           - intros i Hi I. apply WC4 in I. unfold PNH.fb, FRAME in Hi. lia.
           - unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
  split; [exact SZ|].
  split. { eapply (PNHK.iss_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1 BRx WSTD4); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA3].
           - intros i Hi I. apply WC4 in I. unfold PNH.fb, FRAME in Hi. lia.
           - unfold LBX. apply incl_appl. apply incl_refl. }
  split; [exact SZ2|]. split; [exact SG|]. split; [exact ST0|].
  split. { unfold PNH.fb, FRAME. exact PA4. }
  split. { eapply (PNHK.u64_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact VV3].
           intros i Hi I. apply WC4 in I. unfold PNH.fb, FRAME in Hi. lia. }
  split. { apply (PNHK.hstat_keep L LY LBX (sp - 784) (PMSP.pm_scr 1) W4 M3 M4 EK4); [|exact HST3]. intros a I. apply WC4 in I. left. lia. }
  split; [exact HH4|]. split; [exact CK|].
  assert (C0d : L5.u32_at RSEGS M4 (sp - 768) 0).
  { eapply (PNHK.u32_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact C0c].
    intros i Hi I. apply WC4 in I. lia. }
  assert (C2d : L5.u64_at RSEGS M4 (sp - 760) (pa_syscat_obj AD)).
  { eapply (PNHK.u64_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact C2].
    intros i Hi I. apply WC4 in I. lia. }
  assert (C1d : L5.u64_at RSEGS M4 (sp - 328) (sp - 320)).
  { eapply (PNHK.u64_keep L LY sp LBX (PMSP.pm_scr 1) W4 M3 M4 EK4 STKr SC1); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact C1c].
    intros i Hi I. apply WC4 in I. lia. }
  split.
  - unfold PMSP.ec_at, PNH.fb, FRAME. replace (sp - 784 + 16) with (sp - 768) by lia. split; [exact C0d|]. split; [replace (sp - 768 + 8) with (sp - 760) by lia; exact C2d|].
    destruct CORE4 as (_ & _ & _ & _ & _ & DFR & _). unfold PNH.fb, FRAME in DFR. apply (L5.defined_sub M4 (sp - 784) 784); [exact DFR|lia|lia].
  - unfold PNH.fb, FRAME. replace (sp - 784 + 456) with (sp - 328) by lia. replace (sp - 784 + 464) with (sp - 320) by lia. exact C1d.
Qed.

End Stage.
End PNH4.
