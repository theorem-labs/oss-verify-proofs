(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u PnSHarnessKit_u PnSHarnessP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH2.
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

Lemma locW_in_WF a : PMK.inW (PMSP.loc_W AD) a -> PMK.inW WF a.
Proof.
  intros (r & Hin & Hr). unfold PMSP.loc_W in Hin. cbn in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr.
  - exists (0xc87f2, 0xc8f30 - 0xc87f2). split; [unfold WF, PNST.pn_foot, pm_foot; cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
  - exists (0xc9658, 0xc96b0 - 0xc9658). split; [unfold WF, PNST.pn_foot, pm_foot; cbn; auto 6| unfold L5.in_rng; cbn [fst snd]; lia].
Qed.

Lemma stage2 :
  PMS.iss_ctor_spec L HI ->
  forall (fx : FPState) R M model cr s K,
    PNH.H1 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1 cr1 s2 sm,
        PNH.H2 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr1 s s2 sm ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34748 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34738 M model) K.
Proof using All.
  intros ISS fx R M model cr s K (CORE & VS & SZ & (SLOC & SSYS & SERR) & HH & CK & LONG) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (_ & _ & _ & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & _ & _ & LBhi & BASE & MBV & (Mh & Ml & Mm)).
  LeanFeed.pfeed P (PNSHP.bhnB_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10 & A11 & A12)); PMK.pvz_clrT.
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok (PM.vs_own s ++ LB0) cr M model fx fx1 R 0x34738 R1 0x349d4 M1 (fun _ => False) K HH Mh Ml ltac:(lia) MS MG).
  { intros a Ha _. apply FRZ. exact Ha. }
  { intros a []. }
  { intros a. right. tauto. }
  intros HH1.
  assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 (fun _ => False) CORE MG); [intros a Ha _; apply FRZ; exact Ha| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
    intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
  assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & _).
  pose proof CORE1 as (_ & Hcs1 & _).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PNTS.pot_callB_le L n LY Hn) as (PC1 & PC2).
  assert (A8a : (sp - 312) mod 8 = 0).
  { clear - A16. apply Z.mod_divide in A16; [|lia]. destruct A16 as (q & ->). replace (q * 16 - 312) with ((2 * q - 39) * 8) by lia. apply Z.mod_mul. lia. }
  assert (A8b : (sp - 40) mod 8 = 0).
  { clear - A16. apply Z.mod_divide in A16; [|lia]. destruct A16 as (q & ->). replace (q * 16 - 40) with ((2 * q - 5) * 8) by lia. apply Z.mod_mul. lia. }
  assert (STKc : L5C.stk (hl_sptop L) M (sp - 784) (PMSP.pm_scr 4)).
  { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 4) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|]. destruct STK as (X & _). exact X. }
  pose proof CORE1 as (_ & _ & _ & _ & _ & _ & SPT & _).
  unfold PMS.iss_ctor_spec, PMSP.iss_ctor_spec in ISS.
  apply (ISS fx1 R1 M model K (PM.vs_own s ++ LB0) cr (sp - 312) (sp - 40) (sp - 784) 214856 s (PNST.st_loc g) HH1).
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
  - pose proof CORE1 as (_ & _ & _ & _ & _ & DFR1 & _). unfold PNH.fb, FRAME in DFR1. apply (L5.defined_sub M (sp - 784) 784 (sp - 312) 272 DFR1); lia.
  - unfold PNH.fb, FRAME in VS. replace (sp - 784 + 744) with (sp - 40) in VS by lia. exact VS.
  - apply incl_appl. apply incl_refl.
  - rewrite SZ. lia.
  - exact LONG.
  - destruct CORE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B & _). exact B.
  - exact SLOC.
  - destruct CK as (CK1 & CK2). destruct Hcr0 as (C1 & C2). rewrite SZ.
    clear - CK1 CK2 C1 C2 PC1 PC2 HK HB Hn. PNHK.cred_norm. lia.
  - intros fx2 R2 M2 model2 s2 sm cr2 RP IA SZ2 SG ST0 LOC2 HP CK2 MB HH2.
    apply (KONT fx2 R2 M2 model2 cr2 s2 sm). unfold PNH.H2.
    set (W' := (sp - 312, 272) :: (if PNST.st_loc g then [] else PMSP.loc_W AD)) in *.
    assert (WC : forall a, PMK.inW W' a -> (sp - 312 <= a < sp - 40) \/ PMK.inW (PMSP.loc_W AD) a).
    { intros a (r & Hin & Hr). unfold W' in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
      right. destruct (PNST.st_loc g); [destruct Hin| exists r; split; assumption]. }
    assert (WL : forall a, PMK.inW (PMSP.loc_W AD) a -> PNHK.loc_dom a).
    { intros a (r & Hin & Hr). unfold PMSP.loc_W in Hin. cbn in Hin. unfold L5.in_rng in Hr. unfold PNHK.loc_dom.
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (EKc : PMK.ek L (PM.vs_own s ++ LB0) (sp - 784) (PMSP.pm_scr 4) W' M M2) by (apply (PMK.ek_of_hpres L); exact HP).
    split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 (PM.vs_own s ++ LB0) (PMSP.pm_scr 4) W' CORE1 RP HP);
               [apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
             intros a I. destruct (WC a I) as [F|F]; [left; unfold PNH.fb, FRAME; lia| right; apply locW_in_WF; exact F]. }
    split. { apply (PNHK.vstr_keep L LY sp (PM.vs_own s ++ LB0) (PMSP.pm_scr 4) W' M M2 EKc STKc ltac:(unfold PMSP.pm_scr; lia) (PNHK.brange_of_heap L HI LY HIok _ _ cr M _ HH1 (incl_refl _)));
               [|unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |apply incl_appl; apply incl_refl|exact VS].
             - intros a I. destruct (WC a I) as [F|F]; [left; unfold PNH.fb, FRAME; lia| right; apply WL in F; unfold PNHK.loc_dom in F; lia].
             - intros i Hi I. unfold PNH.fb, FRAME in Hi. destruct (WC i I) as [F|F]; [lia| apply WL in F; unfold PNHK.loc_dom in F; lia]. }
    split; [exact SZ|].
    split. { unfold PNH.fb, FRAME. replace (sp - 784 + 472) with (sp - 312) by lia. exact IA. }
    split; [rewrite SZ2; exact SZ|].
    split. { unfold PNH.fb, FRAME. replace (sp - 784 + 552) with (sp - 312 + 80) by lia. exact SG. }
    split; [exact ST0|].
    split. { split; [exact LOC2|]. split.
             - apply (PNHK.sys_keep L LY (PM.vs_own s ++ LB0) (sp - 784) (PMSP.pm_scr 4) W' M M2 EKc); [|exact SSYS].
               intros a I D. unfold PNHK.sys_dom in D. destruct (WC a I) as [F|F]; [lia| apply WL in F; unfold PNHK.loc_dom in F; lia].
             - apply (PNHK.err_keep L LY (PM.vs_own s ++ LB0) (sp - 784) (PMSP.pm_scr 4) W' M M2 EKc); [|exact SERR].
               intros a I D. unfold PNHK.err_dom in D. destruct (WC a I) as [F|F]; [lia| apply WL in F; unfold PNHK.loc_dom in F; lia]. }
    split; [exact HH2|].
    destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4). rewrite SZ in CK3, CK4.
    clear - CKa CKb CK3 CK4 HK HB Hn. PNHK.cred_norm. lia.
Qed.

End Stage.
End PNH2.
