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

Module PNH3.
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

Lemma stage3 :
  PNRS.reader_ctor_spec L HI ->
  forall (fx : FPState) R M model cr s s2 sm K,
    PNH.H2 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 sm -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1 cr1 qc b,
        PNH.H3 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr1 s s2 sm qc b ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3478c M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34748 M model) K.
Proof using All.
  intros RDR fx R M model cr s s2 sm K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & HST & HH & CK) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (_ & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & LBhi & BASE & MBV & (Mh & Ml & Mm)).
  set (LBc := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  assert (LBhic : forall b, In b LBc -> fst b + snd b <= hl_ceil L).
  { intros b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBc cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  LeanFeed.pfeed P (PNSHP.bhnC_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & A11 & A12 & A13 & C0 & C1 & C2 & C3 & C4)); PMK.pvz_clrT.
  set (P := fun a => (sp - 768 <= a < sp - 768 + 24) \/ (sp - 320 <= a < sp - 320 + 8)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
  assert (PF : forall a, P a -> PNH.fb sp <= a < PNH.fb sp + 784) by (intros a [X|X]; unfold PNH.fb, FRAME; lia).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34748 R1 0x36410 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Pa. apply PF in Pa. unfold PNH.fb, FRAME in Pa. left. lia. }
  { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PNH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
    intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
  assert (SCx : 0 <= 65536 - 784) by lia.
  assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
  assert (VS1 : PM.vstr_at RSEGS PNH.T3 M1 (PNH.fb sp + 744) s).
  { eapply (PNHK.vstr_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
    - intros i Hi [X|X]; unfold PNH.fb, FRAME in Hi; lia.
    - unfold LBc. apply incl_appr. apply incl_appl. apply incl_refl. }
  assert (IA1 : PM.iss_at RSEGS AD PNH.T3 M1 (PNH.fb sp + 472) s2 sm).
  { eapply (PNHK.iss_keep_p L sp LBc M M1 P (65536 - 784) FRZ PF STK SCx BRc); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA].
    - intros i Hi [X|X]; unfold PNH.fb, FRAME in Hi; lia.
    - unfold LBc. apply incl_appl. apply incl_refl. }
  assert (HST1 : PNH.hstat M1 true (PNST.st_sys g) (PNST.st_ax g)).
  { apply (PNHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST). }
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
  pose proof CORE1 as (_ & Hcs1 & _ & _ & _ & _ & _ & _ & _ & BASE1 & _).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PNTS.pot_callB_le L n LY Hn) as (PC1 & PC2).
  assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 784) (PMSP.pm_scr 6)).
  { apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 6) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|]. destruct STK1 as (X & _). exact X. }
  unfold PNRS.reader_ctor_spec, PNR.reader_ctor_spec in RDR.
  apply (RDR fx1 R1 M1 model K LBc cr (sp - 784) 214924 (sp - 784) (sp - 768) (sp - 769) s2 sm HH1).
  - repeat split; assumption.
  - exact K0.
  - unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
    split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc.
  - unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia|]. destruct STK1 as (X & _). exact X.
  - rewrite L5K.rl10. unfold PNR.o_p, PMSP.o_p. cbn [pa_off_p AD]. replace (sp - 784 + 40) with (sp - 744) by lia. exact A10.
  - rewrite L5K.rl11. unfold PNR.o_is, PMSP.o_is. cbn [pa_off_is AD]. replace (sp - 784 + 472) with (sp - 312) by lia. exact A11.
  - rewrite L5K.rl12. exact A12.
  - rewrite L5K.rl13. exact A13.
  - lia.
  - unfold PNR.o_p, PMSP.o_p. cbn [pa_off_p AD]. lia.
  - destruct STK1 as (X & _). lia.     (* [comment removed for export] *)
  - unfold PNR.o_p, PMSP.o_p. cbn [pa_off_p AD]. pose proof CORE1 as (_ & _ & _ & _ & _ & DFR1 & _). unfold PNH.fb, FRAME in DFR1. apply (L5.defined_sub M1 (sp - 784) 784 (sp - 784 + 40) 416 DFR1); lia.
  - exact C3.
  - replace (sp - 768 + 16) with (sp - 752) by lia. exact C0.
  - unfold PNR.o_is, PMSP.o_is. cbn [pa_off_is AD]. exact IA1.
  - exact BASE1.
  - destruct HST1 as (X & _). exact X.
  - destruct CK as (CK1 & CK2). destruct Hcr0 as (C6 & C7).
    PNHK.cred_norm. lia.
  - intros fx2 R2 M2 model2 qc b cr2 RP PA HP CK2 MB HH2.
    apply (KONT fx2 R2 M2 model2 cr2 qc b). unfold PNH.H3.
    unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is, PNM.PSIZE in *. cbn [pa_off_p pa_off_is AD] in *.
    set (W' := [(sp - 784 + 40, 416)]) in *.
    assert (WC : forall a, PMK.inW W' a -> sp - 744 <= a < sp - 328).
    { intros a (r & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
    assert (EKc : PMK.ek L LBc (sp - 784) (PMSP.pm_scr 6) W' M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (SC6 : 0 <= PMSP.pm_scr 6) by (unfold PMSP.pm_scr; lia).
    assert (WSTD : forall a, PMK.inW W' a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a I; apply WC in I; left; unfold PNH.fb, FRAME; lia).
    split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LBc (PMSP.pm_scr 6) W' CORE1 RP HP);
               [unfold LBc; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
             intros a I. apply WC in I. left. unfold PNH.fb, FRAME. lia. }
    split. { eapply (PNHK.vstr_keep L LY sp LBc (PMSP.pm_scr 6) W' M1 M2 EKc STKc SC6 BRc WSTD);
               [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS1].
             - intros i Hi I. apply WC in I. unfold PNH.fb, FRAME in Hi. lia.
             - unfold LBc. apply incl_appr. apply incl_appl. apply incl_refl. }
    split; [exact SZ|].
    split. { eapply (PNHK.iss_keep L LY sp LBc (PMSP.pm_scr 6) W' M1 M2 EKc STKc SC6 BRc WSTD);
               [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA1].
             - intros i Hi I. apply WC in I. unfold PNH.fb, FRAME in Hi. lia.
             - unfold LBc. apply incl_appl. apply incl_refl. }
    split; [exact SZ2|]. split; [exact SG|]. split; [exact ST0|].
    split. { unfold PNH.fb, FRAME. exact PA. }
    split. { eapply (PNHK.u64_keep L LY sp LBc (PMSP.pm_scr 6) W' M1 M2 EKc STKc SC6); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |].
             - intros i Hi I. apply WC in I. unfold PNH.fb, FRAME in Hi. lia.
             - unfold PNH.fb, FRAME. replace (sp - 784 + 464) with (sp - 320) by lia. exact C4. }
    split. { apply (PNHK.hstat_keep L LY LBc (sp - 784) (PMSP.pm_scr 6) W' M1 M2 EKc); [|exact HST1]. intros a I. apply WC in I. left. lia. }
    split; [exact HH2|].
    destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4).
    PNHK.cred_norm. lia.
Qed.

End Stage.
End PNH3.
