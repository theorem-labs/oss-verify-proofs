(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u PnSHarnessKit_u PnSHarnessP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH8.
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


Lemma stage8 :
  PMS.opdel_spec L HI ->
  forall (fx : FPState) R M model cr s s2 src bb nb sm ax K,
    PNH.H7 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 src bb nb sm ax -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        PNH.H8 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr s s2 src bb sm ax ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34800 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x347e4 M model) K.
Proof using All.
  intros OPD fx R M model cr s s2 src bb nb sm ax K (CORE & VS & SZ & IA & SRC & NI & BBS & XS & HST & EMONO & HH & CK) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  unfold PNH.fb, FRAME in XS.
  destruct nb as [nt | c nt p].
  - (* [comment removed for export] *)
    destruct XS as (TBD & _ & (Hnt & TB0)).
    pose proof (PMF.even_byte nt) as EVB.
    LeanFeed.pfeed P (PNSHP.bhnQs_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => 2 * nt | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A10)); PMK.pvz_clrT.
    assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x347e4 R1 0x34800 M K Mh Ml MS).
    apply (KONT fx1 R1 M model). unfold PNH.H8.
    split. { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE MG); [intros a Ha _; reflexivity| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
             intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    cbn [PM.vs_own app] in HH. rewrite ?app_nil_r in HH.
    repeat (split; [assumption|]). assumption.
  - (* [comment removed for export] *)
    destruct XS as (TBD & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
    set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
    set (LBc := PM.src_own src ++ PGV8.v8_own bb ++ PM.vs_own (PM.VLong c nt p) ++ LBX) in *.
    set (LB7 := PM.src_own src ++ PGV8.v8_own bb ++ LBX).
    assert (Bt : In (p, c) LBc) by (unfold LBc; rewrite !in_app_iff; cbn [PM.vs_own In]; auto 10).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
    pose proof (PMF.u8_of_u64 RSEGS M _ _ Hc64 TW0) as TB0.
    pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
    set (vb := (c + 1) mod 256) in *.
    assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
    destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
    assert (Hp47 : p < 2 ^ 47) by lia.
    LeanFeed.pfeed P (PNSHP.bhnQl_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => vb | 37%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10)); PMK.pvz_clrT.
    assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x347e4 R1 0x56720 M K Mh Ml MS).
    assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M model).
    { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE MG); [intros a Ha _; reflexivity| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
      intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
    pose proof CORE1 as (_ & Hcs1 & _).
    assert (STKd : L5C.stk (hl_sptop L) M (sp - 784) PMSP.OPDEL_SCR).
    { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
    unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
    apply (OPD fx1 R1 M model K LBc cr p c (sp - 784) 215040 HH).
    { repeat split; assumption. }
    { exact K0. }
    { exact Bt. }
    { rewrite L5K.rl10. exact A10. }
    { rewrite L5K.rl1. exact A1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. exact Rsp1. }
    { rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
    { exact STKd. }
    intros fx2 R2 M2 model2 RP HP MB HH2.
    assert (ELB : lb_remove p LBc = LB7).
    { pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LBc cr M _ HH))) as ND.
      unfold LBc, LB7. apply (PNHK.lb_remove_mid2 p c); exact ND. }
    rewrite ELB in HP, HH2.
    assert (EKd : PMK.ek L LB7 (sp - 784) PMSP.OPDEL_SCR [] M M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
    assert (BR7 : PNHK.brange L LB7) by (apply (PNHK.brange_of_heap L HI LY HIok LB7 LB7 cr M2 _ HH2); apply incl_refl).
    assert (WSTD : forall a, PMK.inW [] a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a (r & [] & _)).
    assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
    apply (KONT fx2 R2 M2 model2). unfold PNH.H8.
    split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 LB7 PMSP.OPDEL_SCR [] CORE1 RP HP);
               [unfold LB7, LBX; repeat apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
             intros a I. destruct (N0 a I). }
    split. { eapply (PNHK.vstr_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
             - intros i _. apply N0.
             - intros x Hx; unfold LB7, LBX; rewrite !in_app_iff; auto 12. }
    split; [exact SZ|].
    split. { eapply (PNHK.iss_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA].
             - intros i _. apply N0.
             - intros x Hx; unfold LB7, LBX; rewrite !in_app_iff; auto 12. }
    split. { eapply (PNHK.src_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact SRC].
             - intros i _. apply N0.
             - unfold LB7, PM.src_own. cbn. auto. }
    split. { eapply (PNHK.nullis_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact NI]. intros i _. apply N0. }
    split. { eapply (PNHK.v8_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact BBS].
             - intros i _. apply N0.
             - intros x Hx; unfold LB7, LBX; rewrite !in_app_iff; auto 12. }
    split. { apply (PNHK.hstat_keep L LY LB7 (sp - 784) PMSP.OPDEL_SCR [] M M2 EKd); [|exact HST]. intros a I. destruct (N0 a I). }
    split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.

End Stage.
End PNH8.
