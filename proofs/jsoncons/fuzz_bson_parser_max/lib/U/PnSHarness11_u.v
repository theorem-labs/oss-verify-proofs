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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u PnSHarnessKit_u PnSHarnessP_u Bs0_code_344b8_344bc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH11.
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
Hypothesis Hsp0 : getr R0 (reg 2) = Z_to_bv 64 sp.
Hypothesis Hra : L5.ra_ok ra.


(* [comment removed for export] *)
Definition H9 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (be : PNST.bax) : Prop :=
  (exists Rm, PNH.hcore L R0 M0 model0 sp ra LB0 Rm M model)
  /\ getr R (reg 1) = Z_to_bv 64 ra /\ getr R (reg 2) = Z_to_bv 64 sp /\ getr R (reg 8) = getr R0 (reg 8) /\ getr R (reg 10) = Z_to_bv 64 0
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ PNH.hstat M true true be /\ PNST.bax_le (PNST.st_ax g) be
  /\ hi_heap HI LB0 cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr (PNH.P0 L n) PMSP.cr0.

Lemma s_gone :
  PMS.opdel_spec L HI ->
  forall (fx : FPState) R M model cr s be K,
    PNH.H10 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s be -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1,
        H9 R1 M1 model1 cr be ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x348c0 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34894 M model) K.
Proof using All.
  intros OPD fx R M model cr s be K (CORE & VS & HST & EMONO & HH & CK) K0 KONT. unfold PNH.hcore in CORE.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & SRA & SS0 & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  unfold PNH.fb, FRAME in VS, SRA, SS0.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as Hs0. change (bv_modulus 64) with (2 ^ 64) in Hs0.
  assert (ES0 : Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) = getr R0 (reg 8)) by (apply Z_to_bv_bv_unsigned).
  set (s0v := bv_unsigned (getr R0 (reg 8))) in *.
  destruct Hra as (Hra1 & Hra2).
  destruct VS as (SD & _ & VS). destruct s as [ns | c ns p].
  - (* [comment removed for export] *)
    destruct VS as (Hns & SB0).
    pose proof (PMF.even_byte ns) as EVB.
    LeanFeed.pfeed P (PNSHP.bhnMs_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => 2 * ns | 38%nat => ra | 39%nat => s0v | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A2 & A8 & A10)); PMK.pvz_clrT.
    assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x34894 R1 0x348c0 M K Mh Ml MS).
    apply (KONT fx1 R1 M model). unfold H9. cbn [PM.vs_own app] in HH.
    split; [exists R; exact CORE|]. split; [exact A1|]. split; [exact A2|]. split; [rewrite A8; exact ES0|]. split; [exact A10|].
    split. { intros k Hk. rewrite <- (Hcs k Hk). apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    split; [exact HST|]. split; [exact EMONO|]. split; [exact HH| exact CK].
  - (* [comment removed for export] *)
    destruct VS as (SW0 & SW8 & SW16 & Hns & Hc & Hc2 & SBP & _).
    set (LBc := PM.vs_own (PM.VLong c ns p) ++ LB0) in *.
    assert (Bt : In (p, c) LBc) by (unfold LBc, PM.vs_own; cbn; auto).
    assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
    pose proof (PMF.u8_of_u64 RSEGS M _ _ Hc64 SW0) as SB0.
    pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
    set (vb := (c + 1) mod 256) in *.
    assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
    destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
    assert (Hp47 : p < 2 ^ 47) by lia.
    LeanFeed.pfeed P (PNSHP.bhnMl_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => vb | 37%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10)); PMK.pvz_clrT.
    assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x34894 R1 0x56720 M K Mh Ml MS).
    assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M model).
    { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE MG); [intros a Ha _; reflexivity| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
      intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
    pose proof CORE1 as (_ & Hcs1 & _).
    assert (STKd : L5C.stk (hl_sptop L) M (sp - 784) PMSP.OPDEL_SCR).
    { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
    unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
    apply (OPD fx1 R1 M model K LBc cr p c (sp - 784) 215216 HH).
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
    assert (ELB : lb_remove p LBc = LB0).
    { unfold LBc, PM.vs_own. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
    rewrite ELB in HP, HH2.
    assert (EKd : PMK.ek L LB0 (sp - 784) PMSP.OPDEL_SCR [] M M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
    assert (CORE2 : PNH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model2).
    { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 LB0 PMSP.OPDEL_SCR [] CORE1 RP HP);
        [apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
      intros a I. destruct (N0 a I). }
    assert (HST2 : PNH.hstat M2 true true be).
    { apply (PNHK.hstat_keep L LY LB0 (sp - 784) PMSP.OPDEL_SCR [] M M2 EKd); [|exact HST]. intros a I. destruct (N0 a I). }
    (* [comment removed for export] *)
    pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model2 CORE2) as (_ & Rsp2 & _ & _ & WR2 & _).
    pose proof CORE2 as (_ & Hcs2 & SRA2 & SS02 & _ & _ & _ & _ & _ & _ & _ & (Mh2 & Ml2 & Mm2)).
    unfold PNH.fb, FRAME in SRA2, SS02. fold s0v in SS02.
    LeanFeed.pfeed PN (PNSHP.bhnN_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 38%nat => ra | 39%nat => s0v | _ => 0 end)) ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PN as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1n & A2n & A8n & A10n)); PMK.pvz_clrT.
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FR3). subst M3.
    apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x348b0 R3 0x348c0 M2 K Mh2 Ml2 MS3).
    apply (KONT fx3 R3 M2 model2). unfold H9.
    split; [exists R2; exact CORE2|]. split; [exact A1n|]. split; [exact A2n|]. split; [rewrite A8n; exact ES0|]. split; [exact A10n|].
    split. { intros k Hk. rewrite <- (Hcs2 k Hk). apply KS3. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
    split; [exact HST2|]. split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.

Lemma not_foot_outside a : ~ in_foot (PNTS.TopLay L) a -> L5.outside WF a.
Proof.
  intros N r Hin Hr. apply N. unfold WF in Hin. apply in_map_iff in Hin. destruct Hin as (iv & <- & Hiv).
  exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia.
Qed.

Lemma stage11 (payload : list byte) :
  n = Z.of_nat (length payload) ->
  PMS.opdel_spec L HI ->
  forall (fx : FPState) R M model cr s be K,
    PNH.H10 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s be -> K [] ->
    (forall (fx' : FPState) (g' : PNST.st) R' M' model' cr',
        lib_post (PNTS.TopLay L) PNTS.TopLS g' LB0 cr0 sp payload R0 M0 R' M' cr' ->
        hi_heap HI LB0 cr' M' (m_vmmaps model') -> model_but_vm model0 model' ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34894 M model) K.
Proof using All.
  intros EN OPD fx R M model cr s be K H8 K0 KONT.
  apply (s_gone OPD fx R M model cr s be K H8 K0).
  clear fx R M model H8. intros fx R M model ((Rm & CORE) & A1 & A2 & A8 & A10 & KSR & HST & EMONO & HH & CK).
  destruct CORE as (_ & _ & _ & _ & STK & DFR & SPT & EK & LBhi & BASE & MB & (Mh & Ml & Mm)).
  destruct Hra as (Hra1 & Hra2).
  unfold PMSP.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x348c0 W_3455c ra F_3455c ltac:(reflexivity) D_3455c A1 Hra1 Hra2)|].
  apply (KONT fx (PNST.ST true true be) R M model cr); [|exact HH|exact MB].
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PNTS.pot_callB_le L n LY Hn) as (PC1 & PC2).
  constructor.
  - rewrite <- L5K.rl10 in A10. exact A10.
  - apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
    destruct Hk as [<-|Hk]; [rewrite A2, Hsp0; reflexivity|].
    destruct Hk as [<-|Hk]; [apply KSR; unfold CSK; cbn; auto|].
    destruct Hk as [<-|Hk]; [apply KSR; unfold CSK; cbn; auto|].
    destruct Hk as [<-|Hk]; [exact A8|].
    apply KSR. unfold CSK. cbn. tauto.
  - cbn [ll_credit PNTS.TopLay]. rewrite <- EN. unfold PMSP.credit_keep, PMSP.cr0, PNH.P0 in CK. unfold LibIface.credit_le, LibIface.credit_sub, PNTS.TOPK, PNTS.TOPB. cbn [fst snd] in *.
    unfold PMF.credit_le in *. cbn [fst snd] in *. unfold PNTS.TOPK, PNTS.TOPB in PC1, PC2. clear - CK PC1 PC2. lia.
  - cbn [ll_heap ll_stack PNTS.TopLay]. intros a Ha CA NF NE. apply EK. split; [exact Ha|]. split; [exact CA|]. split; [exact NE|]. apply not_foot_outside. exact NF.
  - cbn [ll_heap ll_stack PNTS.TopLay]. intros a Ha. unfold PNH.fb, FRAME, SCR in *. destruct STK as (_ & _ & _ & _ & DS).
    destruct (Z_lt_ge_dec a (sp - 784)) as [X|X].
    + replace a with (sp - 784 - (65536 - 784) + (a - (sp - 65536))) by lia. apply DS. lia.
    + replace a with (sp - 784 + (a - (sp - 784))) by lia. apply DFR. lia.
  - destruct HST as (H1 & H2 & H3). split; [exact BASE|]. split; [exact H1|]. split; [exact H2| exact H3].
Qed.

End Stage.
End PNH11.
