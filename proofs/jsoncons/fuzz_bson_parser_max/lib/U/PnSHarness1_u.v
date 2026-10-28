(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnLayout PnModel PnModelFacts PnStatics PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u PnSHarnessKit_u PnSHarnessP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH1.
Import PMS. Import PNH.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma CSK_in_KS (KS : list nat) : (forall k, In k CSK -> existsb (Nat.eqb k) KS = true) -> forall k, In k CSK -> In k KS.
Proof. intros H k Hk. apply L5K.In_of_mem. apply H. exact Hk. Qed.

Lemma stage1 :
  PMS.str_ctor_spec L HI ->
  forall (fx : FPState) g LB cr sp ptr ra payload R M model K,
    lib_pre (PNTS.TopLay L) PNTS.TopLS g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) -> m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1 cr1 s,
        PNH.H1 L HI R M model sp ra (Z.of_nat (length payload)) LB cr g R1 M1 model1 cr1 s ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34738 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3471c M model) K.
Proof.
  intros STR fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm K0 KONT.
  destruct PRE as [Rra RAok Rsp Rgp Rtp Ra0 Ra1 LEN PTR PAY STK CRED STAT].
  cbn [ll_heap ll_stack ll_empty ll_credit ll_gp PNTS.TopLay] in *.
  set (n := Z.of_nat (length payload)) in *.
  destruct STK as (A16 & SLO & SHI & STOP & SOK & SDEF).
  rewrite (ly_tp L LY) in Rtp. rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in Ra0. rewrite L5K.rl11 in Ra1.
  assert (STK0 : L5C.stk (hl_sptop L) M sp 65536).
  { split; [exact A16|]. split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. apply SDEF. lia. }
  pose proof (L5C.stk_writable RSEGS _ M sp 65536 STK0) as WR0.
  assert (LBhi : forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  destruct STAT as (BASE & SLOC & SSYS & SERR).
  LeanFeed.pfeed P (PNSHP.bhnA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A2 & A10 & A11 & A12 & C0 & C1)); PMK.pvz_clrT.
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x3471c R1 0x3490c M1 (fun a => sp - 16 <= a < sp - 16 + 16) K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Ha. apply (PMK.cwr_stack L LB M sp 65536 a STK0). lia. }
  { intros a. apply PMK.rng_dec. }
  intros HH1.
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 784) (65536 - 784)).
  { apply (PMK.stk_call L M1 sp 65536 (sp - 784) (65536 - 784)); [apply (L5C.stk_grows _ M M1 _ _ MG STK0)|lia|lia|lia|].
    clear - A16. replace (sp - 784) with (sp + (-49) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (EK1 : PMK.ek L LB sp 65536 [] M M1).
  { apply (PMK.ek_piece_in' RSEGS L KL LB sp 65536 [] M M1 _ FRZ); [lia|lia|exact LBhi|]. intros a Ha. left. lia. }
  assert (CORE1 : PNH.hcore L R M model sp ra LB R1 M1 model).
  { unfold PNH.hcore, PNH.fb, FRAME, SCR.
    split; [exact A2|].
    split. { intros k Hk. apply KS. revert k Hk. apply CSK_in_KS. intros k Hk. unfold CSK in Hk. cbn in Hk.
             repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]). destruct Hk. }
    split. { replace (sp - 784 + 776) with (sp - 8) by lia. rewrite Rra, L5.unsigned_lit in C1 by lia. exact C1. }
    split. { replace (sp - 784 + 768) with (sp - 16) by lia. exact C0. }
    split; [exact STK1|].
    split. { intros i Hi. apply MG. destruct STK0 as (_ & _ & _ & _ & D0). replace (sp - 784 + i) with (sp - 65536 + (64752 + i)) by lia. apply D0. lia. }
    split; [lia|].
    split. { intros a Ha. apply EK1. destruct Ha as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|]. split; [exact H3| apply L5C.outside_nil]. }
    split; [exact LBhi|].
    split. { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 65536 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil]. }
    split; [apply L5C.model_but_vm_refl| repeat split; assumption]. }
  (* [comment removed for export] *)
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
  pose proof (PNTS.pot_callB_le L n LY ltac:(lia)) as (PC1 & PC2).
  destruct CRED as (CR1 & CR2). unfold PNTS.TOPK, PNTS.TOPB in CR1, CR2. cbn [fst snd] in CR1, CR2, PC1, PC2.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (A8 : (sp - 40) mod 8 = 0).
  { clear - A16. apply Z.mod_divide in A16; [|lia]. destruct A16 as (q & ->). replace (q * 16 - 40) with ((2 * q - 5) * 8) by lia. apply Z.mod_mul. lia. }
  unfold PMS.str_ctor_spec, PMSP.str_ctor_spec in STR.
  apply (STR fx1 R1 M1 model K LB cr (sp - 40) ptr n (sp - 784) 214840 HH1).
  - repeat split; assumption.
  - exact K0.
  - unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
    split; [rewrite (KS 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS 4%nat) by PMK.inl; exact Rtp|].
    apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 0) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    destruct STK1 as (X & _). exact X.
  - rewrite L5K.rl10. exact A10.
  - rewrite L5K.rl11, A11. exact Ra0.
  - rewrite L5K.rl12, A12. exact Ra1.
  - lia.
  - lia.
  - lia.
  - exact A8.
  - destruct CORE1 as (_ & _ & _ & _ & _ & DFR1 & _). unfold PNH.fb, FRAME in DFR1. apply (L5.defined_sub M1 (sp - 784) 784 (sp - 40) 24 DFR1); lia.
  - destruct PTR as [(E0 & _)|(Hp & Hin)]; [left; unfold n; rewrite E0; reflexivity|]. right. exists ptr, n. split; [exact Hin| lia].
  - unfold PMSP.credit_le, PM.cost1. cbn [fst snd]. unfold PNR.pot_callB, PM.credit_add, PM.cost1, PNR.pot_bstack, PM.pot_text, PGV8.pot_v8, PM.CHUNK, PNM.BSZ in PC1, PC2.
    cbn [fst snd PM.vs_cap PGV8.v8_cap] in PC1, PC2. change (2 ^ 12) with 4096 in PC2. change (2 ^ (0 + 1)) with 2 in PC2. change (2 ^ 28) with 268435456 in PC2. lia.
  - intros fx2 R2 M2 model2 s cr2 RP VS SZ SH LG HP CK MB HH2.
    apply (KONT fx2 R2 M2 model2 cr2 s). unfold PNH.H1.
    assert (EKc : PMK.ek L LB (sp - 784) (PMSP.pm_scr 0) [(sp - 40, 24)] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
    split. { apply (PNHK.hcore_call L LY R M model sp ra LB R1 M1 model R2 M2 model2 LB (PMSP.pm_scr 0) [(sp - 40, 24)] CORE1 RP HP (incl_refl LB)); [unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
             intros a (r & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. left. unfold PNH.fb, FRAME. lia. }
    split. { unfold PNH.fb, FRAME. replace (sp - 784 + 744) with (sp - 40) by lia. exact VS. }
    split; [exact SZ|].
    split. { apply (PNHK.hstat_keep L LY LB (sp - 784) (PMSP.pm_scr 0) [(sp - 40, 24)] M1 M2 EKc).
             - intros a (r & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. left. lia.
             - apply (PNHK.hstat_keep L LY LB sp 65536 [] M M1 EK1); [intros a (r & [] & _)|]. split; [exact SLOC| split; [exact SSYS| exact SERR]]. }
    split; [exact HH2|].
    split. { destruct CK as (CK1 & CK2). unfold PMSP.credit_keep, PNH.P0, PNH.rest1, PNH.rest2, PNH.rest3, PNR.pot_callB, PM.credit_add, PM.cost1, PMSP.cr0 in *. cbn [fst snd] in *. lia. }
    intros c n' p E. destruct (Z_le_gt_dec n 22) as [X|X]; [rewrite (SH X) in E; discriminate| rewrite E in SZ; cbn in SZ; lia].
Qed.

End Stage.
End PNH1.
