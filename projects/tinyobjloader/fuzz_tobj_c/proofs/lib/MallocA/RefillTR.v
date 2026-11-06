(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "pair"; "app"; "nil"; "bool"; "cons"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "liftKA"; "ok_frameA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "w_cfg"; "w_tr"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "SLit"; "ss_objs"; "DZero"; "agree_below"; "cell"; "holds"; "mkObj"; "smatch"; "sprop"; "ss_facts"; "ss_next"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "entailsA"; "la_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR.TRS"; "TRok"; "JK"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Numbers.BinNums"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA MmapA MmapFixedA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Iface EnsureMapA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section TRS.
Let segs : list Segment := segsA.
Variable Kc : KcA.

Definition JK (J : jpredA) : Prop := ltac2:(tb__ "0|0|
S11S0S1eQ40A1A1S0S2fA1S2eVJ;R4R3R2R1A4VKc;R3R2A2F_;Fmd;Ftr;Ft;Fr;").

Definition memset_post (C : axst) (s : wsub) (R : list sobj) : axst := ltac2:(tb__ "0|0|
S3bVs;S37S36S3cS38A1A1VC;VR;A5").

Definition commit_post (A : axst) (eb : sv) (nlit : Z) : axst := ltac2:(tb__ "0|1|
S22VA;S39S1fVA;A1M0Veb;S2S12S14G0A1S5S12S19Veb;S13Z0A1S13Vnlit;A1S3S17A1S15A5S3S12A1A3A3S1dG0A1A4A2").

Record TRok (TR : assn -> assn -> Prop) : Prop := mkTRok {
  tr_pre : forall (P P' Q : assn), (forall w, P' w -> P w) -> TR P Q -> TR P' Q;
  tr_post : forall (P Q Q' : assn), (forall w, Q w -> Q' w) -> TR P Q -> TR P Q';
  tr_ex : forall (X : Type) (F : X -> assn) (Q : assn), (forall x, TR (F x) Q) -> TR (fun w => exists x, F x w) Q;
  tr_run : forall fuel cuts A leaves (J : jpredA) rho tp (Q : assn),
    JK J -> stableA segs (ss_next (ax_S A)) J ->
    sym_runA segs fuel cuts A true = Some leaves -> ss_lenient (ax_S A) = false ->
    (forall L rho', In L leaves -> agree_below (ss_next (ax_S A)) rho rho' -> TR (SPA segs J (la_state L) rho' tp) Q) ->
    TR (SPA segs J A rho tp) Q;
  tr_commit : forall (J Jo : jpredA) A rho tp (eb : sv) (nlit : Z) (Q : assn),
    JK J -> stableA segs (ss_next (ax_S A)) J ->
    instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
    reg_sv (ax_S A) 17 = SLit 222 ->
    reg_sv (ax_S A) 10 = eb -> sv_below (ss_next (ax_S A)) eb = true ->
    reg_sv (ax_S A) 11 = SLit nlit -> reg_sv (ax_S A) 12 = SLit 3 -> reg_sv (ax_S A) 13 = SLit 50 ->
    reg_sv (ax_S A) 14 = SLit 18446744073709551615 -> reg_sv (ax_S A) 15 = SLit 0 ->
    nlit mod 4096 = 0 -> 0 < nlit < 2 ^ 62 ->
    (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
       let a := eval rho eb in let ua := bv_unsigned a in
       ua mod 4096 = 0 /\ 0 < ua /\ ua + nlit <= alloc_top (m_vmmaps md)
       /\ region_free (vm_reserved (m_vmmaps md)) a (Z_to_bv 64 nlit) = true
       /\ map_contains (vm_maps (m_vmmaps md)) a (Z_to_bv 64 nlit) = true
       /\ overlap_sum (vm_maps (m_vmmaps md)) ua (ua + nlit) <= nlit
       /\ headroom md tp >= nlit
       /\ (forall o, In o (ss_objs (ax_S A)) -> ranges_disjoint (obj_range rho o) (ua, ua + nlit))
       /\ (forall x : word, ua <= bv_unsigned x < ua + nlit -> ro_addr segs x = false)
       /\ (forall rr y, In rr (ax_X A) ->
             bv_unsigned (eval rho (fst rr)) <= y < bv_unsigned (eval rho (fst rr)) + bv_unsigned (eval rho (snd rr)) ->
             ~ (ua <= bv_unsigned (shadow_addr (bv_unsigned (eval rho (ax_base A))) y) < ua + nlit))
       /\ Jo rho tp tr (vm_forget_range ua (ua + nlit) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) a (Z_to_bv 64 nlit)) md))) ->
    TR (SPA segs Jo (commit_post A eb nlit) rho tp) Q ->
    TR (SPA segs J A rho tp) Q;
  tr_memset : forall (J : jpredA) (C : axst) (s : wsub) (R : list sobj) rho tp (Q : assn),
    JK J -> stableA segs (ss_next (ax_S C)) J -> (NF <= ss_next (ax_S C))%positive ->
    entails_frA C Pre_memsetA s = Some R ->
    call_checkA C Pre_memsetA s R (map la_state Posts_memsetA) = true ->
    (forall rho' tpL, agree_below (ss_next (ax_S C)) rho rho' -> TR (SPA segs J (memset_post C s R) rho' tpL) Q) ->
    TR (SPA segs J C rho tp) Q
}.

Lemma tr_cut : forall TR, TRok TR -> forall (X : Type) (P : assn) (F : X -> assn) (Q : assn),
  (forall w, P w -> exists x, F x w) -> (forall x, TR (F x) Q) -> TR P Q.
Proof. intros TR H X P F Q HP HF. apply (tr_pre TR H (fun w => exists x, F x w) P Q HP). apply (tr_ex TR H). exact HF. Qed.

Lemma tr_pure : ltac2:(tb__ "0|1|
ScScOF_;F_;S2bR1A1OScScSdR3R1A1R5F_;Fw;R4R7R4R3A2M0F_;G0F_;F_;FQ;FP;FX;F_;FTR;").
Proof.
  intros TR H X P Q HX HT. apply (tr_cut TR H X P (fun _ => P) Q).
  - intros w Hw. exists (HX w Hw). exact Hw.
  - exact HT.
Qed.

Lemma tr_facts : ltac2:(tb__ "0|1|
ScScOF_;F_;S2bR1A1S7S20S11S0S1eQ40A1A1ScS33S1bS18R3A1S1cS1fR4A1A1A3R8S8Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FA;FJ;F_;FTR;").
Proof. intros TR H J A rho tp Q HT. apply (tr_pure TR H _ _ _ (fun w Hw => SPA_facts_hold segs J rho A tp w Hw)). exact HT. Qed.

Lemma JK_okf : ltac2:(tb__ "0|0|
SdOF_;S7SaVsegs;R2S9VKc;A1A3S2cR2A1SaVsegs;R4R3A3F_;F_;FJ;Fok;").
Proof. intros ok J Hokl HJK rho tp tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokl rho tp tr ms md msv' (HJK _ _ _ _ HJ) HMI Hh Hp Hs). Qed.
Lemma JK_okp : ltac2:(tb__ "0|0|
SdOF_;S7S28Vsegs;R2S9VKc;A1A3S2cR2A1S28Vsegs;R4R3A3F_;F_;FJ;Fok;").
Proof. intros ok J Hokp HJK rho tp tr ms md x8 HJ Hp Ho. exact (Hokp rho tp tr ms md x8 (HJK _ _ _ _ HJ) Hp Ho). Qed.

Lemma LQA_elimT : ltac2:(tb__ "0|0|
SdOF_;S7S34S11S0S1eQ40A1A1S0S21A1ScS21S11S3dS21R2R4A3S16R8R7R2A3S10Vsegs;RbS8Vsegs;RaS24R4A1R3R7A5R5A4F_;F_;Frho';FL;S10Vsegs;R8SbVsegs;R7R6R5R4R3A6R2A4F_;FQ;Fleaves;Ftp;Frho;Fn;FJ;Fok;").
Proof.
  intros ok J n rho tp leaves Q H. unfold LQA.
  apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros Hin. apply triple_pure; intros Hag. exact (H L rho' Hin Hag).
Qed.

Theorem TRok_triple : ltac2:(tb__ "0|1|
SdOF_;SaVsegs;R1S9VKc;A1M0A3S28Vsegs;R2G0A3S2bS10Vsegs;R3A2A1F_;F_;Fok;").
Proof.
  intros ok Hokl Hokp. constructor.
  - intros P P' Q HP HT. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros P Q Q' HQ HT. eapply triple_conseq; [intros w Hw; exact Hw | exact HQ | exact HT].
  - intros X F Q HF. apply triple_ex. exact HF.
  - intros fuel cuts A leaves J rho tp Q HJK Hst Hrun Hl HL.
    eapply triple_seq; [apply triple1_triple; eapply sym_run_soundA; [exact Hrun | exact (JK_okf ok J Hokl HJK) | exact Hl | exact Hst]|].
    apply LQA_elimT. exact HL.
  - intros J Jo A rho tp eb nlit Q HJK Hst Hi H17 H10 Hbel H11 H12 H13 H14 H15 Hmod Hn HJ HT.
    eapply triple_seq; [apply triple1_triple; exact (triple1_fixed_commitA segs ok J Jo A rho tp eb nlit (JK_okf ok J Hokl HJK) (JK_okp ok J Hokp HJK) Hst Hi H17 H10 Hbel H11 H12 H13 H14 H15 Hmod Hn HJ)|].
    exact HT.
  - intros J C s R rho tp Q HJK Hst HNF He Hchk HT.
    set (Jf := (fun (_ : valuation) t tr md => J rho t tr md) : jpredA).
    assert (Jf_okf : ok_frameA segs ok Jf).
    { intros r t tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokl rho t tr ms md msv' (HJK _ _ _ _ HJ) HMI Hh Hp Hs). }
    assert (Jf_st : stableA segs NF Jf).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply Hst; [apply agree_below_refl | exact Hme | exact HJ]. }
    apply (call_soundA segs ok J Jf Jf J C Pre_memsetA s R Posts_memsetA Q rho tp He Hchk).
    + intros rho1 tp1. exact (memset_sumA ok Jf rho1 tp1 Jf_okf Jf_st).
    + intros tr ms md Hsm HJ. exact HJ.
    + intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
      eapply Hst; [exact (proj1 HLK) | apply mat_equiv_refl | exact HJ'].
    + intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. exact (HT rho' tpL Hag).
Qed.

Theorem TRok_etriple : TRok (etriple segs).
Proof.
  constructor.
  - intros P P' Q HP HT. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros P Q Q' HQ HT. eapply etriple_conseq; [intros w Hw; exact Hw | exact HQ | exact HT].
  - intros X F Q HF. apply etriple_ex. exact HF.
  - intros fuel cuts A leaves J rho tp Q HJK Hst Hrun Hl HL w Hsp.
    destruct (sym_run_completeA segs fuel cuts A leaves J rho tp w Hl Hst Hrun Hsp) as (L & rho' & w' & Hin & Hst' & Hag & Hsp').
    destruct (HL L rho' Hin Hag w' Hsp') as (w'' & Hst'' & HQ).
    exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
  - intros J Jo A rho tp eb nlit Q HJK Hst Hi H17 H10 Hbel H11 H12 H13 H14 H15 Hmod Hn HJ HT.
    eapply etriple_seq; [exact (etriple_fixed_commitA segs J Jo A rho tp eb nlit Hst Hi H17 H10 Hbel H11 H12 H13 H14 H15 Hmod Hn HJ)|].
    exact HT.
  - intros J C s R rho tp Q HJK Hst HNF He Hchk HT.
    set (Jf := (fun (_ : valuation) t tr md => J rho t tr md) : jpredA).
    assert (Jf_st : stableA segs NF Jf).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply Hst; [apply agree_below_refl | exact Hme | exact HJ]. }
    apply (call_completeA segs J Jf Jf J C Pre_memsetA s R Posts_memsetA Q rho tp He Hchk).
    + intros rho1 tp1. exact (memset_sumA_ex Jf rho1 tp1 Jf_st).
    + intros tr ms md Hsm HJ. exact HJ.
    + intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
      eapply Hst; [exact (proj1 HLK) | apply mat_equiv_refl | exact HJ'].
    + intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. exact (HT rho' tpL Hag).
Qed.

Lemma SPA_entails_J : ltac2:(tb__ "0|0|
S7S7S20S20S32S11S0S1eQ40A1A1SdS2dS4S23R6R5R4A3S6A3R9R4R3SfR2A1S25SeR2A1A1A4R9S31R5R6A2R4SfR3A1S25SeR3A1A1A4F_;S8Vsegs;RaR8R5R4R3A6S8Vsegs;RaR8S31R6R7A2R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fs;FT;FL;FJ';FJ;").
Proof. intros J J' L T s rho tp w He HJ [Hsm Hk]. split; [eapply smatchA_entails; eauto | exact (HJ Hk)]. Qed.

Lemma SPA_J : ltac2:(tb__ "0|0|
S7S7S20S11S0S1eQ40A1A1SdR6R3R2SfR1A1S25SeR1A1A1A4R6R4R3SfR2A1S25SeR2A1A1A4F_;S8Vsegs;R7R5R4R3R2A6S8Vsegs;R7R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;FJ';FJ;").
Proof. intros J J' A rho tp w HJ [Hsm Hk]. split; [exact Hsm | exact (HJ Hk)]. Qed.

Lemma SPA_unobj_J : ltac2:(tb__ "0|2|
S7S7S11S20S0S12A1M0G0S0S1eQ40A1A1S0S2fA1M1S35S2eS2dG0S14S1fR7A1A1S2S12R6R5A3A3S8Vsegs;RbR8R9R5S1G1S26R4S27R3R2A2A4A6S1aVsegs;RaS1fR9A1S1G1S26R5S27S29R3R6R4A3S2aR3A1A2A4A4RdRbR7R6R4A4RdS30RcR9S29R5R8R6A3A3R8R7R5A4F_;F_;S8Vsegs;RcS22RaS3aS1fRaA1R9A2A2S30RbR8S29R4R7R5A3A3R7S1G1S26R6S27R5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;FR;Fobjs;FA;Frho;FJ';FJ;").
Proof.
  intros J J' rho A objs R tp tr ms md Ho HS HJ.
  set (rho' := rho_absorb rho R (vms md tp ms)).
  set (Jc := (fun (_ : valuation) (t : list word) (tr' : list event) (md' : Model) => J' rho' t tr' md') : jpredA).
  assert (H0 : SPA segs Jc A rho tp (tr, mkCfg ms md)).
  { destruct HS as [Hsm Hk]. split; [exact Hsm|]. unfold Jc. apply HJ; [|exact Hk]. exact (proj1 Hsm). }
  pose proof (SPA_unobj segs Jc rho A objs R tp tr ms md Ho H0 (fun k => k)) as H1. cbn zeta in H1.
  destruct H1 as [Hsm1 Hk1]. split; [exact Hsm1 | exact Hk1].
Qed.

Lemma tr_cutP : forall TR, TRok TR -> forall (X : Type) (P : assn) (G : X -> Prop) (F : X -> assn) (Q : assn),
  (forall w, P w -> exists x, G x /\ F x w) -> (forall x, G x -> TR (F x) Q) -> TR P Q.
Proof.
  intros TR H X P G F Q HP HF. apply (tr_cut TR H X P (fun x w => G x /\ F x w) Q HP).
  intros x. apply (tr_pure TR H (G x)); [intros w [Hg _]; exact Hg|]. intros Hg.
  apply (tr_pre TR H (F x)); [intros w [_ Hw]; exact Hw | exact (HF x Hg)].
Qed.

End TRS.
