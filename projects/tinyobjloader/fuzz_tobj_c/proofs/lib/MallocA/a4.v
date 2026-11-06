(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From Stdlib Require NArith PArith FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.

(* [comment removed for export] *)
Module SegQlib.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "false"; "andb"; "option"; "pair"; "nil"; "Some"; "fst"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "agree_below"; "ss_next"; "holds"; "ss_facts"; "sobj"; "sprop_below"; "sprop_eqb"; "ss_pc"; "SLit"; "SPBranch"; "SVar"; "rl"; "rm"; "rw"; "sv_below"; "swf"; "SPNot"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "ok_frameA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "ax_setS"; "axwf"; "entailsA"; "sym_runA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "leaf"; "runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "sdiff"; "one_at"; "two_at"; "JQ"; "pairs_eqb"; "diffs_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "call_checkA"; "entails_frA"; "import_postA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "wsub_id_below"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "lt"; "pow"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S3eS11S11S1S13A1S14R4R3R2A3SdS2S40S13S19R5A1R2A3S3A3S42S13S16R5A1M0R3A3S42S13G0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Definition diffs_below (n : positive) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S40S4S12S12A2M0G0S6S22Vn;SbS12S12R1A3A2S22Vn;ScS12S12R1A3A2A2Lp;Vd;A3").
Lemma diffs_ok_agree : ltac2:(tb__ "0|0|
S3eS11S11S1S4S12S12A2A1SdS2S4eR4R1A2S3A3S14R5R4R3A3S46R5R3A2S46R5R4A2F_;F_;F_;Fd;Frho';Frho;Fn;").
Proof.
  intros n rho rho' d Hb Hag Hd. unfold diffs_ok in *. apply Forall_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) Hb p Hp) as B. cbn beta in B. apply andb_prop in B as [B1 B2].
  rewrite <- (eval_agree n rho rho' _ Hag B1), <- (eval_agree n rho rho' _ Hag B2). exact (proj1 (Forall_forall _ _) Hd p Hp).
Qed.

Definition one_at (l : list leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S1S2dA1M0S2Ll;Vl;S5S2dG0G0S2Ll0;R1S5cS1bS2eS2fR2A1A1A1Vpc;A2S2dG0S5Ll2;Ll1;X1x2Ll0;LL;X1x2").
Definition two_at (l : list leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S1S2dA1M0S2Ll;Vl;S5S2dG0G0S2Ll0;R1S5S2dG0G0S2Ll1;R1S6S5cS1bS2eS2fR4A1A1A1Vpc;A2S5cS1bS2eS2fR2A1A1A1Vpc;A2A2S2dG0S5Ll3;Ll2;X1x2Ll1;LL2;X1x2Ll0;LL1;X1x2").

Lemma one_at_In : ltac2:(tb__ "0|1|
S1S2dA1M0S3dS2dSdS2S4aR3R2A2S3A3S3fS2dR2R4A3SeSdS2cS2fR3A1S3bU0R5A2A3SfSdG0R5S9S2dA1A3A1A2F_;F_;FL0;Fpc;Fl;").
Proof.
  intros l pc L0 H Hin. unfold one_at in H. destruct l as [|L [|L' l']]; try discriminate H.
  destruct Hin as [<-|[]]. split; [reflexivity | discriminate].
Qed.
Lemma two_at_In : ltac2:(tb__ "0|2|
S1S2dA1M0S3dS2dSdS2S4bR3R2A2S3A3S3fS2dR2R4A3SeS10SdS2cS2fR3A1M1S3bU0R5A2A3SdS2cG1S3bU1R5A2A3A2SfSdG0R5S9S2dA1A3A1A2F_;F_;FL0;Fpc;Fl;").
Proof.
  intros l pc L0 H Hin. unfold two_at in H. destruct l as [|L1 [|L2 [|L3 l']]]; try discriminate H.
  destruct Hin as [<-|[<-|[]]]; (split; [|discriminate]); [left | right]; reflexivity.
Qed.
Lemma one_at_ne : ltac2:(tb__ "0|1|
S1S2dA1M0S3dSdS2S4aR2R1A2S3A3SfSdG0R3S9S2dA1A3A1F_;Fpc;Fl;"). Proof. intros [|L l'] pc H; [discriminate H | discriminate]. Qed.
Lemma two_at_ne : ltac2:(tb__ "0|1|
S1S2dA1M0S3dSdS2S4bR2R1A2S3A3SfSdG0R3S9S2dA1A3A1F_;Fpc;Fl;"). Proof. intros [|L l'] pc H; [discriminate H | discriminate]. Qed.

Section Runs.
Variables (fuel : nat) (cuts : list Z) (Pre : axst) (l : list leafA) (n : positive) (EA EB : axst).
Hypothesis HLEN : ltac2:(tb__ "0|0|
SdS2S25S2eVPre;A1A1S5A3").
Hypothesis HNX : ltac2:(tb__ "0|0|
SdS3eS15S2eVPre;A1A1Vn;A3").
Hypothesis RUNL : ltac2:(tb__ "0|0|
SdS1S2dA1S3cVfuel;Vcuts;VPre;A3Vl;A3").

Hypothesis HEA : leaf 0 l = EA.
Hypothesis HEB : leaf 1 l = EB.

Lemma run_some : ltac2:(tb__ "0|1|
SfSdS1S2dA1M0Vl;S9S2dA1A3A1SdS7G0A1S33S0Vfuel;Vcuts;VPre;S3A5SaG0Vl;A2A3F_;").
Proof using RUNL. intros Hne. pose proof RUNL as R. unfold runA in R. destruct (sym_runA segsA fuel cuts Pre true) as [l'|]; [congruence|]. exfalso. apply Hne. symmetry. exact R. Qed.

Theorem run_cont1 : ltac2:(tb__ "0|0|
S3dS27S38OF_;S11S1S34Q40A1A1S39SdS2S4aVl;R6A2S3A3S2aS0R5R6A3S28S0Vn;R7A3S11S14Vn;R7R1A3S37S0R9S26S0RaVEA;R2R7A5R6A4F_;FrhoE;S37S0R8S26S0R9VPre;R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA.
  intros pc J ok rho tp Q H1 HOK HST HC. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp (run_some (one_at_ne l pc H1)) HOK HLEN ltac:(rewrite HNX; exact HST)).
  - rewrite HNX. apply triple_LQA_of_leaves. intros L0 rhoE Hin Hag. rewrite (proj1 (one_at_In l pc L0 H1 Hin)), HEA. exact (HC rhoE Hag).
Qed.
Theorem run_econt1 : ltac2:(tb__ "0|0|
S3dS27S11S1S34Q40A1A1S38OF_;SdS2S4aVl;R5A2S3A3S28S0Vn;R5A3S11S14Vn;R6R1A3S36S0S26S0R8VEA;R2R6A5R5A3F_;FrhoE;S36S0S26S0R7VPre;R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA.
  intros pc J rho tp Q H1 HST HC. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN ltac:(rewrite HNX; exact HST) (run_some (one_at_ne l pc H1))).
  - rewrite HNX. apply etriple_LQA_of_leaves. intros L0 rhoE Hin Hag. rewrite (proj1 (one_at_In l pc L0 H1 Hin)), HEA. exact (HC rhoE Hag).
Qed.
Theorem run_cont2 : ltac2:(tb__ "0|0|
S3dS27S38OF_;S11S1S34Q40A1A1S39SdS2S4bVl;R6A2S3A3S2aS0R5R6A3S28S0Vn;R7A3S11S14Vn;R7R1A3S37S0R9S26S0RaVEA;R2R7A5R6A4F_;FrhoE;S11S14Vn;R8R1A3S37S0RaS26S0RbVEB;R2R8A5R7A4F_;FrhoE;S37S0R9S26S0RaVPre;R8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA HEB.
  intros pc J ok rho tp Q H2 HOK HST HC0 HC1. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp (run_some (two_at_ne l pc H2)) HOK HLEN ltac:(rewrite HNX; exact HST)).
  - rewrite HNX. apply triple_LQA_of_leaves. intros L0 rhoE Hin Hag.
    destruct (proj1 (two_at_In l pc L0 H2 Hin)) as [-> | ->]; [rewrite HEA; exact (HC0 rhoE Hag) | rewrite HEB; exact (HC1 rhoE Hag)].
Qed.
Theorem run_econt2 : ltac2:(tb__ "0|0|
S3dS27S11S1S34Q40A1A1S38OF_;SdS2S4bVl;R5A2S3A3S28S0Vn;R5A3S11S14Vn;R6R1A3S36S0S26S0R8VEA;R2R6A5R5A3F_;FrhoE;S11S14Vn;R7R1A3S36S0S26S0R9VEB;R2R7A5R6A3F_;FrhoE;S36S0S26S0R8VPre;R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA HEB.
  intros pc J rho tp Q H2 HST HC0 HC1. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN ltac:(rewrite HNX; exact HST) (run_some (two_at_ne l pc H2))).
  - rewrite HNX. apply etriple_LQA_of_leaves. intros L0 rhoE Hin Hag.
    destruct (proj1 (two_at_In l pc L0 H2 Hin)) as [-> | ->]; [rewrite HEA; exact (HC0 rhoE Hag) | rewrite HEB; exact (HC1 rhoE Hag)].
Qed.
End Runs.

Fixpoint pairs_eqb (a b : list (sv * sv)) : bool :=
  match a, b with
  | [], [] => true
  | p :: a', q :: b' => sv_eqb (fst p) (fst q) && sv_eqb (snd p) (snd q) && pairs_eqb a' b'
  | _, _ => false
  end.
Lemma pairs_eqb_sound : ltac2:(tb__ "0|1|
S1S4S12S12A2A1M0G0SdS2S4dR2R1A2S3A3SdG0R3R2A3F_;Fb;Fa;").
Proof.
  induction a as [|p a IH]; intros [|q b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
  destruct p, q; cbn in *; subst. f_equal. apply IH. exact H3.
Qed.
Definition sdiff (E C : axst) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|5|
S6S6S7S4S1S4S12S12A2A1M0S1S13A1M1A2M2A1S2Lx;S47S2eVE;A1M3S2eVC;A1M4A2G2G2S2Lp;R1G0G1G1S2Ll;R1S4dR2Vd;A2S13G1S5Ll0;Ls;X1x2Ll;Ld';X4x1Lp;S5X7x2S23G4A1A2S64S15G4A1S15G3A1A2A2").

Lemma restate_SPA : ltac2:(tb__ "0|0|
S27S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S38SdS2S49R6R5R4A3S3A3S46R4R5A2S26S0R9R8R5R4R3A6S26S0RaS30R9S2eR8A1A2R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fd;FC;FE;FJ;").
Proof.
  intros J E C d rho tp w H Hd HS. unfold sdiff in H. apply andb_prop in H as [H HN]. apply andb_prop in H as [H HW].
  destruct (state_diff (ax_S E) (ax_S C)) as [[d' [|f nf]]|] eqn:SD; try discriminate H.
  apply pairs_eqb_sound in H. subst d'. apply Pos.eqb_eq in HN.
  exact (SPA_restate segsA J rho E (ax_S C) tp w d [] HW SD HN Hd ltac:(constructor) HS).
Qed.

Lemma restate_cont : ltac2:(tb__ "0|0|
S27S38OF_;S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S39SdS2S49R6R5R4A3S3A3S46R4R5A2SdS2cS30R8S2eR7A1A2R7A3S37S0RaS26S0RbR8R6R5A5R4A4S37S0RbS26S0RcRaR7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;Fok;FJ;").
Proof.
  intros J ok E C d rho tp Q H Hd HEQ HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H Hd Hw).
Qed.
Lemma restate_econt : ltac2:(tb__ "0|0|
S27S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S38OF_;SdS2S49R6R5R4A3S3A3S46R4R5A2SdS2cS30R8S2eR7A1A2R7A3S36S0S26S0RaR8R6R5A5R4A3S36S0S26S0RbRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;FJ;").
Proof.
  intros J E C d rho tp Q H Hd HEQ HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H Hd Hw).
Qed.

Lemma restate_contF : ltac2:(tb__ "0|1|
S27S38OF_;S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S39SdS2S49R6R5R4A3S3A3S42S13S16R4A1S17S2eR7A1M0A1A3S46R5R6A2F_;SdS2cS30R8G0A2R7A3S37S0RaS26S0RbR8R6R5A5R4A4S37S0RbS26S0RcRaR7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;Fok;FJ;").
Proof.
  intros J ok E C d rho tp Q H Hd HEQ HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H (Hd (SPA_facts_hold segsA J rho E tp w Hw)) Hw).
Qed.
Lemma restate_econtF : ltac2:(tb__ "0|1|
S27S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S38OF_;SdS2S49R6R5R4A3S3A3S42S13S16R4A1S17S2eR7A1M0A1A3S46R5R6A2F_;SdS2cS30R8G0A2R7A3S36S0S26S0RaR8R6R5A5R4A3S36S0S26S0RbRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;FJ;").
Proof.
  intros J E C d rho tp Q H Hd HEQ HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H (Hd (SPA_facts_hold segsA J rho E tp w Hw)) Hw).
Qed.

Lemma fact_in_holds : ltac2:(tb__ "0|0|
S11S13S1S13A1SdS2S41S13S1aR2A1R1A3S3A3S42S13S16R4A1R2A3S16R5R4A2F_;F_;FF;Fp;Frho;").
Proof.
  intros rho p F Hb HF. apply existsb_exists in Hb as (q & Hin & Heq). apply sprop_eqb_sound in Heq. subst q. exact (proj1 (Forall_forall _ _) HF p Hin).
Qed.
Lemma fact_geu_lit : ltac2:(tb__ "0|0|
S11S3eS3dS1S13A1SeS5dZ0R2A2S5eR2S5fZ2Z40A2A2A2SdS2S41S13S1aS1dS60S1eR4A1S1cR3A1A3A1R2A3S3A3S42S13S16R6A1R3A3S5dR5S35Q40S21R7R6A2A2A2F_;F_;F_;FF;Fk;Fi;Frho;").
Proof.
  intros rho i k F Hk Hb HF. pose proof (fact_in_holds rho _ F Hb HF) as H. cbn [holds branch_taken eval] in H.
  unfold bv_ltu in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply Bool.negb_true_iff in H. apply Z.ltb_ge in H. exact H.
Qed.
Lemma fact_ltu_lit : ltac2:(tb__ "0|0|
S11S3eS3dS1S13A1SeS5dZ0R2A2S5eR2S5fZ2Z40A2A2A2SdS2S41S13S1aS24S1dS60S1eR4A1S1cR3A1A3A1A1R2A3S3A3S42S13S16R6A1R3A3S5eS35Q40S21R7R6A2A2R5A2F_;F_;F_;FF;Fk;Fi;Frho;").
Proof.
  intros rho i k F Hk Hb HF. pose proof (fact_in_holds rho _ F Hb HF) as H. cbn [holds branch_taken eval] in H.
  unfold bv_ltu in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia).
  destruct (Z.ltb_spec (bv_unsigned (rw rho i)) k) as [L|L]; [exact L|]. exfalso. apply H. reflexivity.
Qed.

Definition entsI (L T : axst) : bool := ltac2:(tb__ "0|2|
S6S6S6S32VL;VT;S61S3aS2eVL;A1S2eVT;A1M0A3M1A3S5bG1S3aA2A2S31VT;A1A2S23G0A1A2").
Lemma ent_SPA : ltac2:(tb__ "0|0|
S27S2cS2cS11S1S34Q40A1A1S38SdS2S48R5R4A2S3A3S28S0S3aR7A3S26S0R8R7R5R4R3A6S58R6S61S3aS2eR8A1S2eR7A1A3A2S11SeS26S0RaR8R1R6R5A6S14S3aR7R1A3A2Trho';F_;F_;F_;Fw;Ftp;Frho;FT;FL;FJ;").
Proof.
  intros J L T rho tp w H HST HS rho'. unfold entsI in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [HE HI].
  split; [exact (SPA_entails segsA J NPRE L T _ rho tp w HE HI HST HS) | apply rho_sub_agree; exact HI].
Qed.
Lemma ent_cont : ltac2:(tb__ "0|0|
S27S38OF_;S2cS2cS11S1S34Q40A1A1S39SdS2S48R5R4A2S3A3S28S0S3aR8A3S11S14S3aR6R1A3S37S0RaS26S0RbR8R2R6A5R5A4F_;Frho';S37S0R9S26S0RaR8R6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;FT;FL;Fok;FJ;").
Proof.
  intros J ok L T rho tp Q H HST HC. eapply triple_conseq; [| intros w Hw; exact Hw | apply (HC (rho_sub rho (infer_sub NPRE (ax_S L) (ax_S T))))].
  - intros w Hw. exact (proj1 (ent_SPA J L T rho tp w H HST Hw)).
  - apply rho_sub_agree. unfold entsI in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ HI]. exact HI.
Qed.
Lemma ent_econt : ltac2:(tb__ "0|0|
S27S2cS2cS11S1S34Q40A1A1S38OF_;SdS2S48R5R4A2S3A3S28S0S3aR7A3S11S14S3aR6R1A3S36S0S26S0RaR8R2R6A5R5A3F_;Frho';S36S0S26S0R9R8R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FT;FL;FJ;").
Proof.
  intros J L T rho tp Q H HST HC. eapply etriple_conseq; [| intros w Hw; exact Hw | apply (HC (rho_sub rho (infer_sub NPRE (ax_S L) (ax_S T))))].
  - intros w Hw. exact (proj1 (ent_SPA J L T rho tp w H HST Hw)).
  - apply rho_sub_agree. unfold entsI in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ HI]. exact HI.
Qed.

Definition JQ (J : jpredA) : jpostA := ltac2:(tb__ "0|3|
S11S1S34Q40A1M0A1M1S11G1S1S45A1S44SeVJ;R4R3R2R1A4SeSdG1R3R5A3SeG0SdS7S34Q8A1M2A1S20R5R1A2S20R7R1A2A3Fa;S3eSdS1G2A1S1fR5R1A2S1fR7R1A2A3Fl;A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Lemma leaf_post : ltac2:(tb__ "0|1|
S27S38OF_;S2cS2cS11S11S1S34Q40A1A1S1S4S2cS52A2M0A1SdS2S48R6R5A2S3A3S28S0S3aR9A3S3fG0S8S2cS52R7S4cRaA1A4R3A3S14S3aR7R6A3S37S0RbS26S0RcRaR7R6A5S56S0S3aR8R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;FrhoL;Frho0;FPost;FL;Fok;FJ;").
Proof.
  intros J ok L Post rho0 rhoL tp Posts H HST HIN Hag. eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. destruct (ent_SPA J L Post rhoL tp w H HST Hw) as [HP Hag'].
  pose proof (agree_below_trans _ _ _ _ Hag Hag') as (Hrw & Hrl & Hrm).
  apply (LQPA_intro segsA NPRE rho0 tp Posts Post (JQ J) _ tp w J HIN HP).
  - split; [exact Hrw | exact Hrl].
  - intros HJ. split; [exact HJ|]. split; [reflexivity|]. split; [intros a; symmetry; apply Hrm | intros l0; symmetry; apply Hrl].
Qed.
Lemma leaf_epost : ltac2:(tb__ "0|1|
S27S2cS2cS11S11S1S34Q40A1A1S1S4S2cS52A2M0A1SdS2S48R6R5A2S3A3S28S0S3aR8A3S3fG0S8S2cS52R7S4cR9A1A4R3A3S14S3aR7R6A3S36S0S26S0RbRaR7R6A5S56S0S3aR8R6R5A5A3F_;F_;F_;F_;FPosts;Ftp;FrhoL;Frho0;FPost;FL;FJ;").
Proof.
  intros J L Post rho0 rhoL tp Posts H HST HIN Hag. eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
  intros w Hw. destruct (ent_SPA J L Post rhoL tp w H HST Hw) as [HP Hag'].
  pose proof (agree_below_trans _ _ _ _ Hag Hag') as (Hrw & Hrl & Hrm).
  apply (LQPA_intro segsA NPRE rho0 tp Posts Post (JQ J) _ tp w J HIN HP).
  - split; [exact Hrw | exact Hrl].
  - intros HJ. split; [exact HJ|]. split; [reflexivity|]. split; [intros a; symmetry; apply Hrm | intros l0; symmetry; apply Hrl].
Qed.

Lemma call_soundA_tp : ltac2:(tb__ "0|3|
S38OF_;S27S27S27S27S2cS2cS5aS1S18A1M0S1S2dA1S39S11S1S34Q40A1A1M1SdS7G0A1S54R8R7R6A3SaG0R5A2A3SdS2S53R9R8R7R6S43S2dS2cS2fR5A4A5S3A3S11G1S37S0R11S26S0RfRbR2R1A5S29S0ReS15S2eRbA1A1R2R1R8A6A4Ftp1;Frho1;S1S45A1M2S4fS44S2bS0R8R7ReS8G2S50R3S51R2R1A2A4A5R13R9R8R4R2A4R13S58S59RaRdS57R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S2dS11S11G2S4fS44G2S44S3fS2dR8R10A3S2bS0RfReR15S8G2S50R6S51R5R4A2A4A5R1aR10RfR7R5A4S62R11S57R6R10R7A3R14R15S2eR16A1S2eR17A1S2eS2fRbA1A1RaR9A9R1aRaR11R6R5A4R1aRcR12R7R6A4F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S2dS11S3fS2dR2RbA3S14S15S2eR10A1A1RaR2A3S37S0R16S26S0R12S55RfR10S2fR4A1R11ReA5R3RaA5RcA4F_;F_;Frho';FL;S37S0R13S26S0R12ReR8R7A5R9A4F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc;FJp';FJp;FJ;Fok;").
Proof.
  intros ok J Jp Jp' Jc C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout Hcont.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segsA C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segsA C Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' HinL HAG n HgQ). split; [exact HSP|].
  exact (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk').
Qed.
Lemma call_completeA_tp : ltac2:(tb__ "0|3|
S27S27S27S27S2cS2cS5aS1S18A1M0S1S2dA1S38OF_;S11S1S34Q40A1A1M1SdS7G0A1S54R8R7R6A3SaG0R5A2A3SdS2S53R9R8R7R6S43S2dS2cS2fR5A4A5S3A3S11G1S36S0S26S0RfRbR2R1A5S29S0ReS15S2eRbA1A1R2R1R8A6A3Ftp1;Frho1;S1S45A1M2S4fS44S2bS0R8R7ReS8G2S50R3S51R2R1A2A4A5R13R9R8R4R2A4R13S58S59RaRdS57R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S2dS11S11G2S4fS44G2S44S3fS2dR8R10A3S2bS0RfReR15S8G2S50R6S51R5R4A2A4A5R1aR10RfR7R5A4S62R11S57R6R10R7A3R14R15S2eR16A1S2eR17A1S2eS2fRbA1A1RaR9A9R1aRaR11R6R5A4R1aRcR12R7R6A4F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S2dS11S3fS2dR2RbA3S14S15S2eR10A1A1RaR2A3S36S0S26S0R12S55RfR10S2fR4A1R11ReA5R3RaA5RcA3F_;F_;Frho';FL;S36S0S26S0R12ReR8R7A5R9A3F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc;FJp';FJp;FJ;").
Proof.
  intros J Jp Jp' Jc C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout Hcont.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segsA C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segsA C Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' HinL HAG _ (conj HSP (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk'))) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Section OpaqueCall.
Variables (Cst : axst) (Pre : axst) (Posts : list leafA) (s : wsub) (R : list sobj) (T : axst) (g : positive).
Hypothesis Hsum : ltac2:(tb__ "0|1|
S38OF_;S27S11S1S34Q40A1A1S2aS0R4R3A3S28S0S15S2eVPre;A1A1M0R4A3S37S0R6S26S0R5VPre;R4R3A5S29S0R5G0R4R3VPosts;A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Hypothesis Hesum : ltac2:(tb__ "0|1|
S27S11S1S34Q40A1A1S28S0S15S2eVPre;A1A1M0R3A3S36S0S26S0R4VPre;R3R2A5S29S0R4G0R3R2VPosts;A6A3F_;Ftp;Frho;FJx;").
Hypothesis He : ltac2:(tb__ "0|1|
SdS7S1S18A1M0A1S54VCst;VPre;Vs;A3SaG0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
SdS2S53VCst;VPre;Vs;VR;S43S2dS2cS2fVPosts;A4A5S3A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S2dS3fS2dR1VPosts;A3SdS2cS55Vs;VPre;S2fR2A1VCst;VR;A5VT;A3F_;FP;").
Hypothesis FBC : ltac2:(tb__ "0|1|
SdS2S40S13S19S15S2eVCst;A1M0A1A1S17G0A1A3S3A3").
Hypothesis FBT : ltac2:(tb__ "0|0|
SdS2S40S13S19S15S2eVT;A1A1A1S17S2eVCst;A1A1A3S3A3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S65Vg;S15S2eVCst;A1A1A2").

Theorem call_cont : ltac2:(tb__ "0|1|
S27S38OF_;S11S1S34Q40A1A1S39S2aS0R4R5A3S28S0Vg;R6A3S11S14S15S2eVCst;A1M0A1R6R1A3S37S0R8S26S0R9S63VT;S17G0A1A2R2R6A5R5A4F_;Frho';S37S0R7S26S0R8VCst;R6R5A5R4A4F_;F_;F_;FQ;Ftp;FrhoE;Fok;FJ;").
Proof.
  intros J ok rhoE tp Q HOK HST HC.
  set (Jf := (fun (_ : valuation) t tr md => J rhoE t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segsA ok Jf) by (intros r t tr ms md msv' HJ; exact (HOK rhoE t tr ms md msv' HJ)).
  assert (Jf_st : stableA segsA (ss_next (ax_S Pre)) Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segsA ok _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segsA _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_soundA_tp ok J Jf Jf J Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ']. eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' HinL Hag. rewrite (HT L HinL).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC rho' Hag)].
    apply SPA_refacts; [exact Hw | exact FBT | intros _; exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC)].
Qed.
Theorem call_econt : ltac2:(tb__ "0|1|
S27S11S1S34Q40A1A1S38OF_;S28S0Vg;R4A3S11S14S15S2eVCst;A1M0A1R5R1A3S36S0S26S0R7S63VT;S17G0A1A2R2R5A5R4A3F_;Frho';S36S0S26S0R6VCst;R5R4A5R3A3F_;F_;FQ;Ftp;FrhoE;FJ;").
Proof.
  intros J rhoE tp Q HST HC.
  set (Jf := (fun (_ : valuation) t tr md => J rhoE t tr md) : jpredA).
  assert (Jf_st : stableA segsA (ss_next (ax_S Pre)) Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  intros w Hw. pose proof (SPA_facts_hold segsA _ rhoE Cst tp w Hw) as HFC. revert w Hw.
  apply (call_completeA_tp J Jf Jf J Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. exact (Hesum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ']. eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' HinL Hag. rewrite (HT L HinL).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC rho' Hag)].
    apply SPA_refacts; [exact Hw | exact FBT | intros _; exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC)].
Qed.
End OpaqueCall.
End SegQlib.

(* [comment removed for export] *)
Module InvIA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "c_addr"; "acell"; "view"; "c_w"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "prod"; "option"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA.WithSegs"; "agree_nz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "qbatch"; "aa_cls"; "ageom"; "aa_live"; "class_state"; "sec_chunk"; "aa_cache_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "DG"; "ag_thread"; "qb_addr"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "ia_zone"; "qhdr_repr"; "IA_BEG"; "alloc_magic_ok"; "batch_repr"; "class_repr"; "depot_wf"; "live_block_repr"; "q_item_ok"; "qlinks"; "set_inited"; "geom_ok"; "ia_inv"; "live_sep"; "quarantine_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "dyn_in"; "IMG_LO"; "Sh"; "max_count"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "DFP"; "depot_mem"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymFrame SymEntail Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac lia := first [Stdlib.micromega.Lia.lia | unfold IMG_HI, IMG_LO, IA_BEG, IA_END, SHADOW_OFF, PG in *; Stdlib.micromega.Lia.lia].

Section WithSegs.
Variable segs : list Segment.
Let AInvA := AInvA segs.

Definition agree_nz (m m' : bview) : Prop := ltac2:(tb__ "0|0|
S0S8S25R1A1A1S7S11S3dQ8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").

Lemma nz_below : ltac2:(tb__ "0|0|
S0SdR1S27A2S8S25R2A1A1F_;Fz;").
Proof. intros z Hz. unfold ia_zone, IA_BEG, IA_END in *. lia. Qed.
Lemma nz_above : ltac2:(tb__ "0|0|
S0SbS35R1A2S8S25R2A1A1F_;Fz;").
Proof. intros z Hz. unfold ia_zone, IA_BEG, IA_END, IMG_HI in *. lia. Qed.
Lemma nz_band : ltac2:(tb__ "0|0|
S0SaSdR1S37A2SbS35R1A2A2S8S25R2A1A1F_;Fz;").
Proof. intros z Hz. unfold ia_zone, IA_BEG, IA_END, IMG_LO, IMG_HI in *. lia. Qed.
Lemma nz_dyn : ltac2:(tb__ "0|0|
S0S0S0S0S36R4R3R2A3S9SbR4R2A2SdR2ScR4R3A2A2A2S8S25R3A1A1F_;F_;Fz;Flen;Fa;Ftop;").
Proof. intros top a len z (_ & _ & _ & HB & _) Hz. apply nz_band. lia. Qed.

Lemma nz_depot : ltac2:(tb__ "0|0|
S21S1S0S42R3R2A2S41R4R2A2S8S25R3A1A1F_;F_;Fz;Fm;FG;").
Proof.
  intros G m z HD Hz. destruct Hz as [Hs|[(b & Hb & Hzb)|(b & Hb & Hzb)]].
  - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold ia_zone, IA_BEG, IA_END. lia.
  - destruct (dm_nb _ _ HD b Hb) as (_ & H1 & _). apply nz_above. lia.
  - destruct (dm_fbases _ _ HD b Hb) as (_ & H1 & _). apply nz_above. lia.
Qed.
Lemma depot_wf_nz : ltac2:(tb__ "0|0|
S1S1S14S13R3R2A2S2bR4R2A2S2bR4R3A2F_;F_;FA;Fm';Fm;").
Proof.
  intros m m' A AH HD. unfold depot_wf in *. eapply depot_mem_frame; [|exact HD]. intros a Ha. apply AH. eapply nz_depot; [exact HD | exact Ha].
Qed.

Lemma rz_bound : ltac2:(tb__ "0|1|
S0S9SbZ10S3aR1A1M0A2SbG0Z800A2A2Fn;").
Proof.
  intros n. unfold rz, rz_log.
  repeat (destruct (n <=? _); [rewrite Z.shiftl_mul_pow2 by lia; cbn; lia|]). rewrite Z.shiftl_mul_pow2 by lia. cbn. lia.
Qed.

Lemma max_count_le : ltac2:(tb__ "0|0|
S0SbS39R1A1Z10A2Fc;").
Proof. intros c. unfold max_count, MaxCachedHint, kMaxNumCachedHint. pose proof (Z.le_min_l 8 (Z.max 1 (kMaxBytesCached / Size c))). lia. Qed.

Lemma cell_ok_agree_above : ltac2:(tb__ "0|0|
S1S1S4S13R3R2A2SbS35S3R2A1A2S2R5R3A2S2R5R4A2F_;F_;F_;Fc;Fm';Fm;").
Proof. intros m m' c AH Hc. apply cell_ok_agree. intros k Hk. apply AH. apply nz_above. lia. Qed.
Lemma cell_ok_agree_below : ltac2:(tb__ "0|0|
S1S1S4S13R3R2A2SbScS3R2A1SeS6R2A1A1A2S27A2S2R5R3A2S2R5R4A2F_;F_;F_;Fc;Fm';Fm;").
Proof. intros m m' c AL H2. apply cell_ok_agree. intros k Hk. apply AL. apply nz_below. lia. Qed.
Lemma cell_ok_agree_dyn : ltac2:(tb__ "0|0|
S1S1S4S0S0S0S13R6R5A2S36R4R3R2A3SbR4S3R6A1A2SbScS3R7A1SeS6R7A1A1A2ScR5R4A2A2S2RaR8A2S2RaR9A2F_;F_;F_;F_;F_;Flen;Fa;Ftop;Fc;Fm';Fm;").
Proof. intros m m' c top a len AH HD H1 H2. apply cell_ok_agree. intros k Hk. apply AH. eapply nz_dyn; [exact HD | lia]. Qed.

Lemma alloc_magic_ok_nz : ltac2:(tb__ "0|0|
S1S1S0S0S13R4R3A2SbScS35Z800A2R3A2S28R6R4R3A3S28R6R5R4A3F_;F_;F_;Fn;Fb;Fm';Fm;").
Proof.
  intros m m' b n AH Hb [H|[H1 H2]]; [left; exact H|right]. pose proof (rz_bound n) as RZ.
  split; (eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | assumption]).
Qed.

Lemma Sh_above : ltac2:(tb__ "0|0|
S0SbZ0R1A2SbS35S38R2A1A2F_;Fa;").
Proof. intros a Ha. unfold Sh, SHADOW_OFF, IMG_HI. pose proof (Z.div_pos a 8 Ha ltac:(lia)). lia. Qed.

Lemma live_block_repr_nz : ltac2:(tb__ "0|0|
S1S1S14S32R1A1S13R4R3A2S2cR5R3A2S2cR5R4A2F_;F_;F_;FA;Fm';Fm;").
Proof.
  intros m m' A Hsep AH Hlive b n Hin.
  destruct (Hlive b n Hin) as (L1 & L2 & L3 & L4 & L5 & L6). destruct (Hsep b n Hin) as (S1 & S2 & S3 & _).
  pose proof (rz_bound n) as RZ.
  split; [rewrite AH by (apply nz_above; lia); exact L1|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact L2]|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact L3]|].
  split.
  - destruct L4 as [L4a L4b]. pose proof (Sh_above b ltac:(lia)) as SB. split.
    + intros g Hg. rewrite AH by (apply nz_above; lia). exact (L4a g Hg).
    + intros Hn. rewrite AH by (apply nz_above; pose proof (Z.div_pos n 8); lia). exact (L4b Hn).
  - split; [eapply alloc_magic_ok_nz; [exact AH | lia | exact L5]|].
    destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite AH by (apply nz_above; lia); exact Ht | exact Hm4].
Qed.

Lemma class_repr_nz : ltac2:(tb__ "0|0|
S1S1S19S14S14S0S1bS30R5A1S9SbZ1R3A2SbR3Z1eA2A2S7S12S1dR5A1S1dR6A1A3S7SfS10S0S0A2A1S1aR6A1S1aR7A1A3S7SfS17A1S3eR7A1S3eR8A1A3S13RcRbA2S2aRdRbRaR8R7A5S2aRdRcRaR9R8A5F_;F_;F_;F_;F_;F_;F_;Fcs;Fc;FA';FA;FG;Fm';Fm;").
Proof.
  intros m m' G A A' c cs HG Hc Hci Hlv Hq AH P4.
  pose proof (geom_nums G HG) as (_ & _ & _ & T1 & T2 & _ & _ & _ & _ & _ & S1 & S2 & S0 & TG).
  pose proof HG as (_ & _ & (_ & TD) & _).
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  assert (CA : forall c, IMG_HI <= c_addr c -> cell_ok m c -> cell_ok m' c).
  { intros c0 Hc0. apply cell_ok_agree_above; [exact AH | exact Hc0]. }
  assert (CT : forall c, ag_thread G <= c_addr c -> c_addr c + Z.of_nat (c_w c) <= ag_thread G + 0x1000 -> cell_ok m c -> cell_ok m' c).
  { intros c0 H1 H2. eapply cell_ok_agree_dyn; [exact AH | exact TD | exact H1 | exact H2]. }
  unfold class_repr in P4 |- *. rewrite Hci.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *.
  assert (RI : IMG_HI <= ri) by (unfold ri, region_info; rewrite kSpaceSize_val; unfold kRegionInfoStride, IMG_HI; lia).
  assert (FA : IMG_HI <= fa) by (unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, IMG_HI; lia).
  unfold live_ids. rewrite Hlv, Hq.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  set (rb := region_beg (ag_spacebeg G) c) in *.
  assert (RB : IMG_HI <= rb) by (unfold rb, region_beg, kRegionSize, IMG_HI; lia).
  split; [apply CA; [cbn [c_addr]; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split; [intros i x Hi; apply CA; [cbn [c_addr]; lia | exact (C9 i x Hi)]|].
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [exact N7|].
  split; [eapply present_but_agree; [|exact PU]; intros z Hz _; apply AH; apply nz_above; lia|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply AH; apply nz_above; pose proof (Sh_above rb ltac:(lia)); lia|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AH; eapply nz_dyn; [exact TD | lia]|].
  split; [exact ND|]. split; [exact LV|].
  split.
  - intros Hx. destruct (CI Hx) as (D1 & D2 & D3 & D4 & D5).
    split; [apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D1]|].
    split; [apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D2]|].
    split; [apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D3]|]. split; [|exact D5].
    intros i x Hi. assert (Li : (i < length (cs_cache cs))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (max_count_le c) as MC.
    apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact (D4 i x Hi)].
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hx. destruct (CN Hx) as [D1 D2]. split; [exact D1|]. eapply filled_agree; [|exact D2]. intros z Hz. apply AH. eapply nz_dyn; [exact TD | lia].
Qed.

Lemma secondary_repr_nz : ltac2:(tb__ "0|1|
S1S1S14S14S7S19S15R1A1S15R2A1A3S7SfS1cA1S16R2A1S16R3A1A3S7S0S1eR3A1S1eR4A1A3S7SfS10S0S0A2A1S1aR4A1S1aR5A1A3S13R8R7A2S34R9R7A2M0G0F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' Eg Es Ep El AH (S1 & SP & S2 & S3 & S4 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite Eg, Es, Ep, El.
  pose proof (dyn_ok_big _ _ _ S4 ltac:(unfold kPtrArrayReserve; lia)) as PB.
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in *; lia)) as CB.
    assert (Li : (i < length (aa_sec A))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D1]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D2]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D3]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D4]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D5]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply AH; apply nz_above; lia|].
    eapply present_agree; [|exact D14]. intros z Hz. apply AH. apply nz_above. pose proof (Sh_above (sc_map_beg ch) ltac:(lia)). lia. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AH; apply nz_above; unfold kPtrArrayReserve in *; lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  unfold SEC_INST in *.
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I1]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I2]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I3]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I4]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I5]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AH; apply nz_below; unfold IA_BEG; lia|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I8]|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AH; apply nz_below; unfold IA_BEG; lia.
Qed.

Lemma q_item_ok_nz : ltac2:(tb__ "0|0|
S1S1S14S14S10S0S0A2S7S19S15R2A1S15R3A1A3S7SfS1bA1S18R3A1S18R4A1A3S7SfS1cA1S16R4A1S16R5A1A3S13R8R7A2S2dR9R7R5A3S2dR9R7R6A3F_;F_;F_;F_;F_;Fit;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' it Eg Ec Es AH HQ. unfold q_item_ok in HQ |- *. cbn zeta in HQ |- *. rewrite Eg, Ec, Es.
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  split; [exact Q1|]. split; [exact Q2|].
  split; [rewrite AH by (apply nz_above; lia); exact Q3|].
  split; [eapply present_agree; [|exact Q4]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact Q5]|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact Q6]|].
  split; [eapply present_agree; [|exact Q7]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [eapply alloc_magic_ok_nz; [exact AH | lia | exact Q8]|].
  split; [exact Q9|]. split; [exact Q10|].
  pose proof (Sh_above (fst it) ltac:(lia)).
  eapply present_agree; [|exact Q11]. intros z Hz. apply AH. apply nz_above. lia.
Qed.

Lemma batch_repr_nz : ltac2:(tb__ "0|0|
S1S1S14S14S17S7S19S15R2A1S15R3A1A3S7SfS1bA1S18R3A1S18R4A1A3S7SfS1cA1S16R4A1S16R5A1A3S13R8R7A2S29R9R7R5A3S29R9R7R6A3F_;F_;F_;F_;F_;Fb;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' b Eg Ec Es AH (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold batch_repr. rewrite Eg, Ec.
  split; [exact B0|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact B1]|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact B2]|].
  split; [exact B3|]. split; [exact B4|].
  split; [eapply present_agree; [|exact B5]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact I1]|].
  eapply (q_item_ok_nz m m' A A'); auto.
Qed.

Lemma qlinks_nz : ltac2:(tb__ "0|0|
S1S1SfS17A1S13R3R2A2S3fS17S17SbS35S23R1A1A2Lb;R2A3S2eR5R3A2S2eR5R4A2F_;F_;F_;Fl;Fm';Fm;").
Proof.
  intros m m' l AH. induction l as [|b r IH]; intros HF H; [exact I|]. cbn in H |- *. destruct H as [H1 H2].
  inversion HF as [|b0 r0 Hb Hr]; subst.
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact H1] | exact (IH Hr H2)].
Qed.

Lemma qhdr_repr_dyn : ltac2:(tb__ "0|0|
S1S1S0S0S0S0SfS17A1S13R7R6A2S36R6R5R4A3SbR6R4A2SbScR5Z20A2ScR7R6A2A2S26RbR6R5A3S26RbR7R6A3F_;F_;F_;F_;F_;Fl;Fhdr;Flen;Fa;Ftop;Fm';Fm;").
Proof.
  intros m m' top a len hdr l AH HD H0 H1 (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
  split; [eapply cell_ok_agree_dyn; [exact AH | exact HD | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact Q1]|].
  split; [intros Hl; destruct (Q2 Hl) as [X Y]; split; (eapply cell_ok_agree_dyn; [exact AH | exact HD | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | assumption])|].
  split; [eapply present_agree; [|exact Q3]; intros z Hz; apply AH; eapply nz_dyn; [exact HD | lia]|].
  eapply cell_ok_agree_dyn; [exact AH | exact HD | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact Q4].
Qed.
Lemma qhdr_repr_below : ltac2:(tb__ "0|0|
S1S1S0SfS17A1S13R4R3A2SbScR3Z20A2S27A2S26R6R4R3A3S26R6R5R4A3F_;F_;F_;Fl;Fhdr;Fm';Fm;").
Proof.
  intros m m' hdr l AL H1 (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
  split; [eapply cell_ok_agree_below; [exact AL | cbn [c_addr c_w Z.of_nat]; lia | exact Q1]|].
  split; [intros Hl; destruct (Q2 Hl) as [X Y]; split; (eapply cell_ok_agree_below; [exact AL | cbn [c_addr c_w Z.of_nat]; lia | assumption])|].
  split; [eapply present_agree; [|exact Q3]; intros z Hz; apply AL; apply nz_below; lia|].
  eapply cell_ok_agree_below; [exact AL | cbn [c_addr c_w Z.of_nat]; lia | exact Q4].
Qed.

Lemma quarantine_repr_nz : ltac2:(tb__ "0|3|
S1S1S14S14S7S19S15R1A1S15R2A1A3S7SfS1bA1S18R2A1S18R3A1A3S7SfS1cA1S16R3A1S16R4A1A3S7SfS17A1M0S20R4A1S20R5A1A3S7G0S1fR5A1S1fR6A1A3S36S24S15R7A1M1A1S22G1A1Z1000A3S13RaR9A2S33RbR9A2M2G2F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' Eg Ec Es E1 E2 HT AH (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). unfold quarantine_repr. rewrite Eg, E1, E2.
  assert (HB : Forall (fun b => IMG_HI <= qb_addr b) (aa_q_thread A ++ aa_q_global A)).
  { apply Forall_forall. intros b Hb. exact (proj1 (proj1 (Forall_forall _ _) Q1 b Hb)). }
  pose proof (proj1 (Forall_app _ _ _) HB) as [HB1 HB2].
  split; [apply Forall_forall; intros b Hb; apply (batch_repr_nz m m' A A' b Eg Ec Es AH); exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
  split; [exact (qlinks_nz m m' _ AH HB1 Q2)|]. split; [exact (qlinks_nz m m' _ AH HB2 Q3)|].
  split; [apply (qhdr_repr_dyn m m' _ _ _ _ _ AH HT); [lia | lia | exact Q4]|].
  split; [apply (qhdr_repr_below m m'); [exact AH | unfold QG, IA_BEG; lia | exact Q5]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold QG, IA_BEG; lia | exact Q6]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold QG, IA_BEG; lia | exact Q7]|].
  split; [exact Q8|]. exact Q9.
Qed.

Lemma AInvA_ia_update : ltac2:(tb__ "0|0|
S14S3cS3cSfS3dQ40A1A1S40VAInvA;R5R4R2R1A4S0S8S25R1A1A1S7S11S3dQ8A1A1S5Vsegs;S3bR6A1R2A3S5Vsegs;S3bR7A1R2A3A3F_;Fz;S31S5Vsegs;S3bR5A1A2S2fR7A1A2VAInvA;S2fR8A1R6R5R4A4F_;F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HA Hout HIA'. pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (geom_nums (aa_geom A) HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  pose proof HG as ((_ & FD) & _ & (_ & TD) & CD & DD & _).
  rewrite FS_total_val in F2, FD.
  assert (AH : agree_nz (view segs (rm rho)) (view segs (rm rho'))) by (intros z Hz; apply Hout; exact Hz).
  assert (AHM : agree_nz (maskv (fs_footb (aa_geom A)) (view segs (rm rho))) (maskv (fs_footb (aa_geom A)) (view segs (rm rho')))).
  { intros z Hz. unfold maskv. destruct (fs_footb (aa_geom A) z); [reflexivity | exact (AH z Hz)]. }
  unfold AInvA, Inv.AInvA. cbn [aa_geom set_inited].
  split; [exact HG|]. split.
  {   eapply cells_ok_frame; [|exact HR]. intros z Hz. apply Hout.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin.
    apply andb_prop in Hin as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - destruct (rtc_cells_img_lt _ _ Hc) as [X Y]. unfold ia_zone. lia.
    - unfold rtc_cells_geom in Hc.
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in Hlo, Hhi; unfold fs_log_cell, fs_needs_gc_cell in *;
        first [ eapply nz_dyn; [exact CD | lia] | eapply nz_dyn; [exact TD | lia] | eapply nz_dyn; [exact DD | lia] | eapply nz_dyn; [exact FD | lia] ] |]).
      destruct Hc. }
  split.
  {
    assert (E : restrictv (fs_footb (aa_geom A)) (view segs (rm rho')) = restrictv (fs_footb (aa_geom A)) (view segs (rm rho))).
    { apply restrictv_ext. intros z Hz. apply Hout.

      unfold fs_footb in Hz. apply orb_prop in Hz as [Hz|Hz]; [apply orb_prop in Hz as [Hz|Hz]|];
        apply andb_prop in Hz as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2.
      - eapply nz_dyn; [exact FD | lia].
      - rewrite FS_kFlagsOffset_val in B1. rewrite FS_total_val in B2. eapply nz_dyn; [exact FD | lia].
      - rewrite FS_frames_off_val in B1. apply nz_above. pose proof (Sh_above (ag_fsb (aa_geom A) + 36864) ltac:(lia)). lia. }
    rewrite E. exact HF. }
  split; [|destruct HM as (HM1 & HM2 & HB); split; [exact HM1|]; split; [exact HM2|];

           eapply bandtp_agree; [|exact HB]; intros z Hz; apply Hout;
           unfold ia_zone, IA_BEG, IA_END, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; clear -Hz; lia].
  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & _ & Hth & Hmi).
  unfold rest_inv. cbn [aa_geom aa_live set_inited].
  split; [exact Hsep|].
  split; [exact (live_block_repr_nz _ _ A Hsep AHM Hlive)|].
  split.
  { destruct Hprim as (P1 & P2 & P3 & P4). unfold primary_repr. cbn [aa_cls aa_geom set_inited].
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    intros c Hc. apply (class_repr_nz _ _ (aa_geom A) A (set_inited A) c _ HG Hc eq_refl eq_refl eq_refl AHM). exact (P4 c Hc). }
  split; [exact (secondary_repr_nz _ _ A (set_inited A) eq_refl eq_refl eq_refl eq_refl AHM Hsec)|].
  split; [exact (quarantine_repr_nz _ _ A (set_inited A) eq_refl eq_refl eq_refl eq_refl eq_refl TD AHM Hq)|].
  split; [exact (depot_wf_nz _ _ A AHM Hdep)|]. split.
  { assert (MV : forall z, z < IMG_HI -> maskv (fs_footb (aa_geom A)) (view segs (rm rho')) z = view segs (rm rho') z).
    { intros z Hz. apply maskv_out.
      pose proof (Sh_above (ag_fsb (aa_geom A) + FS_frames_off) ltac:(rewrite FS_frames_off_val; lia)).
      apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; lia. }
    unfold ia_inv in HIA' |- *. cbn [aa_internal_inited set_inited] in HIA' |- *.
    destruct HIA' as (X1 & X2 & X3 & X4 & X5). unfold IMG_HI in MV.
    split; [rewrite MV by lia; exact X1|]. split; [rewrite MV by lia; exact X2|]. split; [rewrite MV by lia; exact X3|].
    split; [rewrite MV by lia; exact X4|].
    intros z Hz. rewrite MV by (unfold IA_MAP1, IA_MAP1_SZ in Hz; lia). exact (X5 z Hz). }
  split.
  { unfold thread_inv in Hth |- *. destruct Hth as [Hth1 Hth2].
    split; [rewrite AHM by (eapply nz_dyn; [exact TD | lia]); exact Hth1|].
    eapply present_agree; [|exact Hth2]. intros z Hz. apply AHM. eapply nz_dyn; [exact TD | lia]. }

  destruct Hmi as (Hc & Hp & He). unfold misc_inv. split; [|split].
  - eapply cells_ok_frame; [|exact Hc]. intros z Hz. unfold maskv. rewrite Hout; [reflexivity|].
    unfold cells_footb, rtc_extra in Hz. cbn [existsb in_cellb c_addr c_w Z.of_nat] in Hz.
    unfold ia_zone, IA_BEG, IA_END. intros Hiz.
    repeat (apply orb_prop in Hz as [Hz|Hz]); try discriminate Hz;
      unfold in_cellb in Hz; cbn [c_addr c_w Z.of_nat] in Hz;
      apply andb_prop in Hz as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2; lia.
  - eapply present_agree; [|exact Hp]. intros z Hz. unfold maskv. rewrite Hout; [reflexivity|].
    unfold ia_zone, IA_BEG, IA_END. lia.
  - eapply present_agree; [|exact He]. intros z Hz. unfold maskv. rewrite Hout; [reflexivity|].
    unfold ia_zone, IA_BEG, IA_END, ERRNO_A in *. lia.
Qed.
End WithSegs.
End InvIA.

(* [comment removed for export] *)
Module CertFreeNull.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "prod"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "SLit"; "SPUle"; "FcsrFrm0"; "mkSS"; "SPAlign"; "SPUlt"; "SVar"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "TP_A"; "vCTX"; "O_T0"; "O_T40"; "O_cfa"; "O_ctx8"; "O_ctx98"; "O_mcs"; "O_pga"; "O_pgb"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "vBOT"; "vTOP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "E_fn"; "F_geom_fn"; "NW2"; "P0_fn"; "RT_fn"; "O_T3168"; "O_ia"; "O_iamap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "A_globals"; "Wcan"; "free_depth"; "mkA"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "V_FREE_A1"; "ae_free"; "ae_ret_free"; "@Stdlib.ZArith.BinInt.Z"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition NW2 : positive := 220%positive.

Definition O_ia (inited : Z) : sobj := ltac2:(tb__ "0|5|
S18SbZ0A1M0Z180e88M1Z180e8aS0S4S4S12S1A2M2S9A2M3S3G2S9S3S12S1G1U1M4A4SbVinited;A1A4S0G3S3G2S9S3S12S1Z180e89G4A4G0A4S2G3A1A3A3A4").
Definition O_iamap : sobj := ltac2:(tb__ "0|4|
S18SbZ0A1M0Zf2608M1Zf2610S0S4S4S12S1A2M2S9A2M3S3G2S9S3S12S1G1U8A4G0A4S2G3A1A3A4").

Definition O_T3168 : sobj := ltac2:(tb__ "0|3|
S18S1bZc60M0Zc61S0S4S4S12S1A2M1S9A2M2S3G1S9S3S12S1G0U1A4SbZ0A1A4S2G2A1A3A4").

Definition RT_fn : list sobj := ltac2:(tb__ "0|0|
S0S8S39Z1A1S0S8S3aS0S8S26S0S8S27S0S8S2aS0S8S2bS0S8S2cS0S8S28S0S8S29S0S8S21S0S8S22S0S8S1eS0S8S1fS0S8S38S0S8S20S0S8S24S0S8S25S0S8S23S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition F_geom_fn : list sprop := ltac2:(tb__ "0|3|
S0SaS10S2dS2eA2S0SaScSbZ1000M0A1M1S1bA2S0SaScS1bSbS47Z7fffff800000G0A2A1M2A2S0SaSfP97ZcA2S0SaScG1S1dA2S0SaScS1dG2A2S2SaA1A3A3A3A3A3A3").

Section FN.
Variable W : list ulink.
Variable st : ustop.

Definition P0_fn : axst := ltac2:(tb__ "0|1|
S3fSeS45S3bA1S30S32S0S4S1S9A2M0S3S1S9U4SbS1cA1A4S0G0S3S1S9UaSbZ0A1A4S0G0S3S1S9UbS11S44A1A4S2G0A1A3A3A3A2S2fSdS6S9A1S5S8S0S8S41S5S8S43VW;A1S3cA3A3S37A3S5SaS5SaS42VW;Vst;A2S40S3eA1A3S34A3S35S7A9S2S4S9S9A2A1A2").

Definition E_fn : axst := ltac2:(tb__ "0|1|
S3fSeS46S3bA1S30S31S19A1S0S4S1S9A2M0S3S1S9U4SbS1cA1A4S2G0A1A3A2S2fSdS6S9A1S5S8S0S8S41S5S8S43VW;A1S3cA3A3S37A3S5SaS5SaS42VW;Vst;A2S40S3eA1A3S34A3S35S7A9S2S4S9S9A2A1A2").
End FN.

Definition fn_cert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|2|
S15S1aUbb8S2S12A1S19S0S17S36S3dVn;A1M0Vst;A2S2S17A1M1A3S0S17S33G0Vst;A2G1A3A6").
Definition fn_ecert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|4|
S16S1aUbb8S2S12A1S19S0S13S14S36S3dVn;A1M0Vst;A2Z1SbZ0M1A1M2A3S2S13A1M3A3S0S13S14S33G0Vst;A2G1G2A3G3A3A6").

Lemma fn_cert_0 : fn_cert 0 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fn_cert_1 : fn_cert 1 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertFreeNull.

(* [comment removed for export] *)
Module GlueMA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "eqb"; "div"; "opp"; "to_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "gsv"; "@Corelib.Init.Datatypes"; "option"; "Some"; "bool"; "nat"; "true"; "list"; "None"; "fst"; "prod"; "app"; "pair"; "cons"; "false"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "acell"; "mkACell"; "view"; "RTC_A"; "cell_ok"; "rtc_cells"; "cells_ok"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "valuation"; "enc_bytes"; "sv"; "SLit"; "image_byte"; "obj_range"; "cell"; "holds"; "mkObj"; "odefault"; "rw"; "smatch"; "sobj"; "ss_objs"; "sstate"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ageom"; "ag_fsb"; "AA"; "aa_fs_busy"; "aa_geom"; "fs_release"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_busy"; "fs_footb"; "@Stdlib.Lists.List"; "In"; "nth_error"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "FS_total"; "Sh"; "FS_frames_off"; "FS_kFlagsOffset"; "fs_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "stack_win"; "F_sp_high"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma stack_win_range : ltac2:(tb__ "0|3|
S19S3dA1S2eS3cS1cS19S55A1S54A2S39R4R3R2R1A4S49S3aS52S3bR3A1A3S35R5S53A2SbS1Z7fff7f800000S1bS0S0S33R6S52A2M0A3M1A2SbSaS0S22S0S0G0A3M2S11Q40S38R6PaA2A2A3S1G1G2A2A2A2F_;F_;F_;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w Hsm Hin Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of, stack_win in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma obj_range_mk : ltac2:(tb__ "0|2|
S2eS30S0S0S19S34A1S37S1S8S4Z2Z3fA2M0A1R4A2S1R5R4A2S3R5G0A2SaS1cS0S0A2S33R9S36R8S31R7A1S31R6A1R5R4A5A2S1eS0S0S2S11Q40S2dR9R8A2A2M1R7A2S2G1R6A2A4A3F_;F_;F_;Fd;Fcs;Fhi;Flo;Fbase;Frho;").
Proof.
  intros. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Lemma cells_ok_nth : ltac2:(tb__ "0|0|
S2cS19S25A1S17S25S2bR4R3A2SaS14S25A1S4aS25R4R3A3S15S25R2A2A3S29R6R3A2F_;F_;Fc;Fi;Fcs;Fm;").
Proof. intros m cs i c H Hn. exact (proj1 (Forall_forall _ _) H c (nth_error_In _ _ Hn)). Qed.

Lemma wok_of_imageA : ltac2:(tb__ "0|1|
S10Q40M0A1S14S10Q8A1A1F_;S0SbS1Ze4000R1A2S3R1Z646000A2A2SaS16S24S12R3SfG0R2A2A3S18A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold wok_of. destruct (m (Z_to_bv 64 z)); [reflexivity|].
  unfold wseg_addr. rewrite u64_lit by lia.
  destruct (byte_cond_A z Hz) as [_ (seg & b & Hf & Hw & _)].
  change ImageFacts.segsA with segsA in Hf. rewrite Hf. exact Hw.
Qed.

Lemma find_segment_A_off : ltac2:(tb__ "0|0|
S0S1Z646000R1A2SaS14S3dA1S4cS12R2Z1A3S1aS3dA1A3F_;Fx;").
Proof.
  intros x Hx. unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 172032%N) with 172032.
  change (Z.of_N 237568%N) with 237568. change (Z.of_N 696320%N) with 696320.
  change (Z.of_N 933888%N) with 933888. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 954368%N) with 954368. change (Z.of_N 5623808%N) with 5623808.
  destruct (Z.leb_spec 65536 x); destruct (Z.leb_spec (x + 1) (65536 + 172032)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 237568 x); destruct (Z.leb_spec (x + 1) (237568 + 696320)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 933888 x); destruct (Z.leb_spec (x + 1) (933888 + 20480)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 954368 x); destruct (Z.leb_spec (x + 1) (954368 + 5623808)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma image_byte_A_off : ltac2:(tb__ "0|1|
S0SbS1Z646000R1A2S3R1S4Z2Z40A2A2A2SaS14S10Q8A1M0A1S32S12SfQ40R2A2A2S1aG0A1A3F_;Fx;").
Proof.
  intros x Hx. unfold image_byte, memory_read. rewrite u64_lit by lia.
  change (Z.of_N 1) with 1. rewrite find_segment_A_off by lia. reflexivity.
Qed.

Lemma rd_off_image : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z646000R2A2S3R2S4Z2Z40A2A2A2SaG2S23S12R4SfG0R3A2A3S15G1R2A2A3SaG2R5SfG0R4A2A1S15G1R3A2A3F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz H. unfold rd_of in H. destruct (m (Z_to_bv 64 z)); [exact H|].
  rewrite image_byte_A_off in H by lia. discriminate.
Qed.

Lemma wok_rd_off_image : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z646000R2A2S3R2S4Z2Z40A2A2A2SaG2S23S12R4SfG0R3A2A3S15G1R2A2A3SbSaS16S24S12R5SfG0R4A2A3S18A3ScG1G1SaG2S23S12R6SfG0R5A2A3S15G1R1A2A3Ly;A2A2F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz H. pose proof (rd_off_image m z x Hz H) as M.
  unfold wok_of, rd_of. rewrite M. split; [reflexivity | exists x; reflexivity].
Qed.

Lemma find_segment_A_off2 : ltac2:(tb__ "0|1|
S0S1Z0R1A2SdS1S2R2Z1M0A2Z10000A2S1Z646000R2A2A2SaS14S3dA1S4cS12R3G0A3S1aS3dA1A3F_;F_;Fx;").
Proof.
  intros x Hx0 [Hx|Hx]; [|apply find_segment_A_off; exact Hx].
  unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 172032%N) with 172032.
  change (Z.of_N 237568%N) with 237568. change (Z.of_N 696320%N) with 696320.
  change (Z.of_N 933888%N) with 933888. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 954368%N) with 954368. change (Z.of_N 5623808%N) with 5623808.
  destruct (Z.leb_spec 65536 x); destruct (Z.leb_spec (x + 1) (65536 + 172032)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 237568 x); destruct (Z.leb_spec (x + 1) (237568 + 696320)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 933888 x); destruct (Z.leb_spec (x + 1) (933888 + 20480)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 954368 x); destruct (Z.leb_spec (x + 1) (954368 + 5623808)); cbn [andb]; try lia; reflexivity.
Qed.
Lemma image_byte_A_off2 : ltac2:(tb__ "0|1|
S0SbS1Z0R1A2S3R1S4Z2Z40A2A2A2SdS1S2R2Z1A2Z10000A2S1Z646000R2A2A2SaS14S10Q8A1M0A1S32S12SfQ40R3A2A2S1aG0A1A3F_;F_;Fx;").
Proof.
  intros x Hx Ho. unfold image_byte, memory_read. rewrite u64_lit by lia.
  change (Z.of_N 1) with 1. rewrite find_segment_A_off2 by lia. reflexivity.
Qed.
Lemma rd_off_image2 : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z0R2A2S3R2S4Z2Z40A2A2A2SdS1S2R3Z1A2Z10000A2S1Z646000R3A2A2SaG2S23S12R5SfG0R4A2A3S15G1R3A2A3SaG2R6SfG0R5A2A1S15G1R4A2A3F_;F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz Ho H. unfold rd_of in H. destruct (m (Z_to_bv 64 z)); [exact H|].
  rewrite image_byte_A_off2 in H by lia. discriminate.
Qed.
Lemma wok_rd_off_image2 : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z0R2A2S3R2S4Z2Z40A2A2A2SdS1S2R3Z1A2Z10000A2S1Z646000R3A2A2SaG2S23S12R5SfG0R4A2A3S15G1R3A2A3SbSaS16S24S12R6SfG0R5A2A3S18A3ScG1G1SaG2S23S12R7SfG0R6A2A3S15G1R1A2A3Ly;A2A2F_;F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz Ho H. pose proof (rd_off_image2 m z x Hz Ho H) as M.
  unfold wok_of, rd_of. rewrite M. split; [reflexivity | exists x; reflexivity].
Qed.

Lemma fs_footb_true2 : ltac2:(tb__ "0|1|
S3eS0SbS1S2S3fR2A1M0S50A2R1A2S3R1S2G0S4dA2A2A2SaS16S48R3R2A2S18A3F_;Fz;FG;").
Proof.
  intros G z Hz. unfold fs_footb. cbn zeta. apply orb_true_intro. left. apply orb_true_intro. right.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma fs_footb_true3 : ltac2:(tb__ "0|1|
S3eS0SbS1S4eS2S3fR2A1M0S4fA2A1R1A2S3R1S4eS2G0S4dA2A1A2A2SaS16S48R3R2A2S18A3F_;Fz;FG;").
Proof.
  intros G z Hz. unfold fs_footb. cbn zeta. apply orb_true_intro. right.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma fs_footb_true1 : ltac2:(tb__ "0|1|
S3eS0SbS1S3fR2A1M0R1A2S3R1S2G0Z58A2A2A2SaS16S48R3R2A2S18A3F_;Fz;FG;").
Proof.
  intros G z Hz. unfold fs_footb. cbn zeta. apply orb_true_intro. left. apply orb_true_intro. left.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma existsb_app : forall {T} (g : T -> bool) l1 l2, existsb g (l1 ++ l2) = existsb g l1 || existsb g l2.
Proof. intros T g l1 l2. induction l1; cbn; [reflexivity|]. rewrite IHl1, orb_assoc. reflexivity. Qed.

Lemma existsb_pos_false : ltac2:(tb__ "0|1|
S19S1cS0S0A2M0A1S0SeS49S0R1S46G0S0S1bS0S0A2R2A4A3A1SaS16S4bG0G0S6S1bS0S0R1A3R3A2Lpf;R3A3S20A3F_;Fpos;Fl;").
Proof.
  induction l as [|[p g] l IH]; intros pos Hn; cbn; [reflexivity|].
  destruct (Z.eqb_spec p pos); [exfalso; apply Hn; left; cbn; lia|]. cbn. apply IH. intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma fs_busy_release : ltac2:(tb__ "0|3|
S40S0S0S0S19S1cS0S0A2M0A1M1G1S1Z0M2R5A2S1G2R4A2S44S9R7A1S21G1S41R8A1A2A2SaG1S47R9R8A2S1dG0R5S1fG0S1eS0S0R7S51S3fS42R9A1A1R8R7A3A4R4A3A3A3SeS49S0R8S46G0S0S1bS0S0A2R6A4A3A1SaG1S47S43RbRaR9A3R8A2S16G1L_;S6R8RaA2S1dG0R7R6A3S47RbR8A2X16x2A3F_;F_;F_;F_;F_;Fv;Fu;Fc0;Fpos;Fc;FA;").
Proof.
  intros A c pos c0 u v Hc Hc0 Hlen E Hn. unfold fs_busy, nthZ, fs_release. cbn [aa_fs_busy].
  destruct (Z.eqb_spec c0 c).
  - subst c0. rewrite nth_list_upd_same by exact Hlen. change (nth (Z.to_nat c) (aa_fs_busy A) []) with (fs_busy A c).
    rewrite E. apply remove_pos_split. exact Hn.
  - rewrite nth_list_upd_other; [reflexivity|]. intros E'. apply n. lia.
Qed.

Lemma gsv_val : ltac2:(tb__ "0|1|
S2eS30SaS0S11Q40M0S2dR2S13R1A1A2A2S7S11G0S2dR2R1A2A2Z8A2A3Fe;Frho;").
Proof. intros. unfold gsv. cbn [eval]. rewrite srl_val. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma nth0_enc1_zero : ltac2:(tb__ "0|4|
S2eSaS10Q8M0A1M1S45G1U0S2fU1S2dR1S31Z0M2A1A2A2SfG0G2A2M3A4G3A3Frho;").
Proof. intros. reflexivity. Qed.

Lemma rd_of_imageA : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0SbS1Ze4000R1A2S3R1Z646000A2A2ScG1G1SaG2S23S12R4SfG0R3A2A3S15G1R1A2A3Lx;A2F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold rd_of. destruct (m (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity|].
  destruct (byte_cond_A z Hz) as [[b Hb] _]. exists b. exact Hb.
Qed.

Lemma civ_cell : ltac2:(tb__ "0|6|
S2eS10Q40M0A1M1S14S10Q8M2A1M3A1M4F_;S0S0S17S0S30S29S27S12R6A2S26S2R5R4A2R3R2A3A2SaG1S2dR8R2A2SfG0R3A2A3S1Z0M5S2R7R6A2A2S1S2S2R8R7A2S5R6A1A2S4Z2Z40A2A2S17S44R1R8A2SaG4S23S12RcSfG0S2S2RbRaA2S5R2A1A2A2A3S15G3S45G3R2S2fR9S2dRdR7A2A2SfG2G5A2A4A2A3F_;Fj;F_;F_;F_;F_;Fe;Fv;Fk;Foff;Fb;Fm;Frho;").
Proof.
  intros rho m b off k v e Hc He Hb1 Hb2 j Hj. rewrite He. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. exact Hc.
Qed.

Lemma civ_nth : ltac2:(tb__ "0|6|
S2eS10Q40M0A1M1S14S10Q8M2A1M3A1M4F_;S3eS17S0S17S0S0S0S30S2bS27S12R9A2S2aS28R8A2A2SaS14S25A1S4aS25S2aS28R9A2R8A3S15S25S26R7R6R5A3A2A3SaS0R8S2R5R4A2A3SaG1S2dRdR4A2SfG0R7A2A3S1Z0M5RaA2S1S2RbS5RaA1A2S4Z2Z40A2A2S17S44R1RcA2SaG4S23S12R11SfG0S2S2RbRaA2S5R2A1A2A2A3S15G3S45G3R2S2fRdS2dR12R9A2A2SfG2G5A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Foff;Fb;Fv;Fk;Fa;Fn;FG;Fm;Frho;").
Proof.
  intros rho m G n a k v b off e HR Hn -> He Ha1 Ha2. eapply civ_cell; eauto. eapply cells_ok_nth; eauto.
Qed.

Lemma cell_wok_rd : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0S17S0S0S29S27S12R5A2S26R4R3R2A3A2SbS1R5R2A2S3R2S2R5S5R4A1A2A2A2S1Z646000R6A2S1S2R7S5R6A1A2S4Z2Z40A2A2SbSaS16S24S12R9SfG0R5A2A3S18A3ScG1G1SaG2S23S12RaSfG0R6A2A3S15G1R1A2A3Ly;A2A2F_;F_;F_;F_;Fz;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v z Hc Hz Ha1 Ha2. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in Hc by lia.
  eapply wok_rd_off_image; [lia | exact Hc].
Qed.

Lemma cell_wok_rd2 : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0S17S0S0S29S27S12R5A2S26R4R3R2A3A2SbS1R5R2A2S3R2S2R5S5R4A1A2A2A2S1Z0R6A2SdS1S2R7S5R6A1A2Z10000A2S1Z646000R7A2A2S1S2R8S5R7A1A2S4Z2Z40A2A2SbSaS16S24S12RaSfG0R6A2A3S18A3ScG1G1SaG2S23S12RbSfG0R7A2A3S15G1R1A2A3Ly;A2A2F_;F_;F_;F_;F_;Fz;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v z Hc Hz Ha0 Ho Ha2. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in Hc by lia.
  eapply wok_rd_off_image2; [lia | lia | exact Hc].
Qed.

Ltac civ_try HR E n :=
  eapply (civ_nth _ _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | cbn [eval]; E; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Ltac civ_any HR E := first [ civ_try HR E 0%nat | civ_try HR E 1%nat | civ_try HR E 2%nat | civ_try HR E 3%nat | civ_try HR E 4%nat | civ_try HR E 5%nat | civ_try HR E 6%nat | civ_try HR E 7%nat | civ_try HR E 8%nat | civ_try HR E 9%nat | civ_try HR E 10%nat | civ_try HR E 11%nat | civ_try HR E 12%nat | civ_try HR E 13%nat | civ_try HR E 14%nat | civ_try HR E 15%nat | civ_try HR E 16%nat | civ_try HR E 17%nat | civ_try HR E 18%nat | civ_try HR E 19%nat | civ_try HR E 20%nat | civ_try HR E 21%nat | civ_try HR E 22%nat | civ_try HR E 23%nat | civ_try HR E 24%nat | civ_try HR E 25%nat | civ_try HR E 26%nat | civ_try HR E 27%nat | civ_try HR E 28%nat | civ_try HR E 29%nat | civ_try HR E 30%nat | civ_try HR E 31%nat | civ_try HR E 32%nat | civ_try HR E 33%nat | civ_try HR E 34%nat | civ_try HR E 35%nat | civ_try HR E 36%nat | civ_try HR E 37%nat | civ_try HR E 38%nat | civ_try HR E 39%nat | civ_try HR E 40%nat | civ_try HR E 41%nat | civ_try HR E 42%nat | civ_try HR E 43%nat | civ_try HR E 44%nat | civ_try HR E 45%nat | civ_try HR E 46%nat | civ_try HR E 47%nat | civ_try HR E 48%nat | civ_try HR E 49%nat | civ_try HR E 50%nat | civ_try HR E 51%nat | civ_try HR E 52%nat | civ_try HR E 53%nat | civ_try HR E 54%nat ].
Lemma civ_nth2 : ltac2:(tb__ "0|5|
S10Q40M0A1S14S10Q8M1A1M2A1M3F_;S3eS17S0S17S0S0S0S2bS27S12R8A2S2aS28R7A2A2SaS14S25A1S4aS25S2aS28R8A2R7A3S15S25S26R6R5R4A3A2A3SaS0R7S2R4R3A2A3S1Z0M4R8A2S1S2R9S5R8A1A2S4Z2Z40A2A2S17S44R1RaA2SaG3S23S12RfSfG0S2S2R9R8A2S5R2A1A2A2A3S15G2S45G2R2S2fRbSfG0RaA2A2SfG1G4A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;Foff;Fb;Fv;Fk;Fa;Fn;FG;Fm;").
Proof.
  intros m G n a k v b off HR Hn -> Ha1 Ha2 j Hj. pose proof (cells_ok_nth _ _ n _ HR Hn j Hj) as C. cbn [c_addr c_w c_val] in C.
  rewrite view_in in C by lia. exact C.
Qed.
Ltac civ_try2 HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Ltac civ_any2 HR := first [ civ_try2 HR 0%nat | civ_try2 HR 1%nat | civ_try2 HR 2%nat | civ_try2 HR 3%nat | civ_try2 HR 4%nat | civ_try2 HR 5%nat | civ_try2 HR 6%nat | civ_try2 HR 7%nat | civ_try2 HR 8%nat | civ_try2 HR 9%nat | civ_try2 HR 10%nat | civ_try2 HR 11%nat | civ_try2 HR 12%nat | civ_try2 HR 13%nat | civ_try2 HR 14%nat | civ_try2 HR 15%nat | civ_try2 HR 16%nat | civ_try2 HR 17%nat | civ_try2 HR 18%nat | civ_try2 HR 19%nat | civ_try2 HR 20%nat | civ_try2 HR 21%nat | civ_try2 HR 22%nat | civ_try2 HR 23%nat | civ_try2 HR 24%nat | civ_try2 HR 25%nat | civ_try2 HR 26%nat | civ_try2 HR 27%nat | civ_try2 HR 28%nat | civ_try2 HR 29%nat | civ_try2 HR 30%nat | civ_try2 HR 31%nat | civ_try2 HR 32%nat | civ_try2 HR 33%nat | civ_try2 HR 34%nat | civ_try2 HR 35%nat | civ_try2 HR 36%nat | civ_try2 HR 37%nat | civ_try2 HR 38%nat | civ_try2 HR 39%nat | civ_try2 HR 40%nat | civ_try2 HR 41%nat | civ_try2 HR 42%nat | civ_try2 HR 43%nat | civ_try2 HR 44%nat | civ_try2 HR 45%nat | civ_try2 HR 46%nat | civ_try2 HR 47%nat | civ_try2 HR 48%nat | civ_try2 HR 49%nat | civ_try2 HR 50%nat | civ_try2 HR 51%nat | civ_try2 HR 52%nat | civ_try2 HR 53%nat | civ_try2 HR 54%nat ].

Ltac wr_cell HR n :=
  eapply (cell_wok_rd _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell; lia.

Ltac wr_cell2 HR n tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell; [lia | lia | tacW | lia].
Ltac wr_any2 HR tacW := first [ wr_cell2 HR 43%nat tacW | wr_cell2 HR 44%nat tacW | wr_cell2 HR 45%nat tacW | wr_cell2 HR 46%nat tacW | wr_cell2 HR 47%nat tacW | wr_cell2 HR 48%nat tacW | wr_cell2 HR 49%nat tacW | wr_cell2 HR 50%nat tacW | wr_cell2 HR 51%nat tacW | wr_cell2 HR 52%nat tacW | wr_cell2 HR 53%nat tacW | wr_cell2 HR 54%nat tacW ].
Ltac wr_any HR := first [ wr_cell HR 43%nat | wr_cell HR 44%nat | wr_cell HR 45%nat | wr_cell HR 46%nat | wr_cell HR 47%nat | wr_cell HR 48%nat | wr_cell HR 49%nat | wr_cell HR 50%nat | wr_cell HR 51%nat | wr_cell HR 52%nat | wr_cell HR 53%nat | wr_cell HR 54%nat ].

End GlueMA.

