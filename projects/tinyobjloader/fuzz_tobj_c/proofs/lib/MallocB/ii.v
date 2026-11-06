(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih ij.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillJ.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.

(* [comment removed for export] *)
Module UnwT_loop.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "SLit"; "sv"; "SVar"; "cell"; "mkCell"; "ss_objs"; "dflt_writable"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "holds"; "obj_range"; "ranges_disjoint"; "rm"; "sprop"; "ss_facts"; "ss_lenient"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "app"; "cons"; "nat"; "nil"; "Some"; "false"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "le"; "pow"; "add"; "lt"; "to_nat"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "PRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop.TolLoop"; "InvT"; "InvTe"; "eleaf_ok"; "leaf_ok"; "side"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJAF TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section TolLoop.
Variable segs : list Segment.
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.
Variable ok : world -> Prop.
Variable J : jpredA.
Hypothesis Jok : ltac2:(tb__ "0|0|
S27Vsegs;Vok;VJ;A3").
Hypothesis Jst : ltac2:(tb__ "0|0|
S28Vsegs;S36VJ;A3").
Variables LT EX : axst.
Variable bFR : sv.
Variable tp : list word.
Variable Q : assn.
Variables (fuel : nat) (cuts : list Z) (l3 : list leafA).

Let nx : positive := ss_next (ax_S LT).
Hypothesis LT_nx : (GW <= nx)%positive.
Hypothesis LT_len : ltac2:(tb__ "0|0|
S0S1bS18S29VLT;A1A1S23A3").
Hypothesis CWF : ltac2:(tb__ "0|0|
S0S1bS1aS29S45VLT;VbFR;A2A1A1S1cA3").
Hypothesis bFR_below : ltac2:(tb__ "0|0|
S0S1bS19Vnx;VbFR;A2S1cA3").
Hypothesis RUN3 : ltac2:(tb__ "0|1|
S0S24S1dS2aA1M0A1S2dVsegs;Vfuel;Vcuts;S44VLT;VbFR;A2S1cA5S22G0Vl3;A2A3").

Definition side (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S33Vrho;VbFR;A2S34S1S38S3aS42Z10M0A2R1A2S1S38R1S39Z2Z3eA2A2S1S3dS4S4S14S13Vrho;R1A2S25S34S34S37R2G0A2R2A4A2Lo';SbS29VLT;A1A1A3S1S43Vsegs;S15Vrho;A1S37R1G0A2M1R1A4S41Vrho;VLT;G1R1A4A2A2A2A2TB;").
Hypothesis HSIDE : ltac2:(tb__ "0|0|
S5S30S26Vsegs;VJ;VLT;R2Vtp;R1A6S4aR3A1F_;Fw;Frho;").

Definition leaf_ok (L : leafA) : Prop := ltac2:(tb__ "0|6|
S2S1dS4A1M0G0S2S4S4S1S0G0SbS29S2cVL;A1M1A1A1S1eS4R2S1fS4R1S21S4A1A3A3A3S1S0S7SdR1A1VbFR;A3S1S0S7S11R1A1S6N10A1M2A3S1S0S7S10R1A1S6Z0A1A3S1S0S1bScSfR1A1A1S1cA3S1S2fS9SaG2Z8M3S8Vnx;A1A3SeR1A1M4A3S1S2fS9SaS6N8A1G3S8S40Vnx;A1A1A3G4A3S3S0S1bS2eS35G1R2A2M5VLT;A2S1cA3S0S1bS2eG5VEX;A2S1cA3A2A2A2A2A2A2A2A2Lo;A2Lobjs;A2").
Hypothesis LEAVES : ltac2:(tb__ "0|0|
S2aS2fS2aR1Vl3;A3S49R2A1F_;FL;").

Lemma entsF_SPA : ltac2:(tb__ "0|0|
S2bS2bS5S30S0S1bS2eR4R3A2S1cA3S26Vsegs;VJ;R5R3Vtp;R2A6S2S5S5S26Vsegs;VJ;R6R1Vtp;R4A6Lrho';A2F_;F_;Fw;Frho;FT;FL;").
Proof using Jst.
  intros L T rho w H HS. unfold entsF in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [He Hid].
  exists (rho_sub rho (infer_sub GW (ax_S L) (ax_S T))). exact (SPA_entails segs J GW L T _ rho tp w He Hid Jst HS).
Qed.

Definition InvT : assn := ltac2:(tb__ "0|0|
S30S2S5S5S26Vsegs;VJ;VLT;R1Vtp;R2A6Lrho;A2Lw;").

Theorem tol_loop : ltac2:(tb__ "0|0|
S5S32Vsegs;Vok;S26Vsegs;VJ;VEX;R1Vtp;A5VQ;A4Frho;S32Vsegs;Vok;S46VQ;A4F_;").
Proof using HTOP Jok Jst LT_nx LT_len CWF bFR_below RUN3 HSIDE LEAVES.
  intros HEX. apply triple_loop. unfold InvT at 1. apply triple1_ex. intros rho.

  eapply triple1_conseq with (P := fun w => exists rho', (agree_below nx rho rho' /\ side rho
            /\ rd64 (rm rho) (uval rho bFR - 16) = Some (uval rho' (SVar nx))
            /\ rd64 (rm rho) (uval rho bFR - 8) = Some (uval rho' (SVar (Pos.succ nx))))
            /\ SPA segs J (carve_link_state LT bFR) rho' tp w).
  { intros w Hw. pose proof (HSIDE rho w Hw) as HSd. pose proof HSd as (B1 & B2 & HD & HP & HX). destruct w as [tr [ms md]].
    destruct (carve_link segs HTOP J LT bFR rho tp tr ms md ltac:(apply (stableA_mono segs GW); [exact LT_nx | exact Jst]) CWF B1 B2 HD HP HX Hw)
      as (rho' & Hag & R0 & R1 & SP).
    exists rho'. split; [|exact SP]. split; [exact Hag|]. split; [exact HSd | split; [exact R0 | exact R1]]. }
  { intros w Hw. exact Hw. }
  apply triple1_ex. intros rho'. apply triple1_pure. intros (Hag & HSd & R0 & R1).
  destruct HSd as (B1 & B2 & _).

  eapply triple1_seq_l.
  { apply (sym_run_soundA segs fuel cuts (carve_link_state LT bFR) l3 ok J rho' tp RUN3 Jok).
    - unfold carve_link_state. rewrite ax_S_setS. cbn [ss_lenient]. exact LT_len.
    - apply (stableA_mono segs GW); [|exact Jst]. unfold carve_link_state. rewrite ax_S_setS. cbn [ss_next]. fold nx. lia. }
  apply triple_LQA_of_leaves. intros L rhoL HinL HagL.
  assert (Enx2 : ss_next (ax_S (carve_link_state LT bFR)) = Pos.succ (Pos.succ nx)) by (unfold carve_link_state; rewrite ax_S_setS; reflexivity).
  rewrite Enx2 in HagL.
  destruct (LEAVES L HinL) as (objs & o & Hobjs & Hb & Hl & Hh & Hdw & Hc0 & Hc1 & Hent).

  assert (EB : uval rhoL (ob_base o) = uval rho bFR).
  { rewrite Hb. unfold uval. f_equal.
    rewrite <- (eval_agree (Pos.succ (Pos.succ nx)) rho' rhoL bFR HagL ltac:(eapply sv_below_mono; [|exact bFR_below]; lia)).
    symmetry. apply (eval_agree nx rho rho' bFR Hag bFR_below). }
  assert (Erm : rm rhoL = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros a.
    destruct HagL as (_ & _ & M2). destruct Hag as (_ & _ & M1). rewrite <- M2, <- M1. reflexivity. }
  assert (Ev0 : uval rhoL (SVar nx) = uval rho' (SVar nx)).
  { unfold uval. f_equal. symmetry. apply (eval_agree (Pos.succ (Pos.succ nx)) rho' rhoL (SVar nx) HagL). cbn. apply Pos.ltb_lt. lia. }
  assert (Ev1 : uval rhoL (SVar (Pos.succ nx)) = uval rho' (SVar (Pos.succ nx))).
  { unfold uval. f_equal. symmetry. apply (eval_agree (Pos.succ (Pos.succ nx)) rho' rhoL (SVar (Pos.succ nx)) HagL). cbn. apply Pos.ltb_lt. lia. }
  assert (DIS : forall w, SPA segs J (la_state L) rhoL tp w -> SPA segs J (drop_lastA (la_state L) objs) rhoL tp w).
  { intros [tr [ms md]] Hw.
    apply (dissolve_link_same segs HTOP J (la_state L) objs o (SVar nx) (SVar (Pos.succ nx)) rhoL tp tr ms md Hobjs Hl Hh Hdw Hc0 Hc1);
      rewrite ?EB, ?Erm, ?Ev0, ?Ev1; assumption. }
  destruct Hent as [HL | HE].
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. left. destruct (entsF_SPA _ _ rhoL w HL (DIS w Hw)) as (rho2 & S2). exists rho2. exact S2.
  -
    intros n Hg w Hw. destruct (entsF_SPA _ _ rhoL w HE (DIS w Hw)) as (rho2 & S2).
    apply (HEX rho2 n); [|exact S2]. intros w' Hq. apply Hg. right. exact Hq.
Qed.

Variable Qe : world -> Prop.
Definition eleaf_ok (L : leafA) : Prop := ltac2:(tb__ "0|7|
S2S1dS4A1M0G0S2S4S4S1S0G0SbS29S2cVL;A1M1A1M2A1S1eS4R2S1fS4R1S21S4A1A3A3A3S1S0S7SdR1A1VbFR;A3S1S0S7S11R1A1S6N10A1M3A3S1S0S7S10R1A1S6Z0A1A3S1S0S1bScSfR1A1A1S1cA3S1S2fS9SaG3Z8M4S8Vnx;A1A3SeR1A1M5A3S1S2fS9SaS6N8A1G4S8S40Vnx;A1A1A3G5A3S3S1S0S1bS2eS35G1R2A2M6VLT;A2S1cA3S5S3dS16S12R1A1S17G2A1A3S3bS33R2VbFR;A2S33S3fR2S3eS36S29S35G1R4A2A1S29VLT;A1A3A2VbFR;A2A2F_;FrhoL;A2S0S1bS2eG6VEX;A2S1cA3A2A2A2A2A2A2A2A2Lo;A2Lobjs;A2").
Hypothesis ELEAVES : ltac2:(tb__ "0|0|
S2aS2fS2aR1Vl3;A3S48R2A1F_;FL;").

Lemma entsF_SPA_sub : ltac2:(tb__ "0|0|
S2bS2bS5S30S0S1bS2eR4R3A2S1cA3S26Vsegs;VJ;R5R3Vtp;R2A6S26Vsegs;VJ;R5S3fR4S3eS36S29R6A1S29R5A1A3A2Vtp;R3A6F_;F_;Fw;Frho;FT;FL;").
Proof using Jst.
  intros L T rho w H HS. unfold entsF in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [He Hid].
  exact (SPA_entails segs J GW L T _ rho tp w He Hid Jst HS).
Qed.

Definition InvTe (a : nat) : world -> Prop := ltac2:(tb__ "0|0|
S30S2S5S5S1S0S20S3cS37S39Z2Z40A2S33R1VbFR;A2A2A1Va;A3S26Vsegs;VJ;VLT;R1Vtp;R2A6A2Lrho;A2Lw;").

Theorem etol_loop : ltac2:(tb__ "0|0|
S5S31Vsegs;S26Vsegs;VJ;VEX;R1Vtp;A5VQe;A3Frho;S20S31Vsegs;S47R1A1VQe;A3Fa;F_;").
Proof using HTOP Jst LT_nx LT_len CWF bFR_below RUN3 HSIDE ELEAVES.
  intros HEX. apply (etriple_loop (A := nat) (R := lt) Wf_nat.lt_wf InvTe Qe). intros a.
  unfold InvTe at 1. apply etriple_ex. intros rho. apply etriple_pure. intros Ha.
  eapply etriple_conseq with (P := fun w => exists rho', (agree_below nx rho rho' /\ side rho
            /\ rd64 (rm rho) (uval rho bFR - 16) = Some (uval rho' (SVar nx))
            /\ rd64 (rm rho) (uval rho bFR - 8) = Some (uval rho' (SVar (Pos.succ nx))))
            /\ SPA segs J (carve_link_state LT bFR) rho' tp w).
  { intros w Hw. pose proof (HSIDE rho w Hw) as HSd. pose proof HSd as (B1 & B2 & HD & HP & HX). destruct w as [tr [ms md]].
    destruct (carve_link segs HTOP J LT bFR rho tp tr ms md ltac:(apply (stableA_mono segs GW); [exact LT_nx | exact Jst]) CWF B1 B2 HD HP HX Hw)
      as (rho' & Hag & R0 & R1 & SP).
    exists rho'. split; [|exact SP]. split; [exact Hag|]. split; [exact HSd | split; [exact R0 | exact R1]]. }
  { intros w Hw. exact Hw. }
  apply etriple_ex. intros rho'. apply etriple_pure. intros (Hag & HSd & R0 & R1).
  destruct HSd as (B1 & B2 & _).
  eapply etriple_seq.
  { apply (sym_run_etripleA segs fuel cuts (carve_link_state LT bFR) l3 J rho' tp); [| | exact RUN3].
    - unfold carve_link_state. rewrite ax_S_setS. cbn [ss_lenient]. exact LT_len.
    - apply (stableA_mono segs GW); [|exact Jst]. unfold carve_link_state. rewrite ax_S_setS. cbn [ss_next]. fold nx. lia. }
  apply etriple_LQA_of_leaves. intros L rhoL HinL HagL.
  assert (Enx2 : ss_next (ax_S (carve_link_state LT bFR)) = Pos.succ (Pos.succ nx)) by (unfold carve_link_state; rewrite ax_S_setS; reflexivity).
  rewrite Enx2 in HagL.
  destruct (ELEAVES L HinL) as (objs & o & Hobjs & Hb & Hl & Hh & Hdw & Hc0 & Hc1 & Hent).
  assert (EBF : uval rhoL bFR = uval rho bFR).
  { unfold uval. f_equal.
    rewrite <- (eval_agree (Pos.succ (Pos.succ nx)) rho' rhoL bFR HagL ltac:(eapply sv_below_mono; [|exact bFR_below]; lia)).
    symmetry. apply (eval_agree nx rho rho' bFR Hag bFR_below). }
  assert (EB : uval rhoL (ob_base o) = uval rho bFR) by (rewrite Hb; exact EBF).
  assert (Erm : rm rhoL = rm rho).
  { apply FunctionalExtensionality.functional_extensionality. intros x.
    destruct HagL as (_ & _ & M2). destruct Hag as (_ & _ & M1). rewrite <- M2, <- M1. reflexivity. }
  assert (Ev0 : uval rhoL (SVar nx) = uval rho' (SVar nx)).
  { unfold uval. f_equal. symmetry. apply (eval_agree (Pos.succ (Pos.succ nx)) rho' rhoL (SVar nx) HagL). cbn. apply Pos.ltb_lt. lia. }
  assert (Ev1 : uval rhoL (SVar (Pos.succ nx)) = uval rho' (SVar (Pos.succ nx))).
  { unfold uval. f_equal. symmetry. apply (eval_agree (Pos.succ (Pos.succ nx)) rho' rhoL (SVar (Pos.succ nx)) HagL). cbn. apply Pos.ltb_lt. lia. }
  assert (DIS : forall w, SPA segs J (la_state L) rhoL tp w -> SPA segs J (drop_lastA (la_state L) objs) rhoL tp w).
  { intros [tr [ms md]] Hw.
    apply (dissolve_link_same segs HTOP J (la_state L) objs o (SVar nx) (SVar (Pos.succ nx)) rhoL tp tr ms md Hobjs Hl Hh Hdw Hc0 Hc1);
      rewrite ?EB, ?Erm, ?Ev0, ?Ev1; assumption. }
  destruct Hent as [[HL HUP] | HE].
  - eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
    intros w Hw. left.
    pose proof (HUP rhoL (smatchA_facts segs _ _ _ _ (proj1 Hw))) as UP. rewrite EBF in UP.
    set (rho2 := rho_sub rhoL (infer_sub GW (ax_S (drop_lastA (la_state L) objs)) (ax_S LT))) in *.
    exists (Z.to_nat (2 ^ 64 - uval rho2 bFR)). split.
    + rewrite <- Ha. pose proof (uval_range rho2 bFR). pose proof (uval_range rho bFR). lia.
    + exists rho2. split; [reflexivity|]. exact (entsF_SPA_sub _ _ rhoL w HL (DIS w Hw)).
  - eapply etriple_conseq; [intros w Hw; exact (entsF_SPA_sub _ _ rhoL w HE (DIS w Hw)) | intros w Hq; right; exact Hq | apply HEX].
Qed.
End TolLoop.
End UnwT_loop.

(* [comment removed for export] *)
Module SecBump.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "aa_frames"; "budget_bound"; "budget_ok_alloc"; "ageom"; "class_state"; "depot_state"; "mkAA"; "qbatch"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayCommit"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "bumpV"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.
Import ListNotations.
Open Scope Z_scope.

Definition bumpP (A : AA) : AA := ltac2:(tb__ "0|0|
S1dS10VA;A1ScVA;A1SbVA;A1S16VA;A1S22S13VA;A1S21A2S12VA;A1S15VA;A1S14VA;A1SdVA;A1SfVA;A1SeVA;A1S11VA;A1SaVA;A1S9VA;A1S8VA;A1Af").
Lemma bumpP_same : ltac2:(tb__ "0|3|
S7S1S0S1aS10S20R1A1M0A1S10R1A1A3S1S0S4S1bA1ScG0A1ScR1A1A3S1S0S5SbG0A1SbR1A1A3S1S0S4S1fA1S16G0A1S16R1A1A3S1S0S3S13G0A1S22S13R1A1S21A2A3S1S0S4S6S3S3A2A1M1S12G0A1S12R1A1A3S1S0S4S1eA1M2S15G0A1S15R1A1A3S1S0G2S14G0A1S14R1A1A3S1S0S1cSdG0A1SdR1A1A3S1S0S4S3A1SfG0A1SfR1A1A3S1S0S4G1A1SeG0A1SeR1A1A3S1S0S5S11G0A1S11R1A1A3S1S0G1S17G0A1S17R1A1A3S1S0S3SaG0A1SaR1A1A3S1S0S3S9G0A1S9R1A1A3S0S3S8G0A1S8R1A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2FA;").
Proof. intros A. repeat split; reflexivity. Qed.
Lemma bumpP_bumpV : ltac2:(tb__ "0|0|
S7S3S0S7S20S24R2R1A2A1S24S20R2A1R1A2A3Fn;FA;").
Proof. intros A n. reflexivity. Qed.
Lemma budget_boundD_bumpP : ltac2:(tb__ "0|0|
S7S0S3S23S20R1A1A1S22S23R1A1S21A2A3FA;").
Proof. intros A. unfold budget_boundD. cbn [aa_V aa_Km aa_Kf aa_ptr_committed aa_depot bumpP]. lia. Qed.
Lemma budget_bound_bumpP : ltac2:(tb__ "0|0|
S7S0S3S18S20R1A1A1S18R1A1A3FA;").
Proof. intros A. reflexivity. Qed.
Lemma budget_ok_alloc_bumpP : ltac2:(tb__ "0|0|
S7S3S2S19S20R2A1R1A2S19R2R1A2A2Fn;FA;").
Proof. intros A n. unfold budget_ok_alloc. cbn [aa_V aa_Km aa_Kf bumpP]. tauto. Qed.
End SecBump.

(* [comment removed for export] *)
Module RefillJP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "or"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "piece"; "ph_set"; "ph_get"; "ph_quiet"; "pord"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "phase"; "zoneR"; "mlink"; "rlink"; "ph_f"; "mkPh"; "ph_cnt"; "ph_fill"; "ph_pop"; "ph_ri"; "ph_u"; "F0"; "U0"; "shpage"; "@Corelib.Init.Datatypes"; "nat"; "list"; "None"; "app"; "bool"; "false"; "option"; "length"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "maps_subtract"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP.JP"; "pbase"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive piece : Set := PU | PF.

Definition ph_get (p : piece) (ph : phase) : nat := ltac2:(tb__ "0|0|
S6S1aLp;Vp;S16Vph;A1S10Vph;A1X6x2").
Definition ph_set (p : piece) (n : nat) (ph : phase) : phase := ltac2:(tb__ "0|4|
S6ScLp;Vp;S11Vn;S10Vph;A1S13Vph;A1M0S14Vph;A1M1S12Vph;A1M2S15Vph;A1M3A6S11S16Vph;A1Vn;G0G1G2G3A6X6x2").

Definition pord (p : piece) (ph : phase) : Prop := ltac2:(tb__ "0|0|
S6OLp;Vp;S0S1aS10Vph;A1U0A3S5X6x2").
Definition ph_quiet (ph : phase) : Prop := ltac2:(tb__ "0|1|
S1S0SbS13Vph;A1Z0M0A3S1S0SbS14Vph;A1G0A3S1S0S1eS12Vph;A1S1fA3S0S1eS15Vph;A1S1fA3A2A2A2").

Lemma ph_get_set : ltac2:(tb__ "0|0|
S6S1aScS0S1aS8R3S7R3R2R1A3A2R2A3Fph;Fn;Fp;").
Proof. intros [|] n ph; reflexivity. Qed.
Lemma ph_set_set : ltac2:(tb__ "0|0|
S6S1aS1aScS0ScS7R4R2S7R4R3R1A3A3S7R4R2R1A3A3Fph;Fn';Fn;Fp;").
Proof. intros [|] n n' ph; reflexivity. Qed.
Lemma ph_quiet_set : ltac2:(tb__ "0|0|
S6S1aScS9R1A1S9S7R4R3R2A3A1F_;Fph;Fn;Fp;").
Proof. intros [|] n ph H; exact H. Qed.
Lemma pord_set : ltac2:(tb__ "0|0|
S6S1aScSaR3R1A2SaR4S7R4R3R2A3A2F_;Fph;Fn;Fp;").
Proof. intros [|] n ph H; exact H. Qed.

Section JP.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model).
Definition pbase (p : piece) : Z := ltac2:(tb__ "0|0|
S6SbLp;Vp;S18VA;Vrb;A2S17VA;Vrb;A2X6x2").

Lemma mlink_commit : ltac2:(tb__ "0|9|
S6ScS1bS32Q40A1M0A1S24S24SeVA;Vrb;Vtp0;Vmd0;R4R3R2A7S0S1aS8R6R5A2U0A3SaR7R6A2S0S1bS22G0G0A2A1M1S29S23R4A1A1S29S23R5A1M2A1A3S0G1S2bG2A1S2bS23R6A1M3A1A3S0SbS28G3A1S28S23R7A1M4A1A3S0SbS25G4A1S25S23R8A1M5A1A3S0G1S2aG5A1S27S2aS23R9A1A1S31RcA1M6S2dG6Z40000M7A2A3A3S0G1S26R9A1S27S26RaA1S31RdA1M8S2dG8G7A2A3A3S2eS33RaRcA2S2dS33RbRcA2G7A2A2SeVA;Vrb;Vtp0;Vmd0;S7RfU1ReA3RdRbA7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md md' HM Hg Ho EM ER EL ET EN ELz HP.
  unfold mlink in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  rewrite EM, ER, EL, ET, EN, ELz, M5, M6.
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  destruct p; cbn [ph_get pord pbase ph_set ph_u ph_f] in *.
  - rewrite Hg, Ho in *. unfold subU, subF, committed, revealedp, kUserMapSize in *. cbn [Nat.leb] in *.
    split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
  - rewrite Hg in *. unfold subF, committed, revealedp, kFreeArrayMapSize in *. cbn [Nat.leb] in *.
    split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
Qed.

Lemma mlink_reveal : ltac2:(tb__ "0|2|
S6ScS1bS32Q40A1M0A1M1S24G1SeVA;Vrb;Vtp0;Vmd0;R4R3R2A7S0S1aS8R6R5A2U1A3G0S34G0R1R4A3S1S2S34G0R2R7A3A1S19S31R9A1R2A2A2F_;Fq;S2eS30S21G0R4A2A1Z8A2S2eS33R6S1dG0R5R7A3A2S2dS33R6R7A2Z8000A2A2SeVA;Vrb;Vtp0;Vmd0;S7RaU2R9A3S1dG0R6R8A3R7A7F_;F_;F_;F_;F_;Ftpn;Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md tpn HM Hg Hq Hn HP.
  unfold mlink in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  destruct p; cbn [ph_get pbase ph_set ph_u ph_f] in *; rewrite Hg in *; unfold committed, revealedp in *; cbn [Nat.leb] in *.
  - split; [exact M5|]. split; [exact M6|]. exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
    split.
    { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | left; split; [reflexivity | exact S]].
      - destruct (M8 q Hin) as [N [[X _]|X]]; [discriminate X|]. split; [exact N | right; exact X]. }
    split; [rewrite length_app, Nat2Z.inj_add; lia|].
    lia.
  - split; [exact M5|]. split; [exact M6|]. exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
    split.
    { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | right; split; [reflexivity | exact S]].
      - destruct (M8 q Hin) as [N [X|[X _]]]; [|discriminate X]. split; [exact N | left; exact X]. }
    split; [rewrite length_app, Nat2Z.inj_add; lia|].
    lia.
Qed.

Lemma mlink_release : ltac2:(tb__ "0|0|
S6ScS1bS32Q40A1A1S24SeVA;Vrb;Vtp0;Vmd0;R3R2R1A7S0S1aS8R5R4A2U2A3SeVA;Vrb;Vtp0;Vmd0;S7R6U3R5A3R4R3A7F_;F_;Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md HM Hg. unfold mlink in HM |- *. cbn zeta in HM |- *.
  destruct p; cbn [ph_get ph_set ph_u ph_f] in *; rewrite Hg in HM; exact HM.
Qed.

Lemma zone_commit : ltac2:(tb__ "0|0|
S6ScSbS0S1aS8R3R2A2U0A3S3SdVA;Vrb;S7R4U1R3A3R2A4SdVA;Vrb;R3R2A4A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp; cbn [Nat.leb]; tauto.
Qed.
Lemma zone_reveal : ltac2:(tb__ "0|1|
S6ScSbS0S1aS8R3R2A2U1A3S3SdVA;Vrb;S7R4U2R3A3R2A4S4SdVA;Vrb;R3R2A4S1S2eS35S31R4A1A1M0R2A2S2fR2S2dG0Z8000A2A2A2A2A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get pbase ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp; cbn [Nat.leb]; split; intros H; repeat (destruct H as [H|H]); try (destruct H as [X H]; try discriminate X); tauto.
Qed.
Lemma zone_release : ltac2:(tb__ "0|1|
S6ScSbS0S1aS8R3R2A2U2A3S3SdVA;Vrb;S7R4U3R3A3R2A4S4SdVA;Vrb;R3R2A4S1S2eS31R4A1M0R2A2S2fR2S2dG0Z40000A2A2A2A2A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get pbase ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp, kUserMapSize, kFreeArrayMapSize; cbn [Nat.leb]; split; intros H; repeat (destruct H as [H|H]); try (destruct H as [X H]; try discriminate X); tauto.
Qed.

Lemma rlink_grow_quiet : ltac2:(tb__ "0|5|
ScScSbOF_;S2cS2cS2cS9R6A1M0G0SbS3SdVA;Vrb;R8R1A4S4SdVA;Vrb;R9R1A4R7R1A1A2A2Fz;SbS4R8R1A1M1S2G1A1A2Fz;SfVA;Vrb;RaR7R6A5SbS2RaR1A1A1S0S20S32Q8A1M2A1M3R8R2A1R9R2A1M4A3F_;Fz;SbRbR1A1S2S0G3G4S1cG2A1A3A1F_;Fz;SfVA;Vrb;RcRaR8A5F_;F_;F_;F_;F_;F_;F_;Fm';Fm;Fm0;FN;Fph';Fph;").
Proof.
  intros ph ph' N m0 m m' (Q1 & Q2 & Q3 & Q4) (Q1' & Q2' & Q3' & Q4') HZ ND (L1 & L2 & _) HO HI.
  unfold rlink. rewrite Q1', Q2', Q3', Q4'.
  split; [intros z Hz; rewrite HO by (intros X; apply Hz; apply HZ; right; exact X); apply L1; intros X; apply Hz; apply HZ; left; exact X|].
  split.
  { intros z Hz. apply HZ in Hz. destruct (ND z) as [Y|Y]; [exact (HI z Y)|]. rewrite (HO z Y). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
  split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
Qed.

Lemma rlink_quiet_intro : ltac2:(tb__ "0|3|
ScScS2cS2cS2cS9R4A1SbSdVA;Vrb;R7R1A4SdVA;Vrb;R7R2A4F_;Fz;SfVA;Vrb;R7R5R4A5SbS2SdVA;Vrb;R8R1A4A1S0S20S32Q8A1M0A1M1R6R2A1R7R2A1M2A3F_;Fz;SbSdVA;Vrb;R9R1A4S2S0G1G2S1cG0A1A3A1F_;Fz;SfVA;Vrb;R9R8R6A5F_;F_;F_;F_;F_;Fm';Fm;Fm0;Fph';Fph;").
Proof.
  intros ph ph' m0 m m' (Q1' & Q2' & Q3' & Q4') HZ (L1 & _) HO HI.
  unfold rlink. rewrite Q1', Q2', Q3', Q4'.
  split; [intros z Hz; rewrite (HO z Hz); apply L1; intros X; exact (Hz (HZ z X))|].
  split; [exact HI|].
  split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
Qed.
End JP.
End RefillJP.

(* [comment removed for export] *)
Module CallocPosts.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "sprop"; "SVar"; "valuation"; "sobj"; "eval"; "FcsrFrm0"; "SLit"; "mkSS"; "DZero"; "SAlu"; "SPUle"; "ss_next"; "swf"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "list"; "prod"; "app"; "bool"; "true"; "None"; "false"; "nat"; "Some"; "option"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "cut_regs"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "V_RES"; "mkA"; "A_globals"; "KcA"; "ae_ret_calloc"; "malloc_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "F_res_facts"; "JL_malloc_null"; "JL_malloc_ok"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "block_obj"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "PRODs"; "Lconv_S"; "s_fin"; "F_topr"; "Lc_null"; "Lc_ok"; "Lc_ok_S"; "NLC"; "Lconv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2"; "rho_c"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.POSTS"; "JLc_null"; "JLc_ok"; "PFc"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "mul"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation U := bv_unsigned.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition NLC : positive := 150%positive.
Definition PRODs : sv := SMd M_MUL (SVar 143) (SVar 144).
Definition s_fin : wsub := ltac2:(tb__ "0|1|
SfS13S46S0A2M0S10S46S0PcS3P8fA1A4SfG0S10S46S0PdS3P90A1A4S11G0A1A3A3").

Definition Lc_null (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S24S9S27S22A1S21S1fS1eA1SfS13S19S0A2M0S10S19S0UaS8Z0A1A4S11G0A1A3A2S20S7S17S0A1SfS5S2aS14S5S2cVW;A1S25A3A3S14S2S2bVW;Vst;A2S29S28A1A3S42S18A9S11S13S0S0A2A1A2").
Definition Lc_ok_S (W : list ulink) (st : ustop) (size : sv) (extra : list sprop) : sstate := ltac2:(tb__ "0|0|
S9S27S22A1S1fS1eA1S20S7S17S0A1SfS5S2aS14S5S2cVW;A1S14S5SfS5S33Vsize;SaA2S11S5A1A3S25A3A3A3S14S2Vextra;S14S2S2dS3PcA1A1S14S2S2bVW;Vst;A2S29S28A1A3A3A3S42S18A9").
Definition Lc_ok (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|2|
S24S41VW;Vst;S3PcA1M0S11S2A1A4SfS13S0S0A2M1S10S0S0S3S23A1G0A4S11G1A1A3A2").

Definition F_topr : sprop := ltac2:(tb__ "0|0|
ScSbS50S3S23A1S3bA3S8Z7fffff800000A1A2").
Definition Lconv_S (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|0|
S41VW;Vst;S3bSfS2S3eS11S2A1A3A4").
Definition Lconv (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S24S3cVW;Vst;A2SfS13S0S0A2M0S10S0S0S3S23A1S3bA4S11G0A1A3A2").

Section POSTS.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition JLc_null (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S4S12S34Q40A1M0A1M1S4G1S12S4aA1S49S1dS2eVAInv;VCST;VXGL;VA;VKc;R6R5R4R3R2R1AbS1dS1cG0S1R4P8fM2A2S1R6G2A2A3S1cG0S1R4P90M3A2S1R6G3A2A3A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition JLc_ok (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S4S12S34Q40A1M0A1M1S4G1S12S4aA1S49S1dS2fVAInv;VCST;VXGL;VA;VKc;R6R5R4R3R2R1AbS1dS1cG0S1R4P8fM2A2S1R6G2A2A3S1cG0S1R4P90M3A2S1R6G3A2A3A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition PFc (W : list ulink) (st : ustop) : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|1|
S4fS26SfS13S36S47A2M0S10S36S47S3fVW;Vst;A2S54R2R1A2A4SfG0S10S36S47S40VW;Vst;A2S55R2R1A2A4S11G0A1A3A3LKc;LA;").

Lemma SPA_x_restate1 : ltac2:(tb__ "0|3|
S4eS4S36S0S0S0S0S12S13S0S0A2M0A1M1S12S34Q40A1M2A1S4bS1cG1S39R8A1SfG0S10S0S0R7R6A4R3A3A3S1cG2S6RaR6A2S6RaR8A2A3S1cG2S6RbR6A2S6RbR8A2A3S1cS15S3aSdS37RbA1A1S10S0S0R8R7A4A2S16A3S4dS44ReRcRdR6R5A6S4dS44RfS53RdSfG0S10S0S0RaR9A4R8A3A2ReR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;FX;Fl';Fb';Fl;Fb;FA;Frho;FJ;").
Proof.
  intros J rho A b l b' l' X tp w EX Eb El HB [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [exact Hsm|]. split; [exact HMI|]. split.
  - unfold axwf in Hwf |- *. cbn. rewrite EX in Hwf. cbn [forallb] in Hwf. apply andb_prop in Hwf as [HX Hb]. apply andb_prop in HX as [_ HX].
    rewrite HB, HX, Hb. reflexivity.
  - split; [|exact Hhz]. unfold shadow_ok in Hsh |- *. cbn. rewrite EX in Hsh. constructor; [|exact (Forall_inv_tail Hsh)].
    pose proof (Forall_inv Hsh) as H1. unfold xr_ok in H1 |- *. cbn [fst snd] in H1 |- *. rewrite Eb, El. exact H1.
Qed.

Section CONV.
Variables (W : list ulink) (st : ustop).
Hypothesis Wcv : ltac2:(tb__ "0|0|
S1cS15SeS3cVW;Vst;A2A1S16A3").
Hypothesis Dcv : ltac2:(tb__ "0|4|
S1cS1bS13S12S13S0S0A2M0A1M1S12S2A1M2A2M3A1S51S37S40VW;Vst;A2A1S3cVW;Vst;A2A2S1aG3S10G1G2SfG0S10S0S0S3PcA1S3bA4S11G0A1A3SfS2S3eS11S2A1A3A4A2A3").
Hypothesis ENTcv : ltac2:(tb__ "0|0|
S1cS15S38S43VW;Vst;A2S31S22VW;Vst;A3S3dA3S16A3").
Hypothesis ENTnl : ltac2:(tb__ "0|0|
S1cS15S38S3fVW;Vst;A2S30S22VW;Vst;A3S3dA3S16A3").

Lemma fin_agree : ltac2:(tb__ "0|3|
S4S4S4cS1eS45R2A1R1A3S1cS34Q40A1M0S1R2P8fM1A2S1S45R3A1G1A2A3S1cG0S1R3P90M2A2S1S45R4A1G2A2A3S4cS1eR5S52R4S3dA2A3F_;F_;F_;Frho';Frho;").
Proof.
  intros rho rho' [Hw Hl] E143 E144. split.
  - intros i Hi. cbn [rho_sub rw]. unfold s_fin. cbn [wsub_get].
    destruct (Pos.eqb_spec i 12) as [->|N12]; [cbn [eval]; rewrite E143; unfold rho_c; rewrite !rw_set; reflexivity|].
    destruct (Pos.eqb_spec i 13) as [->|N13]; [cbn [eval]; rewrite E144; unfold rho_c; rewrite !rw_set; reflexivity|].
    cbn [eval]. rewrite <- (Hw i Hi). unfold rho_c. rewrite !rw_set. rewrite (proj2 (Pos.eqb_neq _ _) N12).
    replace (Pos.eqb i 143) with false by (symmetry; apply Pos.eqb_neq; unfold NF in Hi; lia).
    replace (Pos.eqb i 144) with false by (symmetry; apply Pos.eqb_neq; unfold NF in Hi; lia). reflexivity.
  - intros l. cbn [rho_sub rl]. rewrite <- (Hl l). reflexivity.
Qed.

Theorem calloc_conv : ltac2:(tb__ "0|1|
S4fS26S4S12S34Q40M0A1A1S4bS57S58S35G0S1R3PcA2A2S35G0S1R3PdA2A2A2S59Z2Z40A2A2S48S44S1eS45R4A1R3S56VW;Vst;R6R5A4R2A6S48S44S1eR5R4S32S22VAInv;VCST;VXGL;VW;Vst;R7R6A8R3A6F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w Hmul (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  assert (E12c : rw (rho_c rho) 12%positive = nwc rho) by (unfold rho_c; rewrite !rw_set; reflexivity).
  assert (ENV : U (rw (rho_c rho) 12%positive) = U (rw rho 12%positive) * U (rw rho 13%positive)).
  { rewrite E12c. unfold nwc. rewrite calloc_size_val. exact (mul_exact _ _ Hmul). }
  assert (Erm : rm (rho_c rho) = rm rho) by reflexivity.
  unfold PFc in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  -
    destruct HJL as (HJ & E143 & E144).
    exists (L_calloc_null AE_A W st), (JL_calloc_null AInv CST XGL A Kc), (rho_sub rho' s_fin), tp'.
    split; [left; reflexivity|]. split; [exact (fin_agree rho rho' Hag E143 E144)|].
    split; [exact (smatchA_entails segs _ _ s_fin rho' tp' w ENTnl Hsm)|].
    unfold JL_calloc_null. unfold JL_malloc_null in HJ. destruct HJ as (A' & HA' & H1 & H2 & HV & H4 & H5 & H6 & HM & HK & HC).
    exists A'. rewrite ENV in HV, HC. rewrite Erm in HM.
    split; [unfold AInv, AInvA in *; rewrite (rm_rho_sub' rho' s_fin); exact HA'|].
    rewrite (rm_rho_sub' rho' s_fin). repeat (split; [assumption|]). exact HC.
  -
    destruct HJL as (HJ & E143 & E144).
    assert (EP : eval rho' PRODs = eval rho' (SVar 12)).
    { unfold PRODs. cbn [eval]. rewrite E143, E144. rewrite <- (proj1 Hag 12%positive) by (unfold NF; lia). rewrite E12c.
      unfold rho_c. rewrite !rw_set. unfold nwc. rewrite calloc_size_val. reflexivity. }
    set (KJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
    assert (H0 : SPA segs KJ (Lc_ok W st) rho' tp' w) by (split; [exact Hsm | exact I]).
    pose proof (proj1 Hsm) as Hs0. unfold virt in Hs0.
    pose proof (smatch_facts_hold _ _ _ _ Hs0) as HFa.
    assert (H1 : SPA segs KJ (ax_setS (Lc_ok W st) (Lconv_S W st)) rho' tp' w).
    { eapply SPA_restate; [exact Wcv | exact Dcv | reflexivity | | | exact H0].
      - constructor; [|constructor]. cbn [fst snd]. symmetry. exact EP.
      - constructor; [|constructor]. unfold F_topr. cbn [holds].
        assert (HT : holds rho' (SPUle (SAlu ALU_ADD (SVar V_RES) (SVar 12)) (SLit atop_hi))).
        { apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts ax_S Lc_ok Lc_ok_S mkA]. cbn [app]. unfold F_res_facts. cbn. tauto. }
        cbn [holds] in HT. cbn [eval] in HT |- *. cbn [eval] in EP. rewrite EP. exact HT. }
    assert (H2 : SPA segs KJ (ax_setX (ax_setS (Lc_ok W st) (Lconv_S W st)) [(SVar V_RES, PRODs)]) rho' tp' w).
    { apply (SPA_x_restate1 KJ rho' _ (SVar V_RES) (SVar 12) (SVar V_RES) PRODs [] tp' w); [reflexivity | reflexivity | exact EP | reflexivity | exact H1]. }
    change (ax_setX (ax_setS (Lc_ok W st) (Lconv_S W st)) [(SVar V_RES, PRODs)]) with (Lconv W st) in H2.
    exists (L_calloc_ok AE_A W st), (JL_calloc_ok AInv CST XGL A Kc), (rho_sub rho' s_fin), tp'.
    split; [right; left; reflexivity|]. split; [exact (fin_agree rho rho' Hag E143 E144)|].
    split; [exact (smatchA_entails segs _ _ s_fin rho' tp' w ENTcv (proj1 H2))|].
    unfold JL_calloc_ok. unfold JL_malloc_ok in HJ. destruct HJ as (A' & l1 & l2 & HA' & HL1 & HL2 & HF & HV & H4 & H5 & H6 & HM & HK & HC).
    exists A', l1, l2. rewrite ENV in HL1, HV, HC. rewrite Erm in HM.
    assert (ER : rw (rho_sub rho' s_fin) V_RES = rw rho' V_RES) by reflexivity.
    split; [unfold AInv, AInvA in *; rewrite (rm_rho_sub' rho' s_fin); exact HA'|].
    rewrite (rm_rho_sub' rho' s_fin), ER. repeat (split; [assumption|]). exact HC.
Qed.
End CONV.
End POSTS.
End CallocPosts.

(* [comment removed for export] *)
Module CertMallocSV.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "SVar"; "sobj"; "sprop"; "mkObj"; "mkCell"; "cell"; "DUnknown"; "sv"; "SPBranch"; "SPNot"; "DZero"; "SPUle"; "sstate"; "ss_objs"; "mkSS"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "prod"; "app"; "pair"; "true"; "bool"; "list"; "option"; "length"; "negb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SUB"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "kAllocBegMagic"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV.NX2"; "RUE"; "L3b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "M48"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "rstS"; "BR"; "Bw"; "O_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV.NX3"; "a2e8"; "END8"; "B4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_MS"; "V_NCH"; "V_PAB"; "O_errno"; "O_oom"; "O_san"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV.NX"; "L3"; "B3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV.NX4"; "UE9"; "BP9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV.NX5"; "UBs"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_3"; "O_3b"; "O_4z"; "O_Mhi"; "O_Mlo"; "O_Pf9"; "O_fill"; "O_pxF"; "O_secgF"; "O_seciF"; "O_secmF"; "O_secsF"; "O_stF"; "PGST"; "a2e8"; "fx8"; "perm7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "kPtrArrayReserve"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "existsb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_A : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS1S26S2Vnx;A1S2S42A1A3S2P9bA1A2S1bS4A1A3").
Definition F_B : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS1S26S2P9bA1S0S2eS2fZ2Z25A2Z1000A2A1A3S2Vnx;A1A2S1bS4A1A3").

Definition B3 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S1S26S2Vnx;A1S0Z1000A1A3S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e6 : sv := ltac2:(tb__ "0|2|
S1S29S1S26S1S27S1S26S2Vnx;A1M0S0Z17f8A1A3S0Z3A1M1A3S0Z1A1A3S1S27S1S26G0S0Z1000A1A3G1A3A3").
Definition L3 : sv := SLit 256.
Definition O_3 : sobj := ltac2:(tb__ "0|0|
S5S4aS0Z0A1S49S1bS7A1S8A5").
Definition ru6 : list (nat * sv) := ltac2:(tb__ "0|1|
S1aS1dS1cS9A2M0S1fS1cS9UcS49A4S1bG0A1A3").
End NX.

Definition rmF (f : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S39VE;A1SeS3aVE;S10S17R1A1S18R1A1S14R1A1S13R1A1S19R1A1SfR1A1S6eS4S22S4A1S70S4A1S4S6cS25S6dS4S11R1A1Vf;A3A1M0A1Lp;S4S6fG0A1Lx;S12R1A1A6S16R1A1S15R1A1A9A2TS;").
Definition runT6 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S3bS40Ufa0S1aS30S34S1bS30A1A3VT;S20A5").

Section NX2.
Variable nx : positive.
Definition RUE : sv := ltac2:(tb__ "0|0|
S1S28S1S26S1S26S1S26S2Vnx;A1S0Z1800A1A3S2PcA1A3S0Z7A1A3S0Zfffffffffffffff8A1A3").
Definition F_g7 : list sprop := ltac2:(tb__ "0|0|
S1aS4SbSaS2aS0Z7fffffffffffA1S31A3A1S1bS4A1A3").
Definition a0e7 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S31S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e7 : sv := ltac2:(tb__ "0|1|
S1S29S1S26S1S27S1S26S1S26S31S1S26S1S29S1S26S2Vnx;A1S0Z1000A1A3S31A3S1S28S1S26S2S48A1S0ZfffA1A3S0Zfffffffffffff000A1A3A3A3S0N8A1A3S0Z3A1M0A3S0Z1A1A3S1S27S31G0A3A3").
Definition L3b : sv := SAlu ALU_ADD L2 (SLit 256).
Definition O_3n : sobj := ltac2:(tb__ "0|0|
S5S36Vnx;A1S0Z0A1S0Z100A1S1bS7A1S8A5").
Definition ru7 : list (nat * sv) := ltac2:(tb__ "0|1|
S1aS1dS1cS9A2M0S1fS1cS9UaS36Vnx;A1A4S1aG0S1fS1cS9UcS32A4S1bG0A1A3A3").
End NX2.
Definition U7p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S54Vnx;A1A3").

Definition perm7 (n : nat) : list nat := ltac2:(tb__ "0|1|
S1eS1cS1aS1cU0S1aS1cS41Vn;U1M0A2S1aS1cG0S1bS1cA1A3A3A3S4eU2S41Vn;U3A2A2A3").
Definition sel7 (E : axst) : axst := ltac2:(tb__ "0|2|
S3aVE;S51S39VE;A1M0S4fSfG0A1M1S68S24S3G1A2A1A2A2A2").

Section NX3.
Variable nx : positive.
Definition END8 : sv := ltac2:(tb__ "0|0|
S1S26S1S26S1S26S2Vnx;A1S0Z1800A1A3S1S28S2PcA1S0S33A1A3A3S0N8A1A3").
Definition a2e8 : sv := ltac2:(tb__ "0|1|
S1S29S1S26S1S27S3eS0Z3A1M0A3S0Z1A1A3S1S27S1S26S2Vnx;A1S0Z1800A1A3G0A3A3").
Definition B4 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S1S26S2Vnx;A1S0Z1800A1A3S0Z3A1A3S0Z7fff8000A1A3").

Definition F_g8 : list sprop := ltac2:(tb__ "0|0|
S1aS4SaS2aS3dS0ZffffffffffffffffA1A3S1aS4SbSaS2aS0Z7fffffffffffA1S3eA3A1S1aS4SbSaS2bS1S28S2PcA1S0S33A1A3S0Z0A1A3A1S1bS4A1A3A3A3").

Definition fx8 : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS3dS0Z4000000000000000A1A2S1bS4A1A3").
Definition O_3b : sobj := ltac2:(tb__ "0|0|
S5S36Vnx;A1S0Z0A1S57S1bS7A1S8A5").
Definition O_4 : sobj := ltac2:(tb__ "0|0|
S5S3fS0Z0A1S3dS1bS7A1S8A5").
End NX3.
Definition U8p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S55Vnx;A1A3").
Definition CT8p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S67Vnx;A1A3").

Section NX4.
Variable nx : positive.
Definition UE9 : sv := ltac2:(tb__ "0|0|
S1S26S1S26S2Vnx;A1S0Z1800A1A3S1S28S2PcA1S0S33A1A3A3").
Definition F_g9 : list sprop := ltac2:(tb__ "0|0|
S1aS4SbSaS2aS0Z7fffffffffffA1S4bA3A1S1bS4A1A3").
Definition BP9 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S4bS0Z3A1A3S0Z7fff8000A1A3").
Definition O_4z : sobj := ltac2:(tb__ "0|0|
S5S52Vnx;A1S0Z0A1S66Vnx;A1S1bS7A1ScA5").
Definition O_P9 : sobj := ltac2:(tb__ "0|0|
S5S4cS0Z0A1S0Z1A1S1bS7A1S8A5").
Definition F_par : sprop := ltac2:(tb__ "0|1|
SaS2bS2PcA1M0S1S28G0S0S33A1A3A3").
End NX4.
Definition U9p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S35VE;S1bS1dS1cS9A2A1S56Vnx;A1A3").
Definition PGST : Z := 0x3c8bc.
Definition runT9 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S3bS40Ufa0S1aS30S34S1aS30S65S1bS30A1A3A3VT;S20A5").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S23SeA1S3cLx;S50S39VA;A1Vi;Vmid;A3SeS3aVA;R1A2LS';VA;X23x2").
Fixpoint find_map (nx : positive) (l : list sobj) (i : nat) : nat :=
  match l with [] => i | o :: t => if sv_eqb (ob_base o) (SVar nx) then i else find_map nx t (S i) end.
Definition runTF (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S3bS40Ufa0S1bS30A1VT;S20A5").

Section NX5.
Variable nx : positive.
Definition UBs : sv := ltac2:(tb__ "0|0|
S1S26S2Vnx;A1S0Z1800A1A3").
Definition O_fill : sobj := ltac2:(tb__ "0|0|
S5S4dS0Z0A1S0Z1000A1S1bS7A1S8A5").
Definition O_Mlo (mc : list cell) : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z0A1S0Z1800A1Vmc;ScA5").
Definition O_Mhi : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z2800A1S2S42A1S1bS7A1ScA5").
Definition O_UBs : sobj := ltac2:(tb__ "0|0|
S5S4dS0Z0A1S2PcA1S1bS7A1S8A5").
Definition mc_map : cell := ltac2:(tb__ "0|0|
S6S0Z0A1Z8S2Vnx;A1A3").
Definition mc_ms : cell := mkCell (SLit 8) 8 msx.
Definition mc_ns : cell := mkCell (SLit 16) 8 (SVar V_NS).
Definition mc_idx : cell := ltac2:(tb__ "0|0|
S6S0Z18A1Z8S2S43A1A3").
Definition mc_magic : cell := ltac2:(tb__ "0|0|
S6S0Z1000A1Z8S0S2dA1A3").
Definition mc_cptr : cell := ltac2:(tb__ "0|0|
S6S0Z1008A1Z8S1S26S2Vnx;A1S0Z17f0A1A3A3").
Definition mc_state : cell := mkCell (SLit 6128) 1 (SLit 2).
Definition mc_type (t : Z) : cell := mkCell (SLit 6129) 1 (SLit t).
Definition mc_sizehi : cell := ltac2:(tb__ "0|0|
S6S0Z17f2A1Z2S1S27S2PcA1S0Z20A1A3A3").
Definition mc_size : cell := mkCell (SLit 6132) 4 (SVar 12).
Definition O_Pf9 : sobj := ltac2:(tb__ "0|2|
S5S53Vnx;A1S0Z0A1M0S0Z1M1A1S1aS7S6G0G1S1S28S2PcA1S0Z7A1A3A3S1bS7A1A3S8A5").
Definition xc_map : cell := ltac2:(tb__ "0|0|
S6S0Z0A1Z8S2Vnx;A1A3").
End NX5.
Definition O_seciF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0S2cA1S0S2eS2cZ40A2A1Vc;S8A5").
Definition O_secsF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0S2eS2cZ40A2A1S0Zead00A1Vc;S8A5").
Definition O_secmF : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1M0S0Zead00A1M1S0Zead04A1S1aS7S6G1Z1G0A3S1aS7S6S0Zead01A1Z3G0A3S1bS7A1A3A3S8A5").
Definition O_secgF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0Zead08A1S0Zead30A1Vc;S8A5").
Definition O_stF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S69S0Zad0A1S0Zc60A1Vc;S8A5").
Definition O_pxF (blk : Z) (d : odefault) (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S37S0Z0A1S0Vblk;A1Vc;Vd;A5").
Definition ic_pg : cell := ltac2:(tb__ "0|0|
S6S0S2cA1Z8S0S6aA1A3").
Definition ic_c1 : cell := ltac2:(tb__ "0|1|
S6S0S2eS2cZ8M0A2A1G0S2S44A1A3").
Definition ic_c2 : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ10A2A1Z8S2S44A1A3").
Definition ic_rs : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ18A2A1Z8S0S6bA1A3").
Definition ic_nres (e : sv) : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ30A2A1Z8Ve;A3").
Definition ic_nch : cell := ltac2:(tb__ "0|0|
S6S0S2eS2cZ38A2A1Z8S1S26S2S43A1S0Z1A1A3A3").
Definition RSF (nx : positive) (c1 c2 c4 c5 mc xc : list cell) (blk : Z) (dpx : odefault) (partial : bool) : list sobj := ltac2:(tb__ "0|1|
S1eS3S1aS3S5eVnx;A1S1aS3S5aVnx;A1S1aS3S59Vnx;A1S1aS3S58Vnx;A1S1aS3S38Vnx;A1S1bS3A1M0A3A3A3A3A3S1eS3S1aS3S61Vc1;A1S1aS3S63Vc2;A1S1aS3S62S1aS3S60Vc4;A1S1aS3S47S1aS3S46S1aS3S45S1aS3S64Vc5;A1G0A3A3A3A3A3A3A3A3S1eS3S1aS3S5cVnx;Vmc;A2S1aS3S5bVnx;A1S1aS3S5fVblk;Vdpx;Vxc;A3G0A3A3A3S21S22S3A1Lpartial;Vpartial;S1aS3S5dVnx;A1G0A3G0X21x2A3A3A3").
End CertMallocSV.

(* [comment removed for export] *)
Module SpineMallocS12iW2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "pair"; "Some"; "nil"; "option"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_next"; "swf"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "creg_a"; "C1g"; "E2a"; "creg_b"; "F_gen"; "V_CLS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "E2a'"; "only_var"; "tab_ok"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "d_k"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma WC1_2 : ltac2:(tb__ "0|0|
S2S5S11S4S14S1U2A1S0Z4A3A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_2 : ltac2:(tb__ "0|5|
S25S3S22Z0R1A2S22R1Z7A2A2S2ScS8S7S8SeSeA2A1M0S7SfA1M1A2M2A1S20S4S27S1U2A1M3S0Z4M4R2A4A1S4S14G3S0G4A3A1A2SaG2S9G0G1S28R2A1S17A4A2A3F_;Fk;").
Proof.
  intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma OVa_2 : ltac2:(tb__ "0|0|
S2S5S1aP9dS13S1U2A1S0Z4A3A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OVb_2 : ltac2:(tb__ "0|0|
S2S5S1aP9dS16S1U2A1S0Z4A3A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TABa_2 : ltac2:(tb__ "0|0|
S2S5S1bP9dS13S1U2A1S0Z4A3S21Z208S23S24S1cS1dS1eS1cS1fA1A1A1A1A1A1A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TABb_2 : ltac2:(tb__ "0|0|
S2S5S1bP9dS16S1U2A1S0Z4A3S21Z18U3eA5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXa_2 : ltac2:(tb__ "0|2|
S2S26S10S4S19U2M0S0Z4M1A3A1A1S10S4S15S1G0A1S0G1A3A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Da'_2 : ltac2:(tb__ "0|7|
S2ScS8S7S8SeSeA2M0A1M1S7SfA1M2A2M3A1S20S4S15S1U2M4A1M5S0Z4M6A3A1S4S19G4S0G6A3A1A2SaG3S9G1G2SdG0S9SeSeS13G5S0G6A3S12S18A1A4SbG0A1A3SbSfA1A4A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Wa'_2 : ltac2:(tb__ "0|0|
S2S5S11S4S19U2S0Z4A3A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End SpineMallocS12iW2.

