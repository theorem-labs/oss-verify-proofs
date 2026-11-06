(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAF.
From Stdlib Require Zwf Wellfounded FunctionalExtensionality.

(* [comment removed for export] *)
Module TobjJAG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sv_eqb"; "sprop"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "Some"; "cons"; "fst"; "option"; "snd"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BUD"; "bsumK"; "bsumV"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "amode"; "ndesc"; "JA"; "JAi"; "@Corelib.Init.Logic"; "eq"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "JAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "remove_firstB"; "remove_firstP"; "svp_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma tvd_perm : ltac2:(tb__ "0|2|
S1S4S5S0S0A2M0A1M1G1S19G0R2R1A3S29R4R3A2S29R5R3A2F_;F_;Ftv';Ftv;Frho;").
Proof.
  intros rho tv tv' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros HD.
  - exact HD.
  - destruct HD as [Hx Hl]. split; [|exact (IH Hl)]. intros t' Ht'. apply Hx. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht'].
  - destruct HD as (Hy & Hx & Hl). cbn. split; [|split; [|exact Hl]].
    + intros t' [<-|Ht'] Nx Nt E0; [exact (Hy x (or_introl eq_refl) Nt Nx (eq_sym E0)) | exact (Hx t' Ht' Nx Nt E0)].
    + intros t' Ht'. apply Hy. right. exact Ht'.
  - exact (IH2 (IH1 HD)).
Qed.

Definition svp_eqb (a b : sv * sv) : bool := ltac2:(tb__ "0|0|
SdS2SaS0S0Va;A3SaS0S0Vb;A3A2S2ScS0S0Va;A3ScS0S0Vb;A3A2A2").
Lemma svp_eqb_sound : ltac2:(tb__ "0|1|
S5S0S0A2M0G0S18S6S27R2R1A2S7A3S18G0R3R2A3F_;Fb;Fa;").
Proof.
  intros [a1 a2] [b1 b2] H. unfold svp_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. congruence.
Qed.
Fixpoint remove_firstP (x : sv * sv) (l : list (sv * sv)) : option (list (sv * sv)) :=
  match l with
  | [] => None
  | y :: r => if svp_eqb x y then Some r else option_map (cons y) (remove_firstP x r)
  end.
Lemma remove_firstP_perm : ltac2:(tb__ "0|2|
S5S0S0A2M0S4G0A1M1G1S18SbG1A1S26R3R2A2S8G1R1A2A3S19G0R3S9G0R4R2A3A3F_;Fr;Fl;Fx;").
Proof.
  intros x l. induction l as [|y t IH]; intros r H; cbn in H; [discriminate|].
  destruct (svp_eqb x y) eqn:E.
  - injection H as <-. apply svp_eqb_sound in E. subst y. apply Permutation_refl.
  - destruct (remove_firstP x t) as [r'|] eqn:E2; cbn in H; [|discriminate]. injection H as <-.
    apply (Permutation_trans (perm_skip y (IH r' eq_refl))). apply perm_swap.
Qed.
Fixpoint tv_permb (l1 l2 : list (sv * sv)) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | x :: r => match remove_firstP x l2 with Some r2 => tv_permb r r2 | None => false end
  end.
Lemma tv_permb_sound : ltac2:(tb__ "0|2|
S4S5S0S0A2M0A1M1G1S18S6S24R2R1A2S7A3S19G0R3R2A3F_;Fl2;Fl1;").
Proof.
  induction l1 as [|x r IH]; intros l2 H; cbn in H.
  - destruct l2; [apply Permutation_refl | discriminate].
  - destruct (remove_firstP x l2) as [r2|] eqn:E; [|discriminate].
    apply (Permutation_trans (perm_skip x (IH r2 H))). apply Permutation_sym. apply remove_firstP_perm. exact E.
Qed.

Fixpoint remove_firstB (x : bitem) (l : list bitem) : option (list bitem) :=
  match l with
  | [] => None
  | y :: r => if bitem_eqb x y then Some r else option_map (cons y) (remove_firstB x r)
  end.
Lemma remove_firstB_perm : ltac2:(tb__ "0|1|
SeS4SeA1M0G0S18SbG0A1S25R3R2A2S8G0R1A2A3S19SeR3S9SeR4R2A3A3F_;Fr;Fl;Fx;").
Proof.
  intros x l. induction l as [|y t IH]; intros r H; cbn in H; [discriminate|].
  destruct (bitem_eqb x y) eqn:E.
  - injection H as <-. apply bitem_eqb_sound in E. subst y. apply Permutation_refl.
  - destruct (remove_firstB x t) as [r'|] eqn:E2; cbn in H; [|discriminate]. injection H as <-.
    apply (Permutation_trans (perm_skip y (IH r' eq_refl))). apply perm_swap.
Qed.
Fixpoint bd_permb (l1 l2 : list bitem) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ => false end
  | x :: r => match remove_firstB x l2 with Some r2 => bd_permb r r2 | None => false end
  end.
Lemma bd_permb_sound : ltac2:(tb__ "0|1|
S4SeA1M0G0S18S6S23R2R1A2S7A3S19SeR3R2A3F_;Fl2;Fl1;").
Proof.
  induction l1 as [|x r IH]; intros l2 H; cbn in H.
  - destruct l2; [apply Permutation_refl | discriminate].
  - destruct (remove_firstB x l2) as [r2|] eqn:E; [|discriminate].
    apply (Permutation_trans (perm_skip x (IH r2 H))). apply Permutation_sym. apply remove_firstB_perm. exact E.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S28S1S4S1cQ40A1A1S1fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S5S5S12S12A2S12A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.

Let JAi : ltac2:(tb__ "0|0|
S15S28S12S1bFkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S17VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S15S1bFnd;") := ltac2:(tb__ "0|0|
S16VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma JAi_tv_perm : ltac2:(tb__ "0|2|
S4S5S0S0A2M0A1M1G1S4S5S5S0S12A2S0A2A1S4SeA1S14S28S12S1S4S1cQ40A1A1S4S20A1S1fS19G0RbRaA3VJAi;S13RcRaR9R8A4R7R6R5R4R3R2A7VJAi;S13RcRbRaR9A4R8R7R6R5R4R3A7F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fam;Fbd;Ffr;Ftv';Ftv;").
Proof using .
  intros tv tv' fr bd am Ai kc rho tp tr md HP HJ.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU |- *.
  assert (PERM : forall t, In t tv' <-> In t tv).
  { intros t. split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact HP | exact H] | eapply Permutation_in; [exact HP | exact H]]. }
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|exact (conj HPA (conj HCKi (eq_ind (cntS rho tv) (fun c => small_live Ai <= bxN BX + c) HCNi (cntS rho tv') (cntS_perm rho tv tv' HP))))]]]]]].
  - split; [|split].
    + unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). apply PERM. exact Ht.
    + cbn [nd_tv]. exact (tvd_perm rho tv tv' HP HD).
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply PERM. exact Ht.
  - unfold XA in *. eapply (proj1 (XAz_transport FB FB _ Ai Ai (rm rho) (rm rho) (tvals rho tv) (tvals rho tv') kc HXA _ _ _ _)).
    Unshelve.
    + intros b n Hin Hnf Hut. split; [exact Hin|]. split; [exact Hnf|]. intros v Hv. apply Hut. unfold tvals in *.
      apply in_map_iff in Hv as (t & <- & Ht). apply in_map. apply PERM. exact Ht.
    + intros; reflexivity.
    + intros; split; [reflexivity | auto].
    + intros bn H1 _ H3 H4. split; [exact H1|]. split; [exact H3|]. intros v Hv. apply H4. unfold tvals in *.
      apply in_map_iff in Hv as (t & <- & Ht). apply in_map. apply PERM. exact Ht.
Qed.
Lemma JA_tv_perm : ltac2:(tb__ "0|2|
S4S5S0S0A2M0A1M1G1S4S5S5S0S12A2S0A2A1S4SeA1S14S1S4S1cQ40A1A1S4S20A1S1fS19G0R9R8A3VJA;S13RaR8R7R6A4R5R4R3R2A5VJA;S13RaR9R8R7A4R6R5R4R3A5F_;F_;Fmd;Ftr;Ftp;Frho;Fam;Fbd;Ffr;Ftv';Ftv;").
Proof using . intros tv tv' fr bd am rho tp tr md HP (Ai & kc & HJ). exists Ai, kc. exact (JAi_tv_perm tv tv' fr bd am Ai kc rho tp tr md HP HJ). Qed.
Lemma SPA_tv_perm : ltac2:(tb__ "0|2|
S4S5S0S0A2M0A1M1G1S4S5S5S0S12A2S0A2A1S4SeA1S14S1eS1S4S1cQ40A1A1S1dS19G0R9R8A3S1aVsegs;VJA;S13RaR8R7R6A4A1R5R4R3R2A6S1aVsegs;VJA;S13RaR9R8R7A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ffr;Ftv';Ftv;").
Proof using . intros tv tv' fr bd am A rho tp [tr [ms md]] HP [Hsm HJ]. split; [exact Hsm|]. exact (JA_tv_perm tv tv' fr bd am rho tp tr md HP HJ). Qed.
Lemma SPA_tv_permb : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S4S5S5S0S12A2S0A2A1S4SeA1S14S1eS1S4S1cQ40A1A1S1dS18S6S24R9R8A2S7A3S1aVsegs;VJA;S13RaR8R7R6A4A1R5R4R3R2A6S1aVsegs;VJA;S13RaR9R8R7A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ffr;Ftv';Ftv;").
Proof using . intros tv tv' fr bd am A rho tp w H. apply SPA_tv_perm. apply tv_permb_sound. exact H. Qed.

Lemma SPA_tv_permb_F : ltac2:(tb__ "0|1|
S1OF_;S4S5S0S0A2A1M0G0S4S5S5S0S12A2S0A2A1S4SeA1S14S1eS1S4S1cQ40A1A1S1dS18S6S24R9R8A2S7A3S1aVsegs;S21VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;RbS13RaR8R7R6A4AdR5R4R3R2A6S1aVsegs;S21VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;RcS13RaR9R8R7A4AdR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ffr;Ftv';Ftv;FPhi;").
Proof using .
  intros Phi tv tv' fr bd am A rho tp [tr [ms md]] H [Hsm [HJ HP]]. split; [exact Hsm|]. split; [|exact HP].
  exact (JA_tv_perm tv tv' fr bd am rho tp tr md (tv_permb_sound _ _ H) HJ).
Qed.

Lemma payA_of_bud_pay2 : ltac2:(tb__ "0|1|
S4S3A1S0S12S4SeA1M0G0S18S6S22R5R4R3R2R1A5S7A3S2aVNP;Vrho0;VP0f;R6R5R4R3R2A8F_;Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof using .
  intros facts costV costK bfrom bto H. unfold payA, pay_okF.
  pose proof H as H0. rewrite bud_pay2_ref_eq in H; unfold bud_pay2_ref in H.
  apply lazy_andb_prop in H as [Hw H]. apply lazy_andb_prop in H as [Hwt H]. apply lazy_andb_prop in H as [Hnn H]. apply lazy_andb_prop in H as [HK H].
  apply Z.leb_le in HK.
  split; [exact Hwt|]. split; [exact HK|].
  intros rho HF _ Hwf Hnf.
  destruct (bud_pay2_sound facts costV costK bfrom bto rho HF Hnf H0) as (P1 & P2 & _ & _ & _ & P6 & _). split; [exact P1|]. split; [exact P2 | exact P6].
Qed.

Lemma bsumV_perm : ltac2:(tb__ "0|1|
S4SeA1M0G0S1S19SeR3R2A3S18S12S11R4R2A2S11R3R2A2A3F_;Frho;Fb';Fb;").
Proof using . intros b b' rho HP. induction HP; cbn; lia. Qed.
Lemma bsumK_perm : ltac2:(tb__ "0|1|
S4SeA1M0G0S1S19SeR3R2A3S18S12S10R4R2A2S10R3R2A2A3F_;Frho;Fb';Fb;").
Proof using . intros b b' rho HP. induction HP; cbn; lia. Qed.
Lemma BUD_perm : ltac2:(tb__ "0|1|
S4SeA1M0G0S5S12S12A2S12S12S12S1S19SeR7R6A3SfR8R6R5R4R3R2A6SfR8R7R6R5R4R3A6F_;F_;Frho;FKf;FKm;FV;FBXv;Fb';Fb;").
Proof using .
  intros b b' BXv V Km Kf rho HP H. unfold BUD in *.
  rewrite <- (bsumV_perm b b' rho HP), <- (bsumK_perm b b' rho HP).
  destruct H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  repeat (split; [assumption|]). split.
  - unfold bd_wpos in *. apply forallb_forall. intros it Hit. apply (proj1 (forallb_forall _ _) Hw). eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hit].
  - split; [|split; assumption]. unfold bd_nn in *. apply Forall_forall. intros it Hit. apply (proj1 (Forall_forall _ _) Hn).
    eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hit].
Qed.
Lemma JA_bd_perm : ltac2:(tb__ "0|1|
S4S5S0S0A2A1S4S5S5S0S12A2S0A2A1S4SeA1M0G0S14S1S4S1cQ40A1A1S4S20A1S1fS19SeR7R6A3VJA;S13RaR9R8R6A4R5R4R3R2A5VJA;S13RbRaR8R7A4R6R5R4R3A5F_;F_;Fmd;Ftr;Ftp;Frho;Fam;Fbd';Fbd;Ffr;Ftv;").
Proof using .
  intros tv fr bd bd' am rho tp tr md HP (Ai & kc & HJ). exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN3, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|]. split; [|exact (conj HPA (conj HCKi HCNi))].
  exact (BUD_perm bd bd' _ _ _ _ rho HP HBU).
Qed.
Lemma SPA_bd_permb : ltac2:(tb__ "0|1|
S4S5S0S0A2A1S4S5S5S0S12A2S0A2A1S4SeA1M0G0S14S1eS1S4S1cQ40A1A1S1dS18S6S23R7R6A2S7A3S1aVsegs;VJA;S13RaR9R8R6A4A1R5R4R3R2A6S1aVsegs;VJA;S13RbRaR8R7A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd';Fbd;Ffr;Ftv;").
Proof using . intros tv fr bd bd' am A rho tp [tr [ms md]] H [Hsm HJ]. split; [exact Hsm|]. apply (JA_bd_perm tv fr bd bd'); [apply bd_permb_sound; exact H | exact HJ]. Qed.
Lemma SPA_bd_permb_F : ltac2:(tb__ "0|1|
S1OF_;S4S5S0S0A2A1S4S5S5S0S12A2S0A2A1S4SeA1M0G0S14S1eS1S4S1cQ40A1A1S1dS18S6S23R7R6A2S7A3S1aVsegs;S21VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;RbS13RaR9R8R6A4AdR5R4R3R2A6S1aVsegs;S21VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;RcS13RbRaR8R7A4AdR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd';Fbd;Ffr;Ftv;FPhi;").
Proof using .
  intros Phi tv fr bd bd' am A rho tp [tr [ms md]] H [Hsm [HJ HP]]. split; [exact Hsm|]. split; [|exact HP].
  apply (JA_bd_perm tv fr bd bd'); [apply bd_permb_sound; exact H | exact HJ].
Qed.
End Sum.
End WithSegs.
End TobjJAG.

(* [comment removed for export] *)
Module TobjJAFb.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "list"; "nat"; "prod"; "Some"; "app"; "bool"; "fst"; "option"; "snd"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "ena_state"; "ena_meas"; "edgeA"; "ena_pred"; "cfg_edgesA"; "eedge_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sv"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@Stdlib.Lists.List"; "In"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "efmeasA"; "enodeIAF"; "phiK"; "JAF"; "ejcertAF"; "phi_reads"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith Zwf Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section G.
Variable segs : list Segment.

Theorem cfg_complete_genTA_b : ltac2:(tb__ "0|6|
S2S1SbA1ScS1SdA1M0G0S1S10A1M1SbS1cOF_;F_;SbSbS1cS2fR3R2A2R5R4R2A2R6R4R3A2F_;F_;Fw;Fb';Fb;SdS1eSdR1R6A3S2dVsegs;S17S15SeR2A1A1A1S11R2A1A3F_;Fn;SdS16S16S1eSdR3R9A3S19S17S15SeR4A1M2A1A1R3R2A3S29SbSfR5R3A2SfR5R4A2M3A3F_;F_;Frho';Frho;Fn;S29S8G1A1S12Vsegs;RaR9R8S1fSdS14SeR7A4S1fSdS14SeR6A4A6S4G1R5A2A3S20S10S13S5SdR8R7A3A1R6A3SdS16S1S28Q40A1A1M4S1eSdR3RbA3S1dVsegs;S2cVsegs;S11R4A1G2R3R2A5M5S1cS2aS2eVsegs;ReG3R1A4RbG3R1A2A2Lw;A3F_;Ftp;Frho;FE;SdS16G4S1eSdR3RdA3S1dVsegs;G5RbSfR4R3A2A1A3F_;Ftp;Frho;Fn;F_;F_;F_;F_;F_;F_;FQ;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es Q HQ Hst Hms Hes Hedges Hexits n rho tp Hin.
  set (B := ena_meas n rho).
  set (I := fun (a : Z) (w : world) =>
              exists n rho tp, In n (cuts ++ exits) /\ SPA segs (ena_pred n) (ena_state n) rho tp w /\ ena_meas n rho = a /\ 0 <= a /\ a <= B).
  assert (ROUND : forall n0 rho0 tp0 w, In n0 cuts -> SPA segs (ena_pred n0) (ena_state n0) rho0 tp0 w ->
            exists w' nj rhoj, wsteps segs w w' /\ In nj (cuts ++ exits)
              /\ SPA segs (ena_pred nj) (ena_state nj) rhoj tp0 w'
              /\ 0 <= ena_meas nj rhoj < ena_meas n0 rho0).
  { intros n0 rho0 tp0 w Hcut Hsp0.
    destruct (In_nth_error _ _ Hcut) as [k Hk].
    assert (HkT : nth_error (map ena_state cuts) k = Some (ena_state n0)) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edgesA in Hes.
    destruct (cuts_edgesA_spec segs fuel cutpcs g (map ena_state cuts) 0 (map ena_state cuts ++ map ena_state exits) es Hes k _ HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    destruct (sym_run_etripleA segs fuel cutpcs (ena_state n0) leaves (ena_pred n0) rho0 tp0 Hlen (Hst n0 Hcut) Hrun w Hsp0) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & X & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_okA in EOK. cbn [ea_src ea_tgt ea_leaf ea_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold enodeA in *.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
    destruct w' as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (FACTS : Forall (holds rho'') (ss_facts (ax_S (la_state L)))) by (eapply smatchA_facts; exact Hsm).
    destruct (EOK n0 nj ltac:(rewrite nth_error_app1; [exact Hk| apply nth_error_Some; congruence]) eq_refl rho'' rho'' tp0 tr md
                (agree_below_refl _ _) Hkk FACTS) as [HGj HMj].
    rewrite (Hms n0 rho0 rho'' Hcut Hag) in HMj.
    exists (tr, mkCfg ms md), nj, (rho_sub rho'' s). split; [exact Hsteps|]. split; [eapply nth_error_In; exact HnXG|].
    split; [|exact HMj]. split; [rewrite HX; eapply smatchA_entails; eauto | exact HGj]. }
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q B w)).
  { intros a w (n0 & rho0 & tp0 & Hin0 & Hsp0 & Hm0 & Ha0 & HaB).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    - destruct (ROUND n0 rho0 tp0 w Hcut Hsp0) as (w' & nj & rhoj & Hsteps & Hinj & Hspj & Hmj).
      exists w'. split; [exact Hsteps|]. left. exists (ena_meas nj rhoj). split; [unfold Zwf; lia|].
      exists nj, rhoj, tp0. split; [exact Hinj|]. split; [exact Hspj|]. split; [reflexivity|lia].
    - destruct (Hexits n0 rho0 tp0 Hexit w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho1 & tp1 & Hin1 & Hsp1 & Hm1).
        exists w'. split; [exact Hsteps|]. left. exists (ena_meas n1 rho1). split; [unfold Zwf; lia|].
        exists n1, rho1, tp1. split; [apply in_or_app; left; exact Hin1|].
        split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. apply (HQ (ena_meas n0 rho0) B w'); [lia | exact Hq]. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I (Q B) BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (ena_meas n rho) 0) as [Hneg|Hnn].
  - exfalso. destruct (ROUND n rho tp w Hin Hw) as (w' & nj & rhoj & _ & _ & _ & Hmj). lia.
  - apply (LOOP (ena_meas n rho)). exists n, rho, tp. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hw|]. split; [reflexivity|]. subst B. lia.
Qed.
End G.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S33S16S1S28Q40A1A1S31OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S32Vsegs;VAInv;VCST;A3").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S3S3SbSbA2SbA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Variable Phis : ltac2:(tb__ "0|0|
S1S3S1ScA1S16OF_;A2A1").
Hypothesis HPhis : ltac2:(tb__ "0|3|
S20S3S1ScA1M0S16OF_;M1A2M2G2S27S7G0G1R1A3S9G0G1R1A3A2Lp;VPhis;A3").

Local Notation enodeIAF := (enodeIAF AInv CST XGL NP Kc rho0 P0f FB FF BX PA Phis).
Local Notation JAF := (JAF AInv CST XGL NP Kc rho0 P0f FB FF BX PA).
Local Notation phiK := (phiK Phis).

Theorem cfg_complete_JAF_b : ltac2:(tb__ "0|9|
S2S1SbA1ScS1S21A1M0G0SbS1cOF_;F_;SbSbS1cS2fR3R2A2R5R4R2A2R6R4R3A2F_;F_;Fw;Fb';Fb;S29S6S26Vsegs;VNP;VPhis;R7R6R5R4R3A8SaA3S14S1aS2S3SbS18A2M1S16S1S28Q40A1A1M2S1eS3S3S3S14S1aA2M3S2A2M4G1A2M5S0G4G1S0G3S2S0S14S1aR6R5A4R4A4R3A4M6RaA3S1dVsegs;S2cVsegs;S25VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S24VPhis;R5A2R6AdR7R3R2A5M7S1cS2aS2eVsegs;S1fS21SdS23VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcRdA4S22S0G4G1S0G3S2S0S14S1aR8R7A4R6A4R5A4R4A2M8R1A4RbG8R1A2A2Lw;A3F_;Ftp;Frho;Frv;FkX;FndX;FX;S14S1aS2G1S16G2S1eG5G6RcA3S1dVsegs;G7RbS22S0G4G1S0G3S2S0S14S1aR7R6A4R5A4R4A4R3A2A1A3F_;Ftp;Frho;Frv;FkT;FndT;FT;F_;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using ALA HKc HPhis.
  intros fuel cutpcs g cutsE exitsE Q HQ Hc Hexits T ndT kT rv rho tp HinT.
  rewrite ejcertAF_ref_eq in Hc. unfold ejcertAF_ref in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edgesA segs fuel cutpcs g (map ef_state cutsE) (map ef_state exitsE)) as [es|] eqn:Hes; [|discriminate].
  change (efmeasA (T, ndT, kT, rv) rho) with (ena_meas (enodeIAF (T, ndT, kT, rv)) rho).
  apply (cfg_complete_genTA_b segs fuel cutpcs g (map enodeIAF cutsE) (map enodeIAF exitsE) es Q HQ) with (n := enodeIAF (T, ndT, kT, rv)).
  - intros n Hin. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X.
    apply andb_prop in X as [X HV]. apply andb_prop in X as [X _]. apply andb_prop in X as [X Hn]. apply andb_prop in X as [_ Hb]. apply Pos.leb_le in Hn.
    cbn [TobjJAF.enodeIAF ena_state ena_pred fst snd].
    apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA HKc (VK Phis (ef_k d)) (phiK (ef_k d)) (phiK_reads Phis HPhis (ef_k d))); [exact Hn | exact Hb | exact HV].
  - intros n rho1 rho2 Hin Hag. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ Hvb].
    cbn [TobjJAF.enodeIAF ena_state ena_meas fst snd] in *. unfold efmeasA.
    rewrite (eval_agree_vals _ rho1 rho2 _ (agree_below_vals _ _ _ Hag) Hvb). reflexivity.
  - rewrite !(map_ef_state AInv CST XGL NP Kc rho0 P0f FB FF BX PA Phis). exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He. apply (eecheckJAF_sound segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA Phis HPhis). exact (proj1 (forallb_forall _ _) Hc e He).
  - intros X rho' tp' Hin. apply in_map_iff in Hin as ([[[S k] kk] r] & <- & Hin). cbn [TobjJAF.enodeIAF ena_state ena_pred ena_meas ef_state ef_nd ef_k fst snd].
    exact (Hexits S k kk r rho' tp' Hin).
  - exact (in_map enodeIAF cutsE _ HinT).
Qed.

Lemma ereenter_cutJAF_b : ltac2:(tb__ "0|4|
S1S21A1S14S1aS2S3SbS18A2M0S1cOF_;SbS16S1S28Q40A1A1S1eS3S3S3S14S1aA2M1S2A2M2G0A2S0G2G0S0G1S2S0S14S1aR8R7A4R6A4R5A4R9A3S24VPhis;R7R3A3S2bS2fZ0S22S0G2G0S0G1S2S0S14S1aRaR9A4R8A4R7A4R4A2M3A2S30G3R5A2A2S1dVsegs;S2cVsegs;S1bVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;RaAcRbR5R4A5S1cS2aS2eVsegs;S1fS21SdS23VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcRdA4R7R1A4R8R1A1A2Lw;A3F_;F_;F_;Ftp;Frho;Fbound;FQ;Frv;Fk;Fnd;FT;FcutsE;").
Proof using .
  intros cutsE T nd k rv Q bound rho tp Hin HP Hm.
  exact (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA Phis cutsE T nd k rv Q bound rho tp Hin HP Hm).
Qed.
End Sum.
End WithSegs.
End TobjJAFb.

(* [comment removed for export] *)
Module AddCellsA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "ss_next"; "ss_objs"; "SLit"; "agree_below"; "dflt_writable"; "ob_dflt"; "ob_hi"; "ob_lo"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "false"; "option"; "andb"; "bool"; "list"; "Some"; "nat"; "pair"; "true"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "ltb"; "opp"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA"; "add_cells8"; "add_cells8_ok"; "obj_lit_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "add_cell8_state"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymFrame SymEntail SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJAF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition add_cell8_at (S : sstate) (i : nat) (z : Z) : sstate := ltac2:(tb__ "0|0|
S10S1A1SbLx;S18S1S4VS;A1Vi;A3S1S33VS;Vi;R1S5Vz;A1A4Lo;VS;X10x2").
Fixpoint add_cells8 (S : sstate) (i : nat) (offs : list Z) : sstate :=
  match offs with [] => S | z :: r => add_cells8 (add_cell8_at S i z) i r end.

Definition obj_lit_room (o : sobj) (offs : list Z) : bool := ltac2:(tb__ "0|8|
S11S7S8Vo;A1A1S0S12Lx;M0SaVo;A1ScG0S9Vo;A1ScS11S11S1dS20S21Z2Z3eA2M1A1R2A2S1fR1G1A2A2S19ScScS11S1dR3R1A2S1dS1eR1Z8A2R2A2A2Lz;Voffs;A3A2Lhi;SdSfLi;M2S2dS0S0SfLb;La;M3Lop;M4G4S2eG3Lop;M5G5S12SeS0SfLa;Lw;Lsgn;M6SdS0ScSfLk;Li;Ll;M7X0x8Llo;G2G4G4G5G5G6G7X0x8A2").
Definition add_cells8_ok (S : sstate) (i : nat) (offs : list Z) : bool := ltac2:(tb__ "0|0|
S10S1A1S12Lx;S18S1S4VS;A1Vi;A3S1S32R1Voffs;A2Lo;SfX10x2").

Lemma nth_error_list_set_same {A} : ltac2:(tb__ "0|1|
S13VA;A1S15VA;VA;S1aS10VA;A1M0S18VA;R4R3A3S14VA;R1A2A3S1aG0S18VA;S2fVA;R5R4R3A4R4A3S14VA;R3A2A3F_;Fy;Fx;Fi;Fl;").
Proof. induction l as [|h t IH]; intros [|i] x y H; cbn in *; try discriminate; [reflexivity | eapply IH; exact H]. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma SPA_add_cells8 : ltac2:(tb__ "0|3|
S13ScA1S25S2S13S35Q40A1A1S29S15S13S2cA1M0S2aS2bSdS34S3S27R6A1M1A1R1A2S26Vsegs;R2RaA3F_;Fn;S1aS12S31G1R5RaA3S17A3S24Vsegs;RaR7R9R8S16G0S22R5S23R4R3A2A4A6S1cS2S2S1bS6S3S27R9A1M2A1RbR1A3S24Vsegs;RcS28R9S30G2R8RdA3A2R1RaS16G0S22R7S23R6R5A2A4A6A2Lrho';A2F_;F_;F_;Fmd;Fms;Ftr;Fi;FA;Ftp;Frho;FJ;Foffs;").
Proof using .
  induction offs as [|z r IH]; intros J rho tp A i tr ms md Hst Hok Hw.
  - exists rho. split; [repeat split; intros; reflexivity|]. cbn [add_cells8]. destruct A as [S X b]. exact Hw.
  - unfold add_cells8_ok in Hok. destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Ho; [|discriminate].
    unfold obj_lit_room in Hok. apply andb_prop in Hok as [Hdw Hb].
    destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
    apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hlo62 Hhi62]. cbn [forallb] in Hall. apply andb_prop in Hall as [Hz Hr].
    apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hlo62, Hz1, Hz2. apply Z.ltb_lt in Hhi62.
    destruct (SPA_add_cell8 segs J rho tp A i o (SLit z) tr ms md (Hst _ (Pos.le_refl _)) Ho Hdw eq_refl) as (bs & rho1 & _ & Hag1 & _ & Hw1).
    + unfold obj_lo_of. rewrite Elo. rewrite !soff_lit_small by lia. exact Hz1.
    + unfold obj_hi_of. rewrite Ehi. rewrite !soff_lit_small by lia. exact Hz2.
    + exact Hw.
    + set (A1 := ax_setS A (add_cell8_state (ax_S A) i o (SLit z))) in *.
      assert (Hn1 : ss_next (ax_S A1) = Pos.succ (ss_next (ax_S A))) by reflexivity.
      destruct (IH J rho1 tp A1 i tr ms md) as (rho2 & Hag2 & Hw2).
      * intros n Hn. apply Hst. rewrite Hn1 in Hn. lia.
      * unfold add_cells8_ok, A1. cbn [ax_S ax_setS add_cell8_state ss_objs].
        rewrite (nth_error_list_set_same _ _ _ _ Ho). unfold obj_lit_room, obj_add_cell. cbn [ob_dflt ob_lo ob_hi]. rewrite Hdw, Elo, Ehi.
        cbn [andb]. apply andb_true_intro. split; [apply andb_true_intro; split; [apply Z.leb_le; exact Hlo62 | apply Z.ltb_lt; exact Hhi62] | exact Hr].
      * exact Hw1.
      * exists rho2. split.
        -- eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [|exact Hag2]. rewrite Hn1. lia.
        -- cbn [add_cells8]. unfold add_cell8_at. rewrite Ho. destruct A as [S X b]. exact Hw2.
Qed.
End WithSegs.
End AddCellsA.

(* [comment removed for export] *)
Module TobjJAK.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "True"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "fst"; "app"; "pair"; "Some"; "option"; "cons"; "snd"; "nil"; "None"; "nat"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sv"; "ss_facts"; "sobj"; "sprop"; "rm"; "SLit"; "SVar"; "holds"; "eval"; "sv_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_tv"; "NDA"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "JA_pre"; "am_subst"; "ok_frameKA"; "TPA"; "am_eqb"; "amode"; "fbinA"; "ffinA"; "frinA"; "tvinA"; "JA"; "JAi"; "JAk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "cls_keptA"; "cls_kept_freeA"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "sv_subst"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "wsub_dom_below"; "call_linkP"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "uval"; "bd_below"; "bxt"; "KU"; "bd_subst"; "BXok_d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Pre_malloc"; "Pre_free"; "L_malloc_ok"; "L_free"; "L_malloc_null"; "ulink"; "unwind_stopJ"; "ustop"; "KcA"; "V_RES"; "alloc_contractsA"; "alloc_contractsA_ex"; "free_shape"; "malloc_shape"; "JL_free"; "J_alloc_pre"; "J_free_pre"; "Posts_malloc"; "alloc_lawsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "call_checkPA"; "entails_frA"; "import_subA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pdescA"; "FFx"; "PostsC"; "T_afterA3"; "pd_okA"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK.WithSegs.Rt"; "keptR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "site_okA"; "payA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "leb"; "pow"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "FBx"; "tnz"; "tvv"; "T_ok"; "import_tv"; "tv_sub_eqb"; "tvd"; "tvz"; "ivar_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK.WithSegs.Client"; "pdescK"; "PostsCk"; "keptK"; "psiK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK.WithSegs"; "PostsCk"; "liftPD";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "JLAP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAF.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S3dS18S5S46Q40A1A1S6eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6cVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S24Sa7VCST;R1A2S1S8bZ0R2A2S8cR2Sa5A2A2F_;Fa;").
Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.
Hypothesis HXGL : ltac2:(tb__ "0|0|
S24Sa7VXGL;R1A2S1S8bZ0R2A2S8cR2Sa5A2A2F_;Fa;").

Section Client.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S8S8S24S24A2S24A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Context {dC : Z}.
Variable P0c : ltac2:(tb__ "0|1|
S5S8S24S24A2M0A1S5S8G0S24A2A1S18OF_;F_;F_;").
Variable PAc : AA -> Prop.
Hypothesis HPAc0 : ltac2:(tb__ "0|0|
S3dVPA;R1A1VPAc;R2A1F_;FA;").
Hypothesis HPAc : ltac2:(tb__ "0|0|
S3dS3dVPA;R2A1VPAc;R2A1VPA;R3A1F_;F_;FA';FA;").
Variable PreC : axst.
Variable ndC : ndesc.

Definition pdescK : Type := ltac2:(tb__ "0|0|
S8S8S15S29A2S18S18OF_;F_;A2").
Variable PD : list pdescK.
Variable NPc : positive.
Hypothesis HnextPre : ltac2:(tb__ "0|0|
S0S25S19S14VPreC;A1A1VNPc;A3").
Hypothesis HfrC : nd_fr ndC = [].
Hypothesis HbaseC : ltac2:(tb__ "0|0|
S0S1aS17VPreC;A1S1fSa6A1A3").

Let JAi : ltac2:(tb__ "0|0|
S29S3dS24S27Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S3bVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S29S27Fnd;") := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let payA : ltac2:(tb__ "0|1|
S5S1dA1S1aS24S5S53A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S87VNP;Vrho0;VP0f;A3").

Local Abbreviation FFx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.FFx FF).
Local Abbreviation BXx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.BXx BX).
Local Abbreviation pclMA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA CST rho0).
Local Abbreviation robjs_okF := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.robjs_okF CST rho0 FB FF).
Local Abbreviation xrs_okF := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xrs_okF CST XGL rho0 FB FF).
Local Abbreviation bdL_ok := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.bdL_ok NPc).
Local Abbreviation amL_ok := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.amL_ok NPc).
Local Abbreviation pd_okA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pd_okA PreC NPc).
Local Abbreviation BXx_nonneg := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.BXx_nonneg BX HBX).
Local Abbreviation In_FFx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.In_FFx FF).
Local Abbreviation pclMA_pclFA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_pclFA CST rho0).
Local Abbreviation T0_calleeA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.T0_calleeA NP rho0).
Local Abbreviation TPA_calleeA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.TPA_calleeA NP rho0).
Local Abbreviation pclMA_pclFA_callee := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_pclFA_callee CST NP rho0).
Local Abbreviation pclMA_cmaddrA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pclMA_cmaddrA CST rho0).
Local Abbreviation fbinA_FBx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.fbinA_FBx FB).
Local Abbreviation ffinA_FFx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.ffinA_FFx FF).
Local Abbreviation fcensus_FFx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.fcensus_FFx FF).
Local Abbreviation live_not_pclMA := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.live_not_pclMA segs AInv CST ALA HCST rho0).
Local Abbreviation untracked_kept_FBx := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.untracked_kept_FBx FB).

Definition PostsCk (FBc : list (Z * Z)) (FFc : list (Z * Z * Z)) (BXc : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|4|
S8aS8S8S15S29A2M0S18S18OF_;F_;M1A2M2S8S15S71A2G2SbS15S71S9S15S29S9G0G1R1A3M3A3Sa8VAInv;VCST;VXGL;VKc;VP0c;VFBc;VFFc;A2VFBc;VFFc;VBXc;VPAc;SfS15S29G3A3SfG0G1R1A3AbA4Ld;VPD;A4").

Definition keptK (rho : valuation) (kept : list (sv * sv)) (fr : list (sv * Z * sv)) (rho' : valuation) : Prop := ltac2:(tb__ "0|1|
S24S1S8bZ0R1A2S8cR1S8eZ2Z40A2A2A2S82VCST;Vrho0;S93VFB;Vrho;Vkept;A3S7bVFF;Vrho;Vfr;A3R2A5S0SdS46Q8A1A1S1eVrho';S47Q40R3A2M0A2S1eVrho;G0A2A3F_;F_;Fa;").
Definition psiK (Psi : valuation -> valuation -> Prop) (Cl : axst) (s : wsub) (R : list sobj) (L : axst) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|2|
S2S18S18S2S18S18S1VPsi;R2R1A2S1S1aS0S46Q40A1M0S22R3R1A2S22Vrho;S4cVs;R1A2A2A3Fe;S1G0S4S4dVrho;VR;R1A3A1S1S0SdS46Q8A1A1M1S1eR4R2A2S1eVrho;R2A2A3S0G1S1eVrho';R2A2S1eR3R2A2A3A2F_;Fa;S1aS0S6S52S9bVNPc;Vs;S19S14VCl;A1A1S14VL;A1A4R1A2S7A3S0G0S22Vrho';S4cS74Vs;VPreC;VL;VCl;A4R2A2A2S22R3R2A2A3F_;Fe;A2A2A2LrhoL;A2Lr0c;A2").

Section CallTCk.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27S15S18S5S46Q40A1A1S42S89S1dS21R3A1S1bS14R4A1A1A3VTR;S26Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S42S42S42S43R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27S15S15S4bS5S1cA1M0S5S8S15S71A2M1A1S5S8S1aS1aA2M2A1S42S18S5S46Q40A1A1M3G2S77G2R1R5A3S77G2R2S16RbA1A3F_;Fr;S0SdG0A1S73RaR9R8A3ScG0R7A2A3S0S6S72RbRaR9R8S8aG1S15S9S15S71A2R7A4A5S7A3S18G3VTR;S26Vsegs;RfRdR2R1A5S70Vsegs;S19S14RdA1A1R2R1RaA5A2Ftp1;Frho1;S5S6fA1M4S6dS6eS28Vsegs;R9R8R10SbG4S90R3S91R2R1A2A4A5R13RaR9R4R2A4R13S4aS49RbRfS76R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S15S71G4S6dS6eS18G3G4S6dS6eS77G1SbS15S71RaR9A4R14A3S28Vsegs;R12R11R19SbG4S90R9S91R8R7A2A4A5R1cR13R12RaR8A4S4eS19S14R1aA1A1S4aS49R14R18S76R9R13RaA3A3R19A2R8A3S28Vsegs;R9R8ReSbG4S90R7S91R6R5A2A4A5ReS4aS49R16R1aS76RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sa3R17S76RcR16RdA3R1bR1cR1dR10R1eR19RbA9S18S51R18S76RdR17ReA3R1cR1dS14R1eA1S14R1fA1S14R11A1R1RcA9VTR;S26Vsegs;S75R11S4aS49R19R1dS76ReR18RfA3A3R1eA2R18RdRcA5Sa4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis SUMT : ltac2:(tb__ "0|1|
S5S8S24S24A2M0A1S5S8G0S24A2A1S56S18S5S46Q40A1A1S59VdC;R3A2VTR;S26Vsegs;S30VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S70Vsegs;VNPc;R3R2S9dR6R5R4A3A5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis Hdd : ltac2:(tb__ "0|1|
S0S6S13S8dZ1M0VdC;A2S8dS8fVdC;G0A2VdF;A2A2S7A3").

Theorem client_callT_k : ltac2:(tb__ "0|e|
S15S4bS5S1cA1M0S5S8S1aS1aA2M1A1M2S18S5S46Q40A1A1M3G2G2S5S8S8S1aS24A2S1aA2A1S5S53A1M4G4S35S42S0S6S80RaS16RdA1A2S7A3S0SdG0A1S73ReVPreC;RdA3ScG0RcA2A3S0S6S72RfVPreC;ReRdS8aS8S8S15S29A2M5S18S18OF_;F_;M6A2M7S15G7S9S15S29S9G5G6R1A3A3Ld;VPD;A4A5S7A3S0S6S85VNP;RfA2S7A3S0S6S50R10VNPc;A2S7A3S0S6S88VNP;S19S14R12A1A1A2S7A3S0S6S2eS19S14R13A1A1S2bSaG1RdRcA3RbRaR8A4A2S7A3S0S6S55S19S14R14A1A1RaA2S7A3S0S6S98R14ReS2aVndC;A1A3S7A3S0S6S34S31R15S2cVndC;A1A2RbA2S7A3VpayA;S1bS14R17A1A1S1fZ0M8A1G8ReSaS53S58R16S2dVndC;A1A2RdA3A5S0S6S78S8S7aG6A2M9G9S7eVPreC;VNPc;R18S19S14R19A1A1S9S7aG6R1A3A5Ld;VPD;A3S7A3S3dS6dS89S1dS21R17A1S1bS14R1bA1A1A3VP0f;Vrho0;A1S4eVNP;Vrho0;R19A3S36VFB;R5A2S37VFF;R6A2S39VFB;R7R1cSaG1R1aR19A3A4S99R1dSaG1R1bR1aA3A2S9aR1eSaG1R1cR1bA3A2S38VFF;RaR1fR1bA4S2S18S18S2G3G3S2S6eS6eVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S33Vrho0;RcA2S96R22S41S3eRdA1A1A2S1S7fVCST;Vrho0;VFB;VFF;R23R21R1fR25A8S1S81VCST;VXGL;Vrho0;VFB;VFF;R23R21R1fR24A9VP0c;S93VFB;R23R21A3S7bVFF;R23R1fA3S4aS49R23R25RdA3R26A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S9cS18G3S77S9cR3VPD;A3S4eS19S14R1eA1A1R1aR3A3S9eR1bR19R17R4A4S9fSfG5G6R6A3R20R1fR1eS9S15S29S9G5G6R6A3A3R1cR5A7VTR;S26Vsegs;VJA;S2bSaG1R1bS97S74R20VPreC;S9S15S29S9G5G6R7A3MaA3MbR21A4McS2aSfS15S29GaA3MdA1A2A3R19SaS53S58GcS2dGdA1A2R17A3S31GcS2cGdA1A2A4A1S7dVPreC;R21R20R1fGbR1eA6R6R5A5R15A2F_;F_;F_;F_;Ftp';Frho';Fd;VTR;S26Vsegs;VJA;S2bSaG1R15R14A3R13R12R10A4A1R1bR17R16A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;").
Proof using ALA HCST HXGL HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUMT Hdd TR_callP TR_ex TR_facts TR_pre.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros Cl s R Xk rho tp kept passed fr bd brest am Q HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass Ham HPAY Hpd HIN Tcont.
  pose proof (xrs_inclb_sound _ _ HXk) as HXk'. apply am_eqb_sound in Ham.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA (kept ++ passed) fr bd am))). intros Ai.
  apply (TR_ex Z (JAi (NDA (kept ++ passed) fr bd am) Ai)). intros kc.
  pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am] in Hbt, Hbf, Hbb, Hba. clear Hnb.

  assert (PASS : forall ms, map (tvv (rho_sub (rho_absorb rho R ms) s)) (nd_tv ndC) = map (tvv rho) passed
                 /\ forall k t t', nth_error passed k = Some t -> nth_error (nd_tv ndC) k = Some t' -> (tnz (rho_sub (rho_absorb rho R ms) s) t' <-> tnz rho t)).
  { intros ms. destruct (tv_sub_eqb_sound s passed (nd_tv ndC) (rho_absorb rho R ms) Hpass) as [M1 M2].
    assert (EA : forall l, map (tvv (rho_absorb rho R ms)) l = map (tvv rho) l).
    { intros l. apply map_ext. intros t. unfold tvv. rewrite !eval_absorb. reflexivity. }
    split; [rewrite M1; apply EA|]. intros k t t' Ht Ht'. rewrite (M2 k t t' Ht Ht'). unfold tnz. rewrite eval_absorb. tauto. }
  assert (EVA : forall ms e, eval (rho_sub (rho_absorb rho R ms) s) e = eval (rho_sub rho s) e).
  { intros ms e. rewrite <- !eval_subst. apply eval_absorb. }
  eapply (TR_callP (JAi (NDA (kept ++ passed) fr bd am) Ai kc) (JA_pre AInv CST XGL Kc (P0c (FBx FB rho kept) (FFx rho fr)) (FBx FB rho kept) (FFx rho fr) (BXx rho brest kept) PAc ndC)
            Cl PreC s R (PostsCk (FBx FB rho kept) (FFx rho fr) (BXx rho brest kept)) Xk Q rho tp HXk' He).
  - unfold PostsCk. rewrite map_map. cbn [fst]. exact Hchk.
  - intros rho1 tp1. rewrite HnextPre. apply SUMT. apply (BXx_nonneg dC rho brest kept Hdd).
    pose proof (nd_below_len _ _ Hnb0) as HL0. cbn [nd_tv] in HL0. rewrite length_app in HL0. lia.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
    destruct (HIN Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & HPc).
    destruct (PASS (vms md tp ms)) as [PM PZ].
    pose proof (fbinA_FBx Ai rho kept passed HB HN) as FBX. pose proof (ffinA_FFx Ai rho fr HFF HFR) as FFX.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [exact FBX | exact FFX | exact HT | exact (HRok o a Ho Hr)]. }
    assert (RNOTSH0 : forall a, in_ranges rho R a -> ~ is_shadowZ (bv_unsigned a)).
    { intros a Hin. eapply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None _ rho tp md HM). destruct Hin as (o & Ho & Hr). exact (HRokA o _ Ho Hr). }

    assert (EAM : am_eval (rho_sub (rho_absorb rho R (vms md tp ms)) s) (nd_am ndC) = am_eval rho am).
    { rewrite <- am_eval_subst, Ham. apply am_eval_exteq. intros e _. apply eval_absorb. }
    destruct (XAz_transport FB (FBx FB rho kept) (am_eval rho am) Ai Ai (rm rho) (rm (rho_sub (rho_absorb rho R (vms md tp ms)) s)) (tvals rho (kept ++ passed)) (map (tvv rho) passed) kc HXA) as [XEXP PEXP].
    { intros b n H1 H2 H3. split; [exact H1|]. exact (untracked_kept_FBx rho kept passed b n H3 H2). }
    { intros b n z H1 H2 H3 Hz. apply rm_absorb_out. intros Hin. destruct Hin as (o & Ho & Hr).
      destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl0 & _). destruct (HBl0 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
      eapply (live_not_pclMA Ai rho tp md (FBx FB rho kept) (FFx rho fr) b n z HM FBX FFX HT H1 (proj1 (untracked_kept_FBx rho kept passed b n H3 H2))); [exact Hz|].
      apply (HRok o _ Ho). rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). exact Hr. }
    { intros b n a H1 H2 H3 Ha.
      destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl0 & _). destruct (HBl0 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
      assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
      split.
      - intros _. apply rm_absorb_out. intros Hin. apply (RNOTSH0 _ Hin). rewrite shadow_addr_Sh, Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia].
      - intros j Hj Hdef. rewrite rm_absorb_out; [exact Hdef|]. intros Hin. apply (RNOTSH0 _ Hin).
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [exact HSa | exact Hj]. }
    {
      intros bn H1 _ H3 H4. destruct (untracked_FBx_kept FB rho kept passed bn H3 H4) as [G1 G2]. split; [exact H1 | split; [exact G1 | exact G2]]. }
    split; [exact Hk|]. exists Ai, kc.
    split; [eapply AInv_absorb; eauto|].
    split; [exact (proj2 (TPA_calleeA Ai s rho R (vms md tp ms) Hav Htp) HT)|].
    split; [exact FBX|]. split; [exact FFX|].
    split; [split; [|split]| split; [rewrite HfrC; split; [constructor | exact (fcensus_FFx Ai rho fr _ HFR)] | split; [apply keptFA_refl | split; [exact HPc|split; [unfold XA, tvals; rewrite EAM, PM; exact XEXP|split; [|split; [exact (HPAc0 _ HPA) | split; [exact HCKi|

      unfold capN in *; cbn [nd_tv] in HCNi; rewrite cntS_app in HCNi; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.BXx; cbn [bxN]; rewrite (cntS_map _ _ _ _ PM); lia]]]]]]]].
    +
      unfold tvinA. apply Forall_forall. intros tc Htc Hnz.
      destruct (In_nth_error _ _ Htc) as [k Hk'].
      assert (exists tq, nth_error passed k = Some tq) as [tq Htq].
      { pose proof (Forall2_map_eq _ _ _ _ PM) as L. destruct (nth_error passed k) eqn:En; [eexists; reflexivity|].
        exfalso. apply nth_error_None in En. assert (k < length (nd_tv ndC))%nat by (apply nth_error_Some; congruence). lia. }
      rewrite (map_nth2 _ _ _ _ k tq tc PM Htq Hk'). apply (proj1 (PZ k tq tc Htq Hk')) in Hnz.
      pose proof (nth_error_In _ _ Htq) as HinP.
      destruct (proj1 (Forall_forall _ _) HN tq ltac:(apply in_or_app; right; exact HinP) Hnz) as (X0 & X1 & X2).
      split; [exact X0|]. split; [exact X1|]. intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnzt & Heq)]; [exact (X2 Hin)|].
      exact (tvd_app_cross rho kept passed t tq HD Ht HinP Hnzt Hnz Heq).
    + eapply tvd_map; [exact PM | exact PZ | exact (tvd_app_r rho kept passed HD)].
    + eapply tvz_map; [exact PM | exact PZ |]. unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. exact Ht.
    +
      destruct (BUD_splitF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S Cl)) bd (bd_subst s (nd_bd ndC)) brest _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF (conj HP0 Hav) HPAY HBU) as [B1 [Wr0 Nr0]].
      pose proof (bsum_nonneg brest rho Wr0 Nr0) as [BN1 BN2].
      assert (EP : apot (nd_am ndC) (rho_sub (rho_absorb rho R (vms md tp ms)) s) = apot am rho) by (unfold apot; rewrite EAM; exact PEXP).
      rewrite EP. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.BXx, bxa, bxV, bxK. cbn [bx2]. rewrite (Z.max_r 0 (bsumV brest rho)) by lia. rewrite (Z.max_r 0 (bsumK brest rho)) by lia.
      unfold BUD in B1 |- *. rewrite bsumV_subst, bsumK_subst, bd_wpos_subst in B1. unfold bxa in B1. cbn [fst snd] in B1 |- *.
      assert (AG : forall b, bsumV b (rho_sub (rho_absorb rho R (vms md tp ms)) s) = bsumV b (rho_sub rho s)
                            /\ bsumK b (rho_sub (rho_absorb rho R (vms md tp ms)) s) = bsumK b (rho_sub rho s)).
      { intros b. apply bsum_eval_ext. exact (EVA (vms md tp ms)). }
      destruct (AG (nd_bd ndC)) as [-> ->]. destruct B1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      split; [lia|]. split; [lia|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
      split; [|split; lia].
      apply bd_nn_subst in Q7. eapply bd_nn_eval_ext; [|exact Q7]. intros e. symmetry. apply EVA.
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
    unfold PostsCk in HinL. apply in_map_iff in HinL as ([[Ld ndL] PsiL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
    destruct (HIN Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & HPc).
    pose proof (proj1 (forallb_forall _ _) Hpd _ Hd) as Hpdd. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.pd_okA in Hpdd. cbn [fst snd] in Hpdd.
    apply andb_prop in Hpdd as [Hpdd HamL].
    apply andb_prop in Hpdd as [Hpdd HbaseL]. apply sv_eqb_sound in HbaseL.
    apply andb_prop in Hpdd as [Hpdd HpostX]. apply andb_prop in Hpdd as [Hpdd HbdL]. apply andb_prop in Hpdd as [Hpdd HfrL]. apply andb_prop in Hpdd as [HtvL Hnew].
    destruct HJL as [(HkL & A' & kcL & HM' & HT' & HB' & HFF' & (HNc & HDc & HZc) & HFRc & [HKc1 HKc2] & HP0c & HXAc & HBUc) HPSI].
    pose proof (fbinA_FBx Ai rho kept passed HB HN) as FBX. pose proof (ffinA_FFx Ai rho fr HFF HFR) as FFX.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [exact FBX | exact FFX | exact HT | exact (HRok o a Ho Hr)]. }
    assert (HRokA' : forall a, in_ranges rho R a -> cmaddrA CST A' None (bv_unsigned a)).
    { intros a (o & Ho & Hr). eapply pclMA_cmaddrA; [exact HB' | exact HFF' | exact (proj1 (TPA_calleeA A' s rho R (vms md tp ms) Hav Htp) HT') | exact (HRok o _ Ho Hr)]. }
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He) as HbC.
    destruct (law_blocks _ _ _ ALA A' _ _ _ HM') as (HPD' & HBl' & HFr').
    assert (XR47 : forall r a, In r Xk -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) -> 0 <= a < 2 ^ 47).
    { intros r a Hr Ha. destruct (HX r a Hr Ha) as [Hp|Hg]; [|apply HXGL in Hg; unfold IMG_HI, LOW_SHADOW_BEG in Hg; lia].
      exact (pclFA_range segs AInv CST ALA HCST _ _ _ Ai rho tp md a HM FBX FFX HT (pclMA_pclFA _ _ _ Hp)). }

    assert (NEWOBJ : forall o', In o' (new_objs (ax_S PreC) (ax_S Ld)) ->
              exists p n', fst (obj_range rhoL o') = p /\ (snd (obj_range rhoL o') <= p \/ (snd (obj_range rhoL o') = p + n'
                           /\ In (p, n') (aa_live A') /\ ~ In (p, n') (FBx FB rho kept) /\ 0 < n'))).
    { intros o' Hin'.
      unfold new_objs_tv in Hnew. pose proof (proj1 (forallb_forall _ _) Hnew o' Hin') as Ho'.
      apply existsb_exists in Ho' as ([vd vsz] & Hvn & Heqs). cbn [fst snd] in Heqs.
      apply andb_prop in Heqs as [Heqs E3]. apply andb_prop in Heqs as [E1 E2].
      apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
      destruct o' as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in E1, E2, E3. subst ob olo ohi.
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
      set (p := bv_unsigned (eval rhoL vd)). set (n' := bv_unsigned (eval rhoL vsz)).
      exists p, n'. split; [lia|].
      destruct (Z.eq_dec n' 0) as [Hz|Hnz0]; [left; rewrite Hz; cbn; lia|].
      assert (Hnz : tnz rhoL (vd, vsz)).
      { intros Hz. pose proof (proj1 (Forall_forall _ _) HZc _ Hvn (fun H => H Hz)) as Z0. unfold tvv in Z0. cbn [fst snd] in Z0. fold n' in Z0. lia. }
      destruct (proj1 (Forall_forall _ _) HNc _ Hvn Hnz) as (Npos & HinN & HninF). unfold tvv in HinN, HninF, Npos. cbn [fst snd] in HinN, HninF, Npos.
      fold p n' in HinN. fold p n' in HninF. fold n' in Npos.
      destruct (HBl' p n' HinN) as (_ & _ & _ & G4 & _). top_rng G4.
      right. pose proof (bv_urange (eval rhoL vsz)) as Rn. fold n' in Rn. pose proof (bv_urange (eval rhoL vd)) as Rp. fold p in Rp.
      destruct (Zsigned_spec n') as [[X8 X]|[X8 X]]; rewrite X; [|exfalso; lia]. repeat split; auto; lia. }

    assert (NEWFREE : forall p n' a, In (p, n') (aa_live A') -> ~ In (p, n') (FBx FB rho kept) -> 0 < n' -> p <= a < p + n' ->
              pclMA (FBx FB rho kept) (FFx rho fr) a -> False).
    { intros p n' a HinN HninF Hn' Ha Hc.
      destruct (HBl' p n' HinN) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      rewrite (TPA_top rho0 A' (proj1 (TPA_calleeA A' s rho R (vms md tp ms) Hav Htp) HT')) in G4.
      destruct Hc as [Hc|[Hc|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]].
      - lia.
      - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      - pose proof (HB' _ Hb) as HbA'.
        assert (Hne : (b, m) <> (p, n')) by (intros Heq; apply HninF; rewrite <- Heq; exact Hb).
        apply In_nth_error in HbA' as [i Hi]. apply In_nth_error in HinN as [j Hj].
        assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; congruence).
        assert (Hi' : nth_error (aa_live A' ++ aa_frames A') i = Some (b, m)) by (rewrite nth_error_app1; [exact Hi | apply nth_error_Some; congruence]).
        assert (Hj' : nth_error (aa_live A' ++ aa_frames A') j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
        pose proof (pd_elems _ i j _ _ HPD' Hi' Hj' Hij) as D. cbn [fst snd] in D. lia.
      - destruct (HFF' _ _ _ Hf) as [HfA' _].
        apply In_nth_error in HfA' as [k Hkk]. apply In_nth_error in HinN as [j Hj].
        assert (Hj' : nth_error (aa_live A' ++ aa_frames A') j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
        assert (Hk' : nth_error (aa_live A' ++ aa_frames A') (length (aa_live A') + k) = Some (f, sz)).
        { rewrite nth_error_app2 by lia. replace (length (aa_live A') + k - length (aa_live A'))%nat with k by lia. exact Hkk. }
        assert (Hjl : (j < length (aa_live A'))%nat) by (apply nth_error_Some; congruence).
        pose proof (pd_elems _ j _ _ _ HPD' Hj' Hk' ltac:(lia)) as D. cbn [fst snd] in D.
        destruct (HFr' f sz (proj1 (HFF' _ _ _ Hf))) as (_ & _ & G64 & _). lia. }
    assert (RNOTSH : forall a, in_ranges rho R a -> ~ is_shadowZ (bv_unsigned a)).
    { intros a Hin. eapply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None _ rho tp md HM). destruct Hin as (o & Ho & Hr). exact (HRokA o _ Ho Hr). }
    split.
    +
      split; [split|split].
      *   intros a Hina. rewrite <- (Z_to_bv_bv_unsigned 64 a).
        apply HKc1; [apply bv_urange |]. left. apply (pclMA_pclFA_callee s rho R (vms md tp ms)); [exact Hav | exact Htp |]. destruct Hina as (o & Ho & Hr). exact (HRok o _ Ho Hr).
      *
        intros o' oR Hin' HinR. destruct (NEWOBJ o' Hin') as (p & n' & Elo & [Hemp|(Ehi & HinN & HninF & Hn')]).
        -- unfold ranges_disjoint. rewrite Elo. cbn [fst snd]. destruct (obj_range rho oR); cbn [fst snd]. lia.
        -- destruct (obj_range rhoL o') as [lo hi] eqn:Eo. cbn [fst snd] in Elo, Ehi. subst lo hi.
           destruct (obj_range rho oR) as [lo2 hi2] eqn:HR2.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE p n' a HinN HninF Hn' Ha1).
           apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      *
        intros r a j oR Hr Ha Hj HoR Hrng.
        pose proof (proj1 (forallb_forall _ _) HpostX r Hr) as HPX. unfold xr_post_ok in HPX.
        assert (Ha47 : 0 <= a < 2 ^ 47).
        { apply lazy_orb_prop in HPX as [HPX|HPX].
          - unfold xr_tracked in HPX. destruct (robj_tracked_sound (nd_tv ndL) None _ HPX) as (jj & t & Hjt & _ & Hb & _ & Hh). cbn [ob_base ob_hi] in Hb, Hh.
            pose proof (nth_error_In _ _ Hjt) as Hint.
            assert (Er : tvv rhoL t = (bv_unsigned (eval rhoL (fst r)), bv_unsigned (eval rhoL (snd r)))) by (unfold tvv; rewrite Hb, Hh; reflexivity).
            destruct (Z.eq_dec (bv_unsigned (eval rhoL (fst r))) 0) as [Hz0|Hnz0].
            { exfalso. pose proof (proj1 (Forall_forall _ _) HZc t Hint) as Z0. cbv beta in Z0. rewrite Er in Z0. cbn [snd] in Z0.
              unfold tnz in Z0. rewrite <- Hb in Z0. specialize (Z0 ltac:(lia)). lia. }
            assert (Hnz : tnz rhoL t) by (unfold tnz; rewrite <- Hb; exact Hnz0).
            destruct (proj1 (Forall_forall _ _) HNc t Hint Hnz) as (Tpos & Tin & _). rewrite Er in Tin.
            destruct (HBl' _ _ Tin) as (_ & _ & G3 & G4 & _). top_rng G4. lia.
          - apply lazy_andb_prop in HPX as [P1 P2]. apply lazy_andb_prop in P2 as [P2 P3].
            pose proof (smatchA_facts segs _ _ _ _ HsmL) as HFL.
            pose proof (prove_sprop_sound rhoL _ _ HFL P1) as Q1. pose proof (prove_sprop_sound rhoL _ _ HFL P2) as Q2.
            pose proof (prove_sprop_sound rhoL _ _ HFL P3) as Q3. cbn [holds] in Q1, Q2, Q3.
            rewrite U_add, !U_lit in Q1. rewrite U_lit in Q2. rewrite U_lit in Q3. unfold M64v in Q1, Q2, Q3.
            change (2 ^ 40 mod 18446744073709551616) with (2 ^ 40) in Q2. change (2 ^ 47 mod 18446744073709551616) with (2 ^ 47) in Q1, Q3.
            pose proof (bv_urange (eval rhoL (fst r))). pose proof (bv_urange (eval rhoL (snd r))).
            rewrite Z.mod_small in Q1 by lia. unfold uval in Ha. lia. }
        apply (RNOTSH (word_byte (bv_unsigned (eval rhoL (ax_base Ld)) + a / 8) j)).
        -- exists oR. split; [exact HoR | exact Hrng].
        --
           assert (EbL : bv_unsigned (eval rhoL (ax_base Ld)) = SHADOW_OFF) by (rewrite HbaseL; cbn [eval]; rewrite lit_unsigned; reflexivity).
           rewrite EbL. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Ha47 | exact Hj].
      *
        intros r a Hr Ha. rewrite (HbC HbaseC). cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
        pose proof (XR47 r a Hr Ha) as Ha47. pose proof (Sh_is_shadow a Ha47) as HSa.
        assert (EW : Sh a = SHADOW_OFF + a / 8) by (unfold Sh; lia).
        assert (PS : pclSA CST XGL (rho_sub (rho_absorb rho R (vms md tp ms)) s) (FBx FB rho kept) (FFx rho fr) (Sh a)).
        { exists a. split; [lia|]. split; [|reflexivity]. destruct (HX r a Hr Ha) as [Hp|Hg]; [left; apply pclMA_pclFA_callee; [exact Hav | exact Htp | exact Hp] | right; exact Hg]. }
        split; [|split; [intros jj Hjj | intros jj o' Hjj]].
        -- assert (NRS : ~ in_ranges rho R (Z_to_bv 64 (Sh a))).
           { intros Hin. apply (RNOTSH _ Hin). rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia]. }
           rewrite shadow_addr_Sh. rewrite (HKc1 (Sh a)); [| unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia |].
           ++ apply rm_absorb_out. exact NRS.
           ++ right. split; [exact PS|]. rewrite rm_absorb_out by exact NRS. rewrite <- shadow_addr_Sh.
              exact (smatchA_X_defined segs rho tp Cl _ r a Hsm (HbC HbaseC) (HXk' r Hr) Ha).
        -- intros Hdef. rewrite <- EW in Hdef |- *.
           apply (HKc2 (Sh a) jj); [unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia | exact PS | exact Hjj |].
           rewrite rm_absorb_out; [exact Hdef|]. intros Hin. apply (RNOTSH _ Hin). apply word_byte_of_shadow; [exact HSa | exact Hjj].
        -- intros Hin' Hrng. destruct (NEWOBJ o' Hin') as (p & n' & Elo & [Hemp|(Ehi & HinN & HninF & Hn')]); [lia|].
           pose proof (word_byte_of_shadow (Sh a) jj HSa Hjj) as WS. rewrite EW in WS.

           eapply (client_not_shadow segs AInv CST ALA HCST A'); [exact HM' | | exact WS]. left; right; left. exists p, n'. split; [exact HinN | lia].
    +
      intros rho' Hlink.
      assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by (destruct Hlink as (A & _); exact A).
      set (rho'' := rho_patch rho' (patchf rho rho' R)).
      assert (Hag'' : agree_vals (ss_next (ax_S Cl)) rho rho'') by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      pose proof Hlink as (L1 & L2 & L3 & L4).
      assert (EI : forall e, sv_vars_all (ivar_ok NPc s (ss_next (ax_S Cl)) (ax_S Ld)) e = true -> eval rho'' (sv_subst (import_subA s PreC Ld Cl) e) = eval rhoL e).
      { intros e Hev. subst rho''. rewrite eval_patch, eval_subst. symmetry.
        apply (eval_agree_vars (ivar_ok NPc s (ss_next (ax_S Cl)) (ax_S Ld)) rhoL (rho_sub rho' (import_subA s PreC Ld Cl)) e); [| |exact Hev].
        - intros u Hu. unfold ivar_ok in Hu. apply andb_prop in Hu as [Hu1 Hu2]. apply Pos.ltb_lt in Hu2.
          cbn [rho_sub rw]. unfold import_subA. apply L4; [rewrite HnextPre; exact Hu1 | lia].
        - intros l. cbn [rho_sub rl]. rewrite <- (proj2 L3 l). cbn [rho_sub rho_absorb rl]. exact (proj2 L1 l). }
      assert (KEPT : keptK rho kept fr rho'').
      { intros a Ha Hp. subst rho''. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [reflexivity|]. rewrite L2.
        rewrite (HKc1 a Ha (or_introl (pclMA_pclFA_callee s rho R (vms md tp ms) _ _ a Hav Htp Hp))). apply rm_absorb_out. exact Hn'. }
      assert (PSI : psiK PsiL Cl s R Ld rho rho'').
      { exists (rho_sub (rho_absorb rho R (vms md tp ms)) s), rhoL. split; [exact HPSI|]. split; [|split; [|exact EI]].
        - intros e. rewrite EVA. symmetry. apply eval_subst.
        - intros a Hn'. split; [apply rm_absorb_out; exact Hn'|]. subst rho''. cbn [rho_patch rm]. unfold patchf.
          destruct (in_ranges_dec rho R a) as [Hi|Hn2]; [exfalso; exact (Hn' Hi) | apply L2]. }
      eapply TR_pre; [ | apply (Tcont (Ld, ndL, PsiL) rho'' tpL Hd Hag'' KEPT PSI)].
      intros w [Hsm' HJ']. cbn [J_ofPA fst snd] in HJ' |- *. unfold JLAP in HJ'. destruct HJ' as [HJ' _].
      destruct HJ' as (Hk2 & A2 & kc2 & HM2 & HT2 & HB2 & HFF2 & (HN2 & HD2 & HZ2) & HFR2 & [HK21 HK22] & _ & HXA2 & HBU2 & HPAc2 & HCK2 & HCN2).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      assert (Hnbk : tv_below (ss_next (ax_S Cl)) kept = true).
      { unfold tv_below in *. rewrite forallb_app in Hbt. apply andb_prop in Hbt as [A _]. exact A. }
      set (isub := import_subA s PreC Ld Cl) in *.
      assert (IM : map (tvv rho'') (import_tv isub (nd_tv ndL)) = map (tvv rhoL) (nd_tv ndL)
                   /\ forall k t t', nth_error (nd_tv ndL) k = Some t -> nth_error (import_tv isub (nd_tv ndL)) k = Some t' -> (tnz rho'' t' <-> tnz rhoL t)).
      { unfold tvL_ok in HtvL. revert HtvL. clear - EI. generalize (nd_tv ndL) as tvL. intros tvL HtvL.
        induction tvL as [|t r IH]; [split; [reflexivity | intros [|k] ? ? H; discriminate]|].
        cbn in HtvL. apply andb_prop in HtvL as [Ht Hr]. apply andb_prop in Ht as [Ht1 Ht2]. destruct (IH Hr) as [IH1 IH2].
        split.
        - cbn [map import_tv]. f_equal; [|exact IH1]. unfold tvv. cbn [fst snd]. rewrite (EI _ Ht1), (EI _ Ht2). reflexivity.
        - intros [|k] a b Ha Hb; cbn in Ha, Hb; [|exact (IH2 k a b Ha Hb)].
          injection Ha as <-. injection Hb as <-. unfold tnz. cbn [fst]. rewrite (EI _ Ht1). tauto. }
      destruct IM as [IM1 IM2].
      assert (IB : bsumV (bd_subst isub (nd_bd ndL)) rho'' = bsumV (nd_bd ndL) rhoL /\ bsumK (bd_subst isub (nd_bd ndL)) rho'' = bsumK (nd_bd ndL) rhoL).
      { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.bdL_ok in HbdL. exact (bsum_vars_ext _ _ _ _ _ HbdL EI). }
      destruct IB as [IB1 IB2].
      split; [exact (cont_smatchA3 segs Cl PreC _ s R Xk rho rho' tp tpL tr ms md _ He Hsm Hag' Hsm')|].
      exists A2, kc2.
      pose proof (proj1 (TPA_calleeA A2 s rho R (vms md tp ms) Hav Htp) HT2) as HT2'.
      assert (HsubR : forall a, in_ranges rho R a -> cmaddrA CST A2 None (bv_unsigned a)).
      { intros a (o & Ho & Hr). eapply pclMA_cmaddrA; [exact HB2 | exact HFF2 | exact HT2' | exact (HRok o _ Ho Hr)]. }

      assert (EAM2 : am_eval rho'' (am_subst isub (nd_am ndL)) = am_eval rhoL (nd_am ndL)).
      { rewrite am_subst_as_map. apply (am_eval_ext (sv_subst isub)). intros e Hine. apply EI. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.amL_ok in HamL. exact (proj1 (forallb_forall _ _) HamL e Hine). }
      assert (TVK : tvals rho'' kept = tvals rho kept).
      { unfold tvals. apply map_ext_in. intros t Ht. apply (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag''). exact (proj1 (forallb_forall _ _) Hnbk t Ht). }
      destruct (XAz_transport (FBx FB rho kept) FB (am_eval rhoL (nd_am ndL)) A2 A2 (rm rhoL) (rm rho'') (tvals rhoL (nd_tv ndL)) (tvals rho kept ++ tvals rhoL (nd_tv ndL)) kc2 HXA2) as [XIMP PIMP].
      { intros b n H1 H2 H3. split; [exact H1|]. split; [intros Hin; apply H2; apply In_FBx; left; exact Hin|].
        intros v Hv Hnz. apply in_app_or in Hv as [Hv|Hv]; [|exact (H3 v Hv Hnz)].
        unfold tvals in Hv. apply in_map_iff in Hv as (t & <- & Ht). intros Heq. apply H2. apply In_FBx. right. exists t. auto. }
      { intros b n z H1 H2 H3 Hz. subst rho''. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hi|Hn]; [|apply L2].
        exfalso. destruct Hi as (o & Ho & Hr).
        destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (_ & HBl2 & _). destruct (HBl2 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
        eapply (live_not_pclMA A2 _ _ _ (FBx FB rho kept) (FFx rho fr) b n z HM2 HB2 HFF2 HT2' H1 H2 Hz).
        apply (HRok o _ Ho). rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). exact Hr. }
      { intros b n a H1 H2 H3 Ha.
        destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (_ & HBl2 & _). destruct (HBl2 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
        assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
        subst rho''. cbn [rho_patch rm]. unfold patchf. split.
        - intros _. rewrite shadow_addr_Sh. destruct (in_ranges_dec rho R (Z_to_bv 64 (Sh a))) as [Hi|Hn]; [|apply L2].
          exfalso. apply (RNOTSH _ Hi). rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia].
        - intros j Hj Hdef. replace (SHADOW_OFF + a / 8) with (Sh a) in * by (unfold Sh; lia).
          destruct (in_ranges_dec rho R (word_byte (Sh a) j)) as [Hi|Hn]; [|rewrite L2; exact Hdef].
          exfalso. apply (RNOTSH _ Hi). apply word_byte_of_shadow; [exact HSa | exact Hj]. }
      {
        intros bn H1 _ H3 H4. split; [exact H1|]. split.
        - intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnz & Heq)]; [exact (H3 Hin)|].
          apply (H4 (tvv rho t)); [apply in_or_app; left; unfold tvals; apply in_map; exact Ht | exact Hnz | exact Heq].
        - intros v Hv Hnz. apply H4; [apply in_or_app; right; exact Hv | exact Hnz]. }
      split; [|split; [exact Hk2|split; [|split; [|split; [|split; [|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [cbn [nd_am nd_tv]; unfold XA; rewrite EAM2; unfold tvals in TVK, XIMP |- *; rewrite map_app, IM1, TVK; exact XIMP|split; [|split; [exact (HPAc _ _ HPA HPAc2) | split; [exact HCK2|

      unfold capN in *; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.BXx in HCN2; cbn [bxN nd_tv] in HCN2 |- *; rewrite cntS_app, (cntS_map _ _ _ _ IM1);
      unfold cntS at 1; rewrite TVK; fold (cntS rho kept); lia]]]]]]]]]]]]]].
      * eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hnf | exact Hag''].
      *
        assert (HM2' : AInv A2 (mkVal (rw rho') (rl rho') (rm rhoL)) tpL mdw).
        { eapply (law_vars _ _ _ ALA); [exact HM2 | reflexivity]. }
        eapply (law_frame _ _ _ ALA); [exact HM2'| |].
        -- intros a Hnm _. subst rho''. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|apply L2].
           exfalso. apply Hnm. eapply cmaddrA_mut. exact (HsubR a Hi).
        -- intros a Hsh Hdef. subst rho''. cbn [rho_patch rm] in *. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|rewrite L2; exact Hdef].
           exfalso. apply (RNOTSH a Hi). destruct Hsh as (f & sz & Hin & Hr).
           destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2') as (_ & _ & HFr2). destruct (HFr2 f sz Hin) as (_ & _ & G64 & Ghs & Gce & _).
           top_rng Gce.
           pose proof (Sh_is_shadow f ltac:(unfold IMG_HI in Ghs; lia)) as S1.
           pose proof (Sh_is_shadow (f + sz - 1) ltac:(unfold IMG_HI in Ghs; lia)) as S2.
           unfold is_shadowZ in *. lia.
      *   exact HT2'.
      * intros bn Hbn. apply HB2. apply In_FBx. left. exact Hbn.
      * intros f sz fl Hin. apply HFF2. apply In_FFx. left. exact Hin.
      *
        unfold tvinA. apply Forall_app. split.
        -- apply Forall_forall. intros t Ht Hnz.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt0.
           rewrite (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0) in *. apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0)) in Hnz.
           destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [|exact X2]. apply HB2. apply In_FBx. right. exists t. auto.
        -- eapply tvinA_map; [exact IM1 | exact IM2 |].
           unfold tvinA in HN2 |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN2 t Ht Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [exact X1|]. intros Hin. apply X2. apply In_FBx. left. exact Hin.
      *
        apply tvd_app.
        -- apply (tvd_agree (ss_next (ax_S Cl)) rho rho'' kept Hag'' Hnbk). exact (tvd_app_l rho kept passed HD).
        -- eapply tvd_map; [exact IM1 | exact IM2 | exact HD2].
        -- intros t t' Ht Ht' Hnz Hnz' Heq.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt0.
           rewrite (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0) in Heq. apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0)) in Hnz.
           destruct (In_nth_error _ _ Ht') as [k Hk'].
           assert (exists t0, nth_error (nd_tv ndL) k = Some t0) as [t0 Ht0].
           { pose proof (Forall2_map_eq _ _ _ _ IM1) as L. destruct (nth_error (nd_tv ndL) k) eqn:En; [eexists; reflexivity|].
             exfalso. apply nth_error_None in En. assert (k < length (import_tv isub (nd_tv ndL)))%nat by (apply nth_error_Some; congruence). lia. }
           rewrite (map_nth2 _ _ _ _ k t0 t' IM1 Ht0 Hk') in Heq. apply (proj1 (IM2 k t0 t' Ht0 Hk')) in Hnz'.
           destruct (proj1 (Forall_forall _ _) HN2 t0 (nth_error_In _ _ Ht0) Hnz') as (_ & _ & X2).
           apply X2. apply In_FBx. right. exists t. auto.
      *
        unfold tvz. apply Forall_app. split.
        -- apply (tvz_agree (ss_next (ax_S Cl)) rho rho'' kept Hag'' Hnbk). unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
        -- eapply tvz_map; [exact IM1 | exact IM2 | exact HZ2].
      *
        eapply frinA_agree; [exact Hag'' | exact Hbf |]. destruct HFR as [HFR HCEN]. split.
        -- unfold frinA0 in HFR |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFR x Hx) as (X1 & X2 & X3).
           destruct (HFF2 (fst (frv rho x)) (snd (frv rho x)) (uval rho (snd x)) ltac:(apply In_FFx; right; exists x; auto)) as [Y1 Y2].
           rewrite <- surjective_pairing in Y1, Y2. auto.
        -- destruct HCEN as [HCEN HND]. split; [| exact HND].
           intros x Hx. destruct HFR2 as [_ [HC2 _]]. destruct (HC2 x Hx) as [(fl & Hin)|Hin2].
           2: { exfalso. revert Hin2 HfrL. clear. destruct (nd_fr ndL); [intros [] | intros _ H; discriminate H]. }
           apply In_FFx in Hin as [Hin|(y & Hy & Ey)]; [left; exists fl; exact Hin | right].
           apply in_map_iff. exists y. split; [|exact Hy]. injection Ey as E1 E2 E3. destruct x as [x1 x2]. cbn [fst snd] in E1, E2. subst x1 x2.
           symmetry. apply surjective_pairing.
      *
        pose proof (T0_calleeA s rho R (vms md tp ms) Hav Htp) as ET0.
        split.
        -- intros a Ha Hp. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply (proj1 HK0); assumption|].
           rewrite L2. transitivity (rm (rho_sub (rho_absorb rho R (vms md tp ms)) s) (Z_to_bv 64 a)).
           ++ pose proof Hp as Hp0. apply HKc1; [exact Ha|]. destruct Hp as [Hp|[Hs0 Hd0]].
              ** left. destruct Hp as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
                 { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
                 { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
              ** right. split; [|rewrite rm_absorb_out by exact Hn'; rewrite (proj1 HK0 _ Ha Hp0); exact Hd0].
                 destruct Hs0 as (y & Hy & Hpy & ->). exists y. split; [exact Hy|]. split; [|reflexivity].
                 destruct Hpy as [Hpy|Hg]; [left|right; exact Hg].
                 destruct Hpy as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
                 { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
                 { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
           ++ rewrite rm_absorb_out by exact Hn'. apply (proj1 HK0); assumption.
        -- intros a jj Ha Hp Hjj Hdef. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct Hp as (y & Hy & Hpy & ->).
           assert (Hy47 : 0 <= y < 2 ^ 47).
           { destruct Hpy as [Hpy|Hg]; [exact (pclFA_range segs AInv CST ALA HCST _ _ _ Ai rho tp md y HM HB HFF HT Hpy)|]. apply HXGL in Hg. unfold IMG_HI, LOW_SHADOW_BEG in Hg. lia. }
           assert (NW : ~ in_ranges rho R (word_byte (Sh y) jj)).
           { intros Hin. apply (RNOTSH _ Hin). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Hy47 | exact Hjj]. }
           destruct (in_ranges_dec rho R (word_byte (Sh y) jj)) as [Hi|Hn']; [exfalso; exact (NW Hi)|].
           rewrite L2. apply (HKc2 (Sh y) jj); [pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia | | exact Hjj |].
           ++ exists y. split; [lia|]. split; [|reflexivity]. destruct Hpy as [Hpy|Hg]; [left|right; exact Hg].
              destruct Hpy as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
              { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
              { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
           ++ rewrite rm_absorb_out by exact Hn'. apply (proj2 HK0); try assumption. exists y. auto.
      *
        destruct (BUD_splitF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S Cl)) bd (bd_subst s (nd_bd ndC)) brest _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF (conj HP0 Hav) HPAY HBU) as [_ Nr].
        pose proof HBU as (BX1 & BX2 & _). unfold bxa in BX1, BX2. cbn [fst snd] in BX1, BX2.
        pose proof (apot_range am rho) as [PR1 PR2]. pose proof (XA_kc_nonneg FB _ _ _ _ _ HXA) as KC0.
        pose proof (apot_range (nd_am ndL) rhoL) as [PR3 PR4]. pose proof (XAz_kc_nonneg _ _ _ _ _ _ HXA2) as KC2.
        assert (EP2 : apot (am_subst isub (nd_am ndL)) rho'' = apot (nd_am ndL) rhoL) by (unfold apot; rewrite EAM2; exact PIMP).
        cbn [nd_am nd_bd]. rewrite EP2.
        apply (BUD_join (bd_subst isub (nd_bd ndL)) brest _ (aa_V A2) (aa_Km A2) (aa_Kf A2) rho rho'').
        -- unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.BXx, bxa, bxV, bxK in HBU2. cbn [bx2] in HBU2. pose proof (bsum_nonneg brest rho (proj1 Nr) (proj2 Nr)) as [BN1 BN2].
           rewrite (Z.max_r 0 (bsumV brest rho)) in HBU2 by lia. rewrite (Z.max_r 0 (bsumK brest rho)) in HBU2 by lia.
           unfold BUD in HBU2 |- *. unfold bxa. cbn [fst snd] in HBU2 |- *. rewrite IB1, IB2, bd_wpos_subst.
           destruct HBU2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
           split; [lia|]. split; [lia|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
           split; [|split; lia].
           unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.bdL_ok in HbdL. exact (bd_nn_vars_ext _ _ _ _ _ HbdL EI Q7).
        -- symmetry. symmetry. apply (bsumV_agree (ss_next (ax_S Cl))); [exact Hag'' | exact Hbr].
        -- apply (bsumK_agree (ss_next (ax_S Cl))); [exact Hag'' | exact Hbr].
        -- exact (proj1 Nr).
        -- eapply bd_nn_agree; [exact Hag'' | exact Hbr | exact (proj2 Nr)].
        -- unfold bxa. cbn [fst snd]. pose proof (BXok_d_pair _ BX HBX) as [HX1 HX2]. lia.
        -- unfold bxa. cbn [fst snd]. pose proof (BXok_d_pair _ BX HBX) as [HX1 HX2]. lia.
Qed.
End CallTCk.

Hypothesis SUM : ltac2:(tb__ "0|1|
S43OF_;S5S8S24S24A2M0A1S5S8G0S24A2A1S56S18S5S46Q40A1A1S32Vsegs;VKc;R6A3S59VdC;R4A2S45Vsegs;R8S26Vsegs;S30VAInv;VCST;VXGL;VKc;VP0c;R7R6A2R7R6R5VPAc;VndC;AaVPreC;R4R3A5S70Vsegs;VNPc;R4R3S9dR7R6R5A3A5A4F_;F_;Ftp1;Frho1;FBXc;FFFc;FFBc;Fok;").
Hypothesis SUMX : ltac2:(tb__ "0|1|
S5S8S24S24A2M0A1S5S8G0S24A2A1S56S18S5S46Q40A1A1S59VdC;R3A2S44Vsegs;S26Vsegs;S30VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S70Vsegs;VNPc;R3R2S9dR6R5R4A3A5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis HddA : ltac2:(tb__ "0|1|
S0S6S13S8dZ1M0VdC;A2S8dS8fVdC;G0A2VdF;A2A2S7A3").

Theorem client_callA_k : ltac2:(tb__ "0|e|
S43OF_;S15S4bS5S1cA1M0S5S8S1aS1aA2M1A1M2S18S5S46Q40A1A1M3G2G2S5S8S8S1aS24A2S1aA2A1S5S53A1M4G4S35S42S32Vsegs;VKc;ReA3S0S6S80RbS16ReA1A2S7A3S0SdG0A1S73RfVPreC;ReA3ScG0RdA2A3S0S6S72R10VPreC;RfReS8aS8S8S15S29A2M5S18S18OF_;F_;M6A2M7S15G7S9S15S29S9G5G6R1A3A3Ld;VPD;A4A5S7A3S0S6S85VNP;R10A2S7A3S0S6S50R11VNPc;A2S7A3S0S6S88VNP;S19S14R13A1A1A2S7A3S0S6S2eS19S14R14A1A1S2bSaG1ReRdA3RcRbR9A4A2S7A3S0S6S55S19S14R15A1A1RbA2S7A3S0S6S98R15RfS2aVndC;A1A3S7A3S0S6S34S31R16S2cVndC;A1A2RcA2S7A3VpayA;S1bS14R18A1A1S1fZ0M8A1G8RfSaS53S58R17S2dVndC;A1A2ReA3A5S0S6S78S8S7aG6A2M9G9S7eVPreC;VNPc;R19S19S14R1aA1A1S9S7aG6R1A3A5Ld;VPD;A3S7A3S3dS6dS89S1dS21R18A1S1bS14R1cA1A1A3VP0f;Vrho0;A1S4eVNP;Vrho0;R1aA3S36VFB;R5A2S37VFF;R6A2S39VFB;R7R1dSaG1R1bR1aA3A4S99R1eSaG1R1cR1bA3A2S9aR1fSaG1R1dR1cA3A2S38VFF;RaR20R1cA4S2S18S18S2G3G3S2S6eS6eVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S33Vrho0;RcA2S96R23S41S3eRdA1A1A2S1S7fVCST;Vrho0;VFB;VFF;R24R22R20R26A8S1S81VCST;VXGL;Vrho0;VFB;VFF;R24R22R20R25A9VP0c;S93VFB;R24R22A3S7bVFF;R24R20A3S4aS49R24R26RdA3R27A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S9cS18G3S77S9cR3VPD;A3S4eS19S14R1fA1A1R1bR3A3S9eR1cR1aR18R4A4S9fSfG5G6R6A3R21R20R1fS9S15S29S9G5G6R6A3A3R1dR5A7S45Vsegs;R23S26Vsegs;VJA;S2bSaG1R1cS97S74R21VPreC;S9S15S29S9G5G6R7A3MaA3MbR22A4McS2aSfS15S29GaA3MdA1A2A3R1aSaS53S58GcS2dGdA1A2R18A3S31GcS2cGdA1A2A4A1S7dVPreC;R22R21R20GbR1fA6R6R5A5R16A4F_;F_;F_;F_;Ftp';Frho';Fd;S45Vsegs;R1dS26Vsegs;VJA;S2bSaG1R16R15A3R14R13R11A4A1R1cR18R17A5R10A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;Fok;").
Proof using ALA HCST HXGL HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUM HddA.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros ok Cl s R Xk rho tp kept passed fr bd brest am Q Hok.
  apply (client_callT_k (triple segs ok) (triple_factsA segs ok) (triple_SPA_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H) (call_soundPA3 segs ok)); [|exact HddA].
  intros FBc FFc BXc rho1 tp1 HB0. apply SUM; [exact Hok | exact HB0].
Qed.

Theorem client_callA_ex_k : ltac2:(tb__ "0|e|
S15S4bS5S1cA1M0S5S8S1aS1aA2M1A1M2S18S5S46Q40A1A1M3G2G2S5S8S8S1aS24A2S1aA2A1S5S53A1M4G4S35S42S0S6S80RaS16RdA1A2S7A3S0SdG0A1S73ReVPreC;RdA3ScG0RcA2A3S0S6S72RfVPreC;ReRdS8aS8S8S15S29A2M5S18S18OF_;F_;M6A2M7S15G7S9S15S29S9G5G6R1A3A3Ld;VPD;A4A5S7A3S0S6S85VNP;RfA2S7A3S0S6S50R10VNPc;A2S7A3S0S6S88VNP;S19S14R12A1A1A2S7A3S0S6S2eS19S14R13A1A1S2bSaG1RdRcA3RbRaR8A4A2S7A3S0S6S55S19S14R14A1A1RaA2S7A3S0S6S98R14ReS2aVndC;A1A3S7A3S0S6S34S31R15S2cVndC;A1A2RbA2S7A3VpayA;S1bS14R17A1A1S1fZ0M8A1G8ReSaS53S58R16S2dVndC;A1A2RdA3A5S0S6S78S8S7aG6A2M9G9S7eVPreC;VNPc;R18S19S14R19A1A1S9S7aG6R1A3A5Ld;VPD;A3S7A3S3dS6dS89S1dS21R17A1S1bS14R1bA1A1A3VP0f;Vrho0;A1S4eVNP;Vrho0;R19A3S36VFB;R5A2S37VFF;R6A2S39VFB;R7R1cSaG1R1aR19A3A4S99R1dSaG1R1bR1aA3A2S9aR1eSaG1R1cR1bA3A2S38VFF;RaR1fR1bA4S2S18S18S2G3G3S2S6eS6eVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S33Vrho0;RcA2S96R22S41S3eRdA1A1A2S1S7fVCST;Vrho0;VFB;VFF;R23R21R1fR25A8S1S81VCST;VXGL;Vrho0;VFB;VFF;R23R21R1fR24A9VP0c;S93VFB;R23R21A3S7bVFF;R23R1fA3S4aS49R23R25RdA3R26A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S9cS18G3S77S9cR3VPD;A3S4eS19S14R1eA1A1R1aR3A3S9eR1bR19R17R4A4S9fSfG5G6R6A3R20R1fR1eS9S15S29S9G5G6R6A3A3R1cR5A7S44Vsegs;S26Vsegs;VJA;S2bSaG1R1bS97S74R20VPreC;S9S15S29S9G5G6R7A3MaA3MbR21A4McS2aSfS15S29GaA3MdA1A2A3R19SaS53S58GcS2dGdA1A2R17A3S31GcS2cGdA1A2A4A1S7dVPreC;R21R20R1fGbR1eA6R6R5A5R15A3F_;F_;F_;F_;Ftp';Frho';Fd;S44Vsegs;S26Vsegs;VJA;S2bSaG1R15R14A3R13R12R10A4A1R1bR17R16A5RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;").
Proof using ALA HCST HXGL HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUMX HddA.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros Cl s R Xk rho tp kept passed fr bd brest am Q.
  apply (client_callT_k (etriple segs) (etriple_factsA segs) (etriple_SPA_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H) (call_completePA3 segs)); [|exact HddA].
  intros FBc FFc BXc rho1 tp1 HB0. apply SUMX. exact HB0.
Qed.

End Client.

Definition liftPD (PD0 : list pdescA) : list pdescK := ltac2:(tb__ "0|2|
S8aS8S15S29A2M0S8G0S18S18OF_;F_;M1A2G0SbG0G1SbS15S29S9S15S29R1A3SfS15S29R1A3A4S18S18S3L_;L_;A4Ld;VPD0;A4").

Lemma LQPA_PostsC_k : ltac2:(tb__ "0|3|
S62S5S8S24S24A2M0A1M1S5S8G0S24A2A1M2S18OF_;F_;F_;S3dOF_;S5S7aA1S25G1G2S56S18S5S46Q40A1A1S43S70Vsegs;R7R3R2S7cVAInv;VCST;VXGL;RbRaR9R8R6R5R4AaR1A6S70Vsegs;R8R4R3Sa0RcRbRaSa1R9A1R7R6R5A7R2A6F_;Fw;Ftp1;Frho1;FBXc;FFFc;FFBc;FNPc;FPD0;FPAc;FP0c;FKc;").
Proof using .
  intros Kc P0c PAc PD0 NPc FBc FFc BXc rho1 tp1 w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PostsC in Hin. apply in_map_iff in Hin as (d & Heq & Hd). injection Heq as E1 E2. subst L JL.
  exists (fst d), (JLAP AInv CST XGL Kc (P0c FBc FFc) FBc FFc BXc PAc (snd d) (fun _ _ => True)), rho', tp'.
  split; [|split; [exact Hag | split; [exact Hsm | split; [exact HJL | exact I]]]].
  unfold PostsCk, liftPD. rewrite map_map. apply in_map_iff. exists d. split; [reflexivity | exact Hd].
Qed.

Lemma sum_PostsC_k {d : Z} : ltac2:(tb__ "0|6|
S62S5S8S24S24A2M0A1M1S5S8G0S24A2A1M2S18OF_;Fx0;Fx;S3dOF_;S15S29S5S7aA1S25S43OF_;M3G1G2S56S18S5S46Q40A1A1M4S32Vsegs;RdR6A3S59Vd;R4A2M5S45Vsegs;R8S26Vsegs;S30VAInv;VCST;VXGL;RfReR7R6A2R7R6R5RdRbAaRcR4R3A5S70Vsegs;R9R4R3S7cVAInv;VCST;VXGL;RfReRdRaR7R6R5AaA5A4F_;F_;Ftp1;Frho1;FBXc;FFFc;FFBc;Fok;G3G1G2S56S18G4S32Vsegs;ReR6A3G5S45Vsegs;R8S26Vsegs;S30VAInv;VCST;VXGL;R10RfR7R6A2R7R6R5ReRcAaRdR4R3A5S70Vsegs;RaR4R3Sa0R10RfReSa1RbA1R7R6R5A7A5A4F_;F_;Ftp1;Frho1;FBXc;FFFc;FFBc;Fok;F_;FNPc;FPD0;FndC;FPreC;FPAc;FP0c;FKc;").
Proof using .
  intros Kc P0c PAc PreC ndC PD0 NPc SUM ok FBc FFc BXc rho1 tp1 Hok HB.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (LQPA_PostsC_k _ _ _ _ _ _ _ _ _ _ w Hw) | exact (SUM ok FBc FFc BXc rho1 tp1 Hok HB)].
Qed.
Lemma sum_PostsC_k_ex {d : Z} : ltac2:(tb__ "0|5|
S62S5S8S24S24A2M0A1M1S5S8G0S24A2A1M2S18OF_;Fx0;Fx;S3dOF_;S15S29S5S7aA1S25G1G2S56S18S5S46Q40A1A1M3S59Vd;R3A2M4S44Vsegs;S26Vsegs;S30VAInv;VCST;VXGL;RdRcR6R5A2R6R5R4RbR9AaRaR3R2A5S70Vsegs;R7R3R2S7cVAInv;VCST;VXGL;RdRcRbR8R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;G1G2S56S18G3G4S44Vsegs;S26Vsegs;S30VAInv;VCST;VXGL;ReRdR6R5A2R6R5R4RcRaAaRbR3R2A5S70Vsegs;R8R3R2Sa0ReRdRcSa1R9A1R6R5R4A7A5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;F_;FNPc;FPD0;FndC;FPreC;FPAc;FP0c;FKc;").
Proof using .
  intros Kc P0c PAc PreC ndC PD0 NPc SUM FBc FFc BXc rho1 tp1 HB.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (LQPA_PostsC_k _ _ _ _ _ _ _ _ _ _ w Hw) | exact (SUM FBc FFc BXc rho1 tp1 HB)].
Qed.

Section Rt.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S8S8S24S24A2S24A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.

Let JAi : ltac2:(tb__ "0|0|
S29S3dS24S27Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S3bVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S29S27Fnd;") := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S29S3dS27FAi;Fnd;") := ltac2:(tb__ "0|0|
S3cVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Local Abbreviation AInv_absorb := (TobjJAM.AInv_absorb segs AInv CST ALA HCST).
Local Abbreviation KEPT_stepA := (TobjJAM.KEPT_stepA segs AInv CST XGL ALA).
Local Abbreviation T_of_chkA := (TobjJAM.T_of_chkA NP rho0).
Local Abbreviation call_checkTA := (TobjJAM.call_checkTA NP).
Local Abbreviation caller_X_kept := (TobjJAM.caller_X_kept segs AInv CST XGL ALA HCST HXGL).
Local Abbreviation client_not_shadow := (TobjJAM.client_not_shadow segs AInv CST ALA HCST).
Local Abbreviation cmaddrA := (TobjJAM.cmaddrA CST).
Local Abbreviation cont_JAi := (TobjJAM.cont_JAi segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA).
Local Abbreviation cont_smatchA := (TobjJAM.cont_smatchA segs).
Let payA : ltac2:(tb__ "0|1|
S5S1dA1S1aS24S5S53A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S87VNP;Vrho0;VP0f;A3").
Local Abbreviation robjs_okA_weaken := (TobjJAM.robjs_okA_weaken CST).
Local Abbreviation shadow_not_in_R := (TobjJAM.shadow_not_in_R segs AInv CST ALA HCST).
Local Abbreviation site_okA := (TobjJAM.site_okA AInv CST XGL NP rho0 P0f FB FF).
Local Abbreviation top_of_TPA := (TobjJAM.top_of_TPA NP rho0).
Local Abbreviation tp_of_TPA := (TobjJAM.tp_of_TPA NP rho0).
Local Abbreviation xrs_range := (TobjJAM.xrs_range segs AInv CST XGL ALA HCST HXGL).
Local Abbreviation live2_kept := (TobjJAM.live2_kept segs AInv CST XGL ALA HCST).

Ltac chain_same_tv Hlink Hnb :=
  cbn zeta; intros ? ? _ _ Hut;
  eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).

Definition keptR (rho : valuation) (tv : list (sv * sv)) (rho' : valuation) : Prop := ltac2:(tb__ "0|4|
S8S1aS1aA2M0S24S77G0R2Vtv;A3S94Vrho;R3A2S1S8bS9S24S24S95Vrho;R4A2M1A3M2R3A2S8cR3S8fG2SfS24S24G1A3A2A2A2S0SdS46Q8A1A1S1eVrho';S47Q40R4A2M3A2S1eVrho;G3A2A3F_;F_;F_;Fz;Ft;").

Section CallTK.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27S15S18S5S46Q40A1A1S42S89S1dS21R3A1S1bS14R4A1A1A3VTR;S26Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S42S42S42S43R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27S15S15S4bS5S1cA1M0S5S8S15S71A2M1A1S5S8S1aS1aA2M2A1S42S18S5S46Q40A1A1M3G2S77G2R1R5A3S77G2R2S16RbA1A3F_;Fr;S0SdG0A1S73RaR9R8A3ScG0R7A2A3S0S6S72RbRaR9R8S8aG1S15S9S15S71A2R7A4A5S7A3S18G3VTR;S26Vsegs;RfRdR2R1A5S70Vsegs;S19S14RdA1A1R2R1RaA5A2Ftp1;Frho1;S5S6fA1M4S6dS6eS28Vsegs;R9R8R10SbG4S90R3S91R2R1A2A4A5R13RaR9R4R2A4R13S4aS49RbRfS76R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S15S71G4S6dS6eS18G3G4S6dS6eS77G1SbS15S71RaR9A4R14A3S28Vsegs;R12R11R19SbG4S90R9S91R8R7A2A4A5R1cR13R12RaR8A4S4eS19S14R1aA1A1S4aS49R14R18S76R9R13RaA3A3R19A2R8A3S28Vsegs;R9R8ReSbG4S90R7S91R6R5A2A4A5ReS4aS49R16R1aS76RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sa3R17S76RcR16RdA3R1bR1cR1dR10R1eR19RbA9S18S51R18S76RdR17ReA3R1cR1dS14R1eA1S14R1fA1S14R11A1R1RcA9VTR;S26Vsegs;S75R11S4aS49R19R1dS76ReR18RfA3A3R1eA2R18RdRcA5Sa4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Theorem malloc_callT_k : ltac2:(tb__ "0|6|
S5S5fA1S61S15S4bS5S1cA1M0S18S5S46Q40A1A1M1S29S5S53A1S42S3dS18G1VTR;S26Vsegs;S69VAInv;RdRcR3VKc;S20PcM2A1A6S5aVE;RdRcA3R2R1A5S70Vsegs;Sa2R2R1S6bVE;VAInv;VCST;VXGL;RdRcR3VKc;A8A5A2Ftp1;Frho1;FAi;S0SdG0A1S73R9S5aVE;RbRaA3R8A3ScG0R7A2A3S0S6S72RaS5aVE;RcRbA3R9R8SeS15S5eVE;RcRbA3SeS15S5cVE;RcRbA3S10S15A1A3A3A5S7A3S0S6S85VNP;RaA2S7A3S0S6S88VNP;S19S14RcA1A1A2S7A3S0S6S2eS19S14RdA1A1R8A2S7A3S0S6S55S19S14ReA1A1R8A2S7A3S0S6S23S19S14RfA1A1S48ReG2A2A2S7A3S0S1aS48S74RfS5aVE;R12R11A3S5cVE;R12R11A3R10A4S63A2S20S4fS19S14R10A1A1UaM3A2A1A3VpayA;S1bS14R11A1A1S48R10G2A2S57S2dRcA1RbA5S3dS3dVPA;R2A1S3fR3R2S54R12S48R14G2A2A2M4A3VPA;R3A1F_;F_;FA';FA;S86VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R13R12R11R10ReS11S24A1S3dS6dS1S1S8bZ1G4A2S8cG4S8eZ2Z27A2A2A2S60R17R16S4aS49R12R13R1A3R14A2A3A2Lms;LAi;AfS18G1S4eS19S14R16A1A1R13R2A3S83R14S2aR12A1R3A3VTR;S26Vsegs;VJA;S2bS2aR13A1M5S2fR13A1R12S2cR13A1A4A1S84S5aVE;R1aR19A3R18R17R16S5eVE;R1aR19A3A5R4R3A5R11A2F_;F_;Ftp';Frho';S18G1S4eS19S14R17A1A1R14R2A3S83R15G5R3A3VTR;S26Vsegs;VJA;S2bSeS8S1aS1aA2SbS1aS1aS20S4fS19S14R19A1A1G3A2A1S48R18G2A2A4S2aR14A1A3S2fR14A1R13S2cR14A1A4A1S84S5aVE;R1bR1aA3R19R18R17S5cVE;R1bR1aA3A5R4R3A5R12A2F_;F_;Ftp';Frho';VTR;S26Vsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre HBX.
  intros W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HSITE Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (J_alloc_pre AInv W st Ai Kc (SVar 12)) Cl (Pre_malloc E W st) s R
            (Posts_malloc E AInv CST XGL W st Ai Kc) (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & HU).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|]. split; [exact HU|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    cbn [eval]. rewrite rw_call'. split; [|split; [exact Hn | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)]].
    pose proof (bv_urange (eval rho (wsub_get s 12))) as HR12. unfold uval in P1.
    apply budget_ok_alloc_intro; [eapply (BUD_limit_ok_alloc (nd_bd nd) _); [exact HBU | lia | lia | lia] | | exact (TobjJAM.prim_room_JA BX _ _ nd Ai rho HBX HCNi Hnb)].
    exact (TobjJAM.sec_room_JA BX _ _ _ Ai rho (BXok_d_ok _ _ HBX) HCKi (proj1 (proj1 (apot_range (nd_am nd) rho))) ltac:(eapply XA_kc_nonneg; exact HXA) HBU).
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    set (n := uval rho (wsub_get s 12)) in *.
    assert (Hn12 : bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 12%positive) = n) by (subst n; rewrite rw_call'; reflexivity).
    cbn [Posts_malloc In] in HinL.
    destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A2 & HM2 & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. auto.
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
        -- intros r a j oR Hr. cbn in Hr. destruct Hr.
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
      * intros rho' Hlink.
        assert (HagP0 : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]).
        assert (KR : keptR rho (nd_tv nd) (rho_patch rho' (patchf rho rho' R))).
        { intros t0 z Ht0 Hnz0 Hz. destruct (proj1 (Forall_forall _ _) HN t0 Ht0 Hnz0) as (_ & Hl0 & _).
          exact (proj1 (live2_kept Ai A2 None rho rho' rhoL (vms md tp ms) s R tp md _ _ HM HRok Hkept2 (proj1 (proj2 Hlink)) Hl0 ltac:(rewrite HL2; exact Hl0)) z Hz). }
        eapply TR_pre; [ | apply (Tnull (rho_patch rho' (patchf rho rho' R)) tpL HagP0 KR)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A2' & HM2' & HL2' & HF2' & HV2' & HKm2' & HKf2' & HG2' & Hkept2' & Hk2' & HC2').
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_malloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A2', kc.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A2' None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL2'. auto.
          - right; right; right. exists f, sz. rewrite HF2'. auto. }
        destruct (law_budget _ _ _ ALA A2' _ _ _ HM2') as (_ & _ & HV0 & HKm0 & HKf0).
        pose proof (HPAK Ai A2' HPA ltac:(rewrite <- Hn12; exact HC2')) as HPA2.
        eapply (cont_JAi Cl (Pre_malloc E W st) (L_malloc_null E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A2' None
                  (nd_tv nd) bd' (wsub_get s 12) KU He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2' Hk2' Hsub'); try assumption.
        -- intros b Hb. rewrite HL2'. exact (HB b Hb).
        -- rewrite HV2', Hn12. unfold n. lia.
        -- rewrite HKm2', HKf2'. unfold KU. lia.
        -- assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
           { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
           destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
           cbn zeta. split; [|split].
           ++ apply (tvinA_agree FB A2' (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
              unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL2'; exact X1 | exact X2].
           ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL2'. exact Hb.
        -- chain_same_tv Hlink Hnb.
        -- cen_same_tvG Hlink Hnb HL2'.
        -- capK_sameG HCKi HL2' HV2'.
        -- capN_sameG HCNi Hlink Hnb HL2'.
    +
      destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      rewrite Hn12 in HL2.
      assert (HinNew : In (p, n) (aa_live A2)) by (rewrite HL2; apply in_or_app; right; left; reflexivity).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. split; [apply in_app_mid; rewrite <- HLi; exact Hin | auto].
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
      destruct (HBl p n HinNew) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      assert (NEWFREE : forall a, p <= a < p + n -> cmaddrA Ai None a -> False).
      { intros a Ha [Hc|[Hc|[(b & m & Hb & _ & Hr)|(f & sz & Hf & Hr)]]].
        -   rewrite <- HG2 in Hc. lia.
        - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
        - rewrite HLi in Hb. pose proof (pd_mid l1 (p, n) l2 (aa_frames A2) (b, m) ltac:(rewrite <- HL2; exact HPD) Hb) as D. cbn [fst snd] in D. lia.
        - assert (Hf2 : In (f, sz) (aa_frames A2)) by (rewrite HF2; exact Hf).
          apply In_nth_error in Hf2 as [k Hkk].
          assert (Hx : nth_error (aa_live A2 ++ aa_frames A2) (length l1) = Some (p, n)).
          { rewrite nth_error_app1 by (rewrite HL2, length_app; cbn; lia). rewrite HL2, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
          assert (Hy : nth_error (aa_live A2 ++ aa_frames A2) (length (aa_live A2) + k) = Some (f, sz)).
          { rewrite nth_error_app2 by lia. replace (length (aa_live A2) + k - length (aa_live A2))%nat with k by lia. exact Hkk. }
          pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(rewrite HL2, length_app; cbn; lia)) as D. cbn [fst snd] in D.
          destruct (HFr f sz ltac:(rewrite HF2; exact Hf)) as (_ & _ & G64 & _). lia. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        --
           intros o' oR Hin' HinR. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
           assert (Ho' : o' = block_obj (SVar 12) DUnknown).
           { cbn [ax_S L_malloc_ok Pre_malloc mkA ss_objs] in A, B0.
             apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
             apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
             apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
           subst o'. destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p. rewrite bv_signed_U, (proj1 Hag1 12%positive ltac:(cbv; lia)) || idtac.
           assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
           { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
           rewrite bv_signed_U, E12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
        --
           intros r a j oR Hr Ha Hj HoR. cbn [ax_X L_malloc_ok mkA] in Hr. destruct Hr as [<-|[]]. cbn [fst snd eval] in Ha.
           assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
           { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
           fold p in Ha. rewrite E12 in Ha.
           intros Hrng. apply (shadow_not_in_R Ai None rho tp md R (bv_unsigned (word_byte (bv_unsigned (eval rhoL (ax_base (L_malloc_ok E W st))) + a / 8) j)) HM HRok).
           ++ cbn [ax_base L_malloc_ok mkA base_sv eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
              replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; lia | exact Hj].
           ++ rewrite Z_to_bv_bv_unsigned. exists oR. split; [exact HoR | exact Hrng].
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin' w Hw. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
              assert (Ho' : o' = block_obj (SVar 12) DUnknown).
              { cbn [ax_S L_malloc_ok Pre_malloc mkA ss_objs] in A, B0.
                apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
                apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
                apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
              subst o'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
              rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
              assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
              { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
              rewrite bv_signed_U, E12.
              destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X; cbn [fst snd]; intros Hr';
                exact (client_not_shadow A2 (bv_unsigned w) rhoL tpL md' HM2 ltac:(left; right; left; exists p, n; split; [exact HinNew | lia]) Hw).
      * intros rho' Hlink.
        assert (HagP0 : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]).
        assert (KR : keptR rho (nd_tv nd) (rho_patch rho' (patchf rho rho' R))).
        { intros t0 z Ht0 Hnz0 Hz. destruct (proj1 (Forall_forall _ _) HN t0 Ht0 Hnz0) as (_ & Hl0 & _).
          refine (proj1 (live2_kept Ai A2 None rho rho' rhoL (vms md tp ms) s R tp md _ _ HM HRok Hkept2 (proj1 (proj2 Hlink)) Hl0 _) z Hz).
          rewrite HL2. apply in_app_mid. rewrite <- HLi. exact Hl0. }
        eapply TR_pre; [ | apply (Tok (rho_patch rho' (patchf rho rho' R)) tpL HagP0 KR)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_malloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A3, kc.
        rewrite Hn12 in HL3. fold p in HL3.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL3. split; [apply in_app_mid; rewrite <- HLi3; exact Hin | auto].
          - right; right; right. exists f, sz. rewrite HF3. auto. }
        destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
        destruct (law_blocks _ _ _ ALA A3 _ _ _ HM3) as (HPD3 & HBl3 & _).
        assert (HinNew3 : In (p, n) (aa_live A3)) by (rewrite HL3; apply in_or_app; right; left; reflexivity).
        destruct (HBl3 p n HinNew3) as (G1' & _ & G3' & _).
        assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
        assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
        { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
        assert (E1 : rw rho' (pos_add_nat (ss_next (ax_S Cl)) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (ax_S (Pre_malloc E W st))) with NF in L4.
          unfold import_subA in Hres. change (ss_next (ax_S (Pre_malloc E W st))) with NF in Hres.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (wsub_get s 12)) = n).
        { unfold n, uval. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next (ax_S Cl)) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
        pose proof (HPAK Ai A3 HPA ltac:(rewrite <- Hn12; exact HC3)) as HPA2.
        eapply (cont_JAi Cl (Pre_malloc E W st) (L_malloc_ok E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                  _ bd' (wsub_get s 12) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
        -- intros b Hb. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact (HB b Hb).
        -- rewrite HV3, Hn12. unfold n. lia.
        -- rewrite HKm3, HKf3. unfold KU. lia.
        -- cbn zeta. split; [|split].
           ++
              constructor.
              ** intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [exact HinNew3|].
                 intros HinFB. pose proof (HB _ HinFB) as Hold. rewrite HLi3 in Hold.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (p, n) ltac:(rewrite <- HL3; exact HPD3) Hold) as D. cbn [fst snd] in D. lia.
              ** apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
                 unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
                 destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [|exact X2].
                 rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact X1.
           ++
              cbn [tvd]. split.
              ** intros t' Ht' _ Hnz'. rewrite Enew.
                 assert (Hbt' : (sv_below (ss_next (ax_S Cl)) (fst t') && sv_below (ss_next (ax_S Cl)) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hbt t' Ht').
                 rewrite (tvv_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt').
                 apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt')) in Hnz'.
                 destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (X0 & X1 & _).
                 intros Heq. rewrite HLi3 in X1.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (tvv rho t') ltac:(rewrite <- HL3; exact HPD3) X1) as D.
                 rewrite <- Heq in D. cbn [fst snd] in D. lia.
              ** apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++
              constructor.
              ** intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
              ** apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact Hb.
        --
           cbn zeta. intros b m Hb _ Hut. apply (proj2 (untracked_tv _ _ _)). intros t [<-|Ht] Hnz.
           ++ rewrite Enew. intros Heq. rewrite HLi3 in Hb.
              pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (b, m) ltac:(rewrite <- HL3; exact HPD3) Hb) as D. cbn [fst snd] in D.
              injection Heq as E1p E2n. destruct (HBl3 b m ltac:(rewrite HL3; apply in_app_mid; exact Hb)) as (Gm & _). lia.
           ++ revert t Ht Hnz. apply (proj1 (untracked_tv _ _ _)).
              eapply untracked_agree; [exact HagP | exact Hbt | exact Hut].
        -- cbn zeta. exact (TobjJAM.cen_insert FB Ai A3 rho _ _ (nd_tv nd) _ k1 k2 p n HagP Hbt HL3 HLi3 Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
        -- apply (TobjJAM.capK_insert BX Ai A3 k1 k2 p n HCKi HLi3 HL3); [unfold n, uval; match goal with |- context [bv_unsigned ?x] => pose proof (bv_urange x) end; lia | rewrite HV3; try rewrite Hn12; reflexivity].
        -- exact (TobjJAM.capN_insert BX Ai A3 _ rho _ (nd_tv nd) _ k1 k2 p n HCNi HLi3 HL3 HagP Hbt Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
Qed.

Theorem free_callT_k : ltac2:(tb__ "0|5|
S5S5fA1S61S15S4bS5S1cA1M0S18S5S46Q40A1A1M1S29S12S8S1aS1aA2M2S5S53A1S42S3dS18G1VTR;S26Vsegs;S6aVAInv;RfReR3VKc;A5S5bVE;RfReA3R2R1A5S70Vsegs;Sa2R2R1SeS8S15S71A2M3SbS15S71S5dVE;RfReA3S68VAInv;VCST;VXGL;R3VKc;A5A4S10G3A1A3A5A2Ftp1;Frho1;FAi;S0SdG0A1S73RbS5bVE;RdRcA3RaA3ScG0R9A2A3S0S6S72RcS5bVE;ReRdA3RbRaSeS15S5dVE;ReRdA3S10S15A1A3A5S7A3S0S6S85VNP;RcA2S7A3S0S6S88VNP;S19S14ReA1A1A2S7A3S0S6S2eS19S14RfA1A1RaA2S7A3S0S6S55S19S14R10A1A1R8A2S7A3S0SdG2A1S79G2S2aRcA1RbA3ScG2RaA2A3VpayA;S1bS14R12A1A1S1fZ0A1S57S2dRdA1RaA5S3dS3dVPA;R2A1S40R3R2A2VPA;R3A1F_;F_;FA';FA;S86VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R14R13R12R11RfScS24S54R11S48R13PcM4A2A2A2S3dS6dS1S94R13RfA2S1S0S8S24S24A2S95R13RfA2SbS24S24S54R13S48R15G4A2A2S54R13S48R15PdA2A2A4A3S60R18R17S4aS49R13R14R1A3R15A2A3A2A2Lms;LAi;AfS18G1S4eS19S14R17A1A1R14R2A3S83R15S92G2R12S2aR13A1A3R3A3VTR;S26Vsegs;VJA;S2bS92G2R13S2aR14A1A3S2fR14A1R11S2cR14A1A4A1S84S5bVE;R1bR1aA3R19R18R17S5dVE;R1bR1aA3A5R4R3A5R10A2F_;F_;Ftp';Frho';VTR;S26Vsegs;VJA;R11A1R16R13R12A5RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros W st Cl s R rho tp nd i t bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hnth HPAY HPAK HSITE Tfree.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  set (p := uval rho (wsub_get s 12)) in *. set (n := uval rho (wsub_get s 13)) in *.
  eapply (TR_callP (JAi nd Ai kc) (J_free_pre AInv W st Ai Kc) Cl (Pre_free E W st) s R
            [(L_free E W st, JL_free AInv CST XGL Ai Kc)] (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hnz & Ht & HU).
    split; [eapply AInv_absorb; [exact HM | eapply robjs_okA_weaken; exact HRok]|]. split; [exact HU|].
    split.
    { rewrite !rw_call'. destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (_ & X1 & _). rewrite Ht in X1. exact X1. }
    split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    split; [|exact (top_of_TPA Ai s rho _ _ Hav HT Htp)].
    eapply (BUD_limit_ok_free (nd_bd nd) _); [exact HBU | lia].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hnz & Ht & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    destruct HinL as [HinL | []]; injection HinL as HL HJLe; subst L JL.
    destruct HJL as (A2 & l1 & l2 & HM2 & HLi & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
    rewrite !rw_call' in HLi. fold p n in HLi. change (bv_unsigned (eval rho (wsub_get s 12))) with p in HLi. change (bv_unsigned (eval rho (wsub_get s 13))) with n in HLi.
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & TFB). rewrite Ht in Tpos, Tin, TFB. cbn [snd] in Tpos.
    destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (HPD & HBl & HFr).
    assert (SAMEBASE : forall b m, In (b, m) (aa_live Ai) -> b <> p -> In (b, m) (l1 ++ l2)).
    { intros b m Hin Hne. rewrite HLi in Hin. destruct (in_mid_cases' l1 l2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin'].
      exfalso. injection E0. lia. }
    assert (Hsub : forall a, cmaddrA Ai (Some p) a -> cmaddrA A2 None a).
    { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
      - right; right; left. exists b, m. rewrite HL2. split; [apply SAMEBASE; [exact Hin | intros ->; apply Hx; reflexivity] | auto].
      - right; right; right. exists f, sz. rewrite HF2. auto. }
    assert (HFB2 : forall b, In b FB -> In b (aa_live A2)).
    { intros [b m] Hb. rewrite HL2. pose proof (HB _ Hb) as Hin. rewrite HLi in Hin.
      destruct (in_mid_cases' l1 l2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin']. exfalso. apply TFB. rewrite <- E0. exact Hb. }
    split.
    * split; [split; [exact (KEPT_stepA Ai A2 (Some p) rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
         cbn [ax_S L_free Pre_free mkA ss_objs] in A, B0. apply B0.
         apply in_inv in A as [A|A]; [left; exact A|]. right. apply in_app_or in A as [A|A]; apply in_or_app; [left; exact A | right; apply in_or_app; right; exact A].
      -- intros r a j oR Hr. cbn in Hr. destruct Hr.
      -- eapply (caller_X_kept Ai A2 (Some p) rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         ++ eapply xrs_range; eauto.
         ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
            cbn [ax_S L_free Pre_free mkA ss_objs] in A, B0. apply B0.
            apply in_inv in A as [A|A]; [left; exact A|]. right. apply in_app_or in A as [A|A]; apply in_or_app; [left; exact A | right; apply in_or_app; right; exact A].
    * intros rho' Hlink.
      assert (HagP0 : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]).
      assert (KR : keptR rho (remove_nth i (nd_tv nd)) (rho_patch rho' (patchf rho rho' R))).
      { intros t0 z Ht0 Hnz0 Hz. destruct (proj1 (Forall_forall _ _) HN t0 (remove_nth_In _ _ _ Ht0) Hnz0) as (_ & Hl0 & _).
        refine (proj1 (live2_kept Ai A2 (Some p) rho rho' rhoL (vms md tp ms) s R tp md _ _ HM HRok Hkept2 (proj1 (proj2 Hlink)) Hl0 _) z Hz).
        rewrite HL2. pose proof Hl0 as Hl1. rewrite HLi in Hl1. destruct (in_mid_cases' l1 l2 (p, n) (tvv rho t0) Hl1) as [E0|Hin']; [|exact Hin'].
        exfalso. apply (tvd_nth_distinct rho (nd_tv nd) i t t0 HD Hnth Ht0 Hnz Hnz0). rewrite Ht. exact E0. }
      eapply TR_pre; [ | apply (Tfree (rho_patch rho' (patchf rho rho' R)) tpL HagP0 KR)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (A3 & k1 & k2 & HM3 & HLi3 & HL3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
      rewrite !rw_call' in HLi3. change (bv_unsigned (eval rho (wsub_get s 12))) with p in HLi3. change (bv_unsigned (eval rho (wsub_get s 13))) with n in HLi3.
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA Cl (Pre_free E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists A3, kc.
      assert (SAMEBASE3 : forall b m, In (b, m) (aa_live Ai) -> b <> p -> In (b, m) (k1 ++ k2)).
      { intros b m Hin Hne. rewrite HLi3 in Hin. destruct (in_mid_cases' k1 k2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin'].
        exfalso. injection E0. lia. }
      assert (DIST3 : forall bm, In bm (aa_live Ai) -> bm <> (p, n) -> In bm (k1 ++ k2)).
      { intros bm Hin Hne. rewrite HLi3 in Hin. destruct (in_mid_cases' k1 k2 (p, n) bm Hin) as [E0|Hin']; [exfalso; exact (Hne E0)|exact Hin']. }
      assert (Hsub' : forall a, cmaddrA Ai (Some p) a -> cmaddrA A3 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL3. split; [apply SAMEBASE3; [exact Hin | intros ->; apply Hx; reflexivity] | auto].
        - right; right; right. exists f, sz. rewrite HF3. auto. }
      destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      assert (Hbt' : tv_below (ss_next (ax_S Cl)) (remove_nth i (nd_tv nd)) = true).
      { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hbt). eapply remove_nth_In. exact Ht'. }
      pose proof (HPAK Ai A3 HPA HC3) as HPA2.
      eapply (cont_JAi Cl (Pre_free E W st) (L_free E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 (Some p)
                _ bd' (SLit 0) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
      -- intros [b m] Hb. rewrite HL3. apply DIST3; [exact (HB _ Hb)|]. intros E0. apply TFB. rewrite <- E0. exact Hb.
      -- rewrite HV3. pose proof (uval_range rho (SLit 0)). lia.
      -- rewrite HKm3, HKf3. unfold KU. lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' |].
            unfold tvinA in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
            destruct (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hnz') as (X0 & X1 & X2).
            split; [exact X0|]. split; [|exact X2]. rewrite HL3. apply DIST3; [exact X1|].
            rewrite <- Ht. exact (tvd_nth_distinct rho (nd_tv nd) i t t' HD Hnth Ht' Hnz Hnz').
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' | apply tvd_remove; exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' |].
            unfold tvz in HZ |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
      --
         intros b m Hb _ Hut. rewrite HL3. apply DIST3; [exact Hb|]. intros E0.
         apply (proj1 (untracked_tv _ _ _) Hut t (nth_error_In _ _ Hnth) Hnz). rewrite Ht. symmetry. exact E0.
      -- cbn zeta. intros b m _ _ Hut. eapply untracked_agree; [exact HagP | exact Hbt' |].
         eapply untracked_sub; [| exact Hut]. intros t' Ht'. eapply remove_nth_In. exact Ht'.
      -- cbn zeta. destruct (HBl p n ltac:(rewrite HLi3; apply in_or_app; right; left; reflexivity)) as (Gn & _).
         exact (TobjJAM.cen_remove FB Ai A3 rho _ _ (nd_tv nd) i t k1 k2 p n (aa_frames Ai) HagP Hbt Hnth Ht Gn HLi3 HL3 ltac:(rewrite <- HLi3; exact HPD)).
      -- apply (TobjJAM.capK_remove BX Ai A3 k1 k2 p n HCKi HLi3 HL3). rewrite HV3. lia.
      -- exact (TobjJAM.capN_remove BX Ai A3 _ rho _ (nd_tv nd) i t k1 k2 p n HCNi HLi3 HL3 HagP Hbt Hnth Ht Hnz).
Qed.

End CallTK.

Let TRs (ok : world -> Prop) : assn -> assn -> Prop := triple segs ok.
Let TRe : assn -> assn -> Prop := etriple segs.
Lemma TRs_facts : ltac2:(tb__ "0|1|
S43OF_;S27S15S18S5S46Q40A1A1S42S89S1dS21R3A1S1bS14R4A1A1A3VTRs;R7S26Vsegs;R6R5R4R3A5R2A3M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;Fok;").
Proof using . intros ok. exact (triple_factsA segs ok). Qed.
Lemma TRs_ex : forall ok (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TRs ok (SPA segs (J x) S rho tp) Q) -> TRs ok (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Proof using . intros ok. exact (triple_SPA_ex segs ok). Qed.
Lemma TRs_pre : ltac2:(tb__ "0|0|
S43OF_;S42S42S42S43R3R1A1R5R2A1F_;Fw;VTRs;R5R4R2A3VTRs;R6R4R3A3F_;F_;FQ;FP';FP;Fok;").
Proof using segs. intros ok P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma TRe_facts : ltac2:(tb__ "0|1|
S27S15S18S5S46Q40A1A1S42S89S1dS21R3A1S1bS14R4A1A1A3VTRe;S26Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Proof using . exact (etriple_factsA segs). Qed.
Lemma TRe_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TRe (SPA segs (J x) S rho tp) Q) -> TRe (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Proof using . exact (etriple_SPA_ex segs). Qed.
Lemma TRe_pre : ltac2:(tb__ "0|0|
S42S42S42S43R3R1A1R5R2A1F_;Fw;VTRe;R4R2A2VTRe;R4R3A2F_;F_;FQ;FP';FP;").
Proof using segs. intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.

Lemma TRe_pureP : ltac2:(tb__ "0|1|
S42OS42S43R4R1A1R4F_;Fw;R3VTRe;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Proof using . clear. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.
Lemma TRs_pureP : ltac2:(tb__ "0|1|
S43OF_;S42OS42S43R4R1A1R4F_;Fw;R3VTRs;R6R5R3A3M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof using . clear. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.

Ltac by_callT_safety ok lem :=
  apply (lem (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundPA3 segs ok)).
Ltac by_callT_ex lem :=
  apply (lem (etriple segs) TRe_facts TRe_ex TRe_pre (call_completePA3 segs)).

Theorem malloc_callA_k : ltac2:(tb__ "0|6|
S43OF_;S5S5fA1S61S15S4bS5S1cA1M0S18S5S46Q40A1A1M1S29S5S53A1S42S67RaR9A2S32Vsegs;VKc;RcA3S64Vsegs;VE;VAInv;VCST;VXGL;A5S0SdG0A1S73RbS5aVE;RdRcA3RaA3ScG0R9A2A3S0S6S72RcS5aVE;ReRdA3RbRaSeS15S5eVE;ReRdA3SeS15S5cVE;ReRdA3S10S15A1A3A3A5S7A3S0S6S85VNP;RcA2S7A3S0S6S88VNP;S19S14ReA1A1A2S7A3S0S6S2eS19S14RfA1A1RaA2S7A3S0S6S55S19S14R10A1A1RaA2S7A3S0S6S23S19S14R11A1A1S48R10PcM2A2A2S7A3S0S1aS48S74R11S5aVE;R14R13A3S5cVE;R14R13A3R12A4S63A2S20S4fS19S14R12A1A1UaM3A2A1A3VpayA;S1bS14R13A1A1S48R12G2A2S57S2dReA1RdA5S3dS3dVPA;R2A1S3fR3R2S54R14S48R16G2A2A2M4A3VPA;R3A1F_;F_;FA';FA;S86VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R15R14R13R12R10S11S24A1S3dS6dS1S1S8bZ1G4A2S8cG4S8eZ2Z27A2A2A2S60R19R18S4aS49R14R15R1A3R16A2A3A2Lms;LAi;AfS18G1S4eS19S14R18A1A1R15R2A3S83R16S2aR14A1R3A3S45Vsegs;R1dS26Vsegs;VJA;S2bS2aR15A1M5S2fR15A1R14S2cR15A1A4A1S84S5aVE;R1cR1bA3R1aR19R18S5eVE;R1cR1bA3A5R4R3A5R13A4F_;F_;Ftp';Frho';S18G1S4eS19S14R19A1A1R16R2A3S83R17G5R3A3S45Vsegs;R1eS26Vsegs;VJA;S2bSeS8S1aS1aA2SbS1aS1aS20S4fS19S14R1bA1A1G3A2A1S48R1aG2A2A4S2aR16A1A3S2fR16A1R15S2cR16A1A4A1S84S5aVE;R1dR1cA3R1bR1aR19S5cVE;R1dR1cA3A5R4R3A5R14A4F_;F_;Ftp';Frho';S45Vsegs;R1bS26Vsegs;VJA;R13A1R18R15R14A5R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;").
Proof using ALA HCST HXGL HKc HBX.
  intros ok W st Cl s R rho tp nd bd' Q HW Hok AC. by_callT_safety ok malloc_callT_k.
  intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [exact HW | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
Qed.

Theorem malloc_callA_ex_k : ltac2:(tb__ "0|6|
S5S5fA1S61S15S4bS5S1cA1M0S18S5S46Q40A1A1M1S29S5S53A1S42S67RaR9A2S65Vsegs;VE;VAInv;VCST;VXGL;A5S0SdG0A1S73RaS5aVE;RcRbA3R9A3ScG0R8A2A3S0S6S72RbS5aVE;RdRcA3RaR9SeS15S5eVE;RdRcA3SeS15S5cVE;RdRcA3S10S15A1A3A3A5S7A3S0S6S85VNP;RbA2S7A3S0S6S88VNP;S19S14RdA1A1A2S7A3S0S6S2eS19S14ReA1A1R9A2S7A3S0S6S55S19S14RfA1A1R9A2S7A3S0S6S23S19S14R10A1A1S48RfPcM2A2A2S7A3S0S1aS48S74R10S5aVE;R13R12A3S5cVE;R13R12A3R11A4S63A2S20S4fS19S14R11A1A1UaM3A2A1A3VpayA;S1bS14R12A1A1S48R11G2A2S57S2dRdA1RcA5S3dS3dVPA;R2A1S3fR3R2S54R13S48R15G2A2A2M4A3VPA;R3A1F_;F_;FA';FA;S86VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R14R13R12R11RfS11S24A1S3dS6dS1S1S8bZ1G4A2S8cG4S8eZ2Z27A2A2A2S60R18R17S4aS49R13R14R1A3R15A2A3A2Lms;LAi;AfS18G1S4eS19S14R17A1A1R14R2A3S83R15S2aR13A1R3A3S44Vsegs;S26Vsegs;VJA;S2bS2aR14A1M5S2fR14A1R13S2cR14A1A4A1S84S5aVE;R1bR1aA3R19R18R17S5eVE;R1bR1aA3A5R4R3A5R12A3F_;F_;Ftp';Frho';S18G1S4eS19S14R18A1A1R15R2A3S83R16G5R3A3S44Vsegs;S26Vsegs;VJA;S2bSeS8S1aS1aA2SbS1aS1aS20S4fS19S14R1aA1A1G3A2A1S48R19G2A2A4S2aR15A1A3S2fR15A1R14S2cR15A1A4A1S84S5aVE;R1cR1bA3R1aR19R18S5cVE;R1cR1bA3A5R4R3A5R13A3F_;F_;Ftp';Frho';S44Vsegs;S26Vsegs;VJA;R12A1R17R14R13A5R10A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc HBX.
  intros W st Cl s R rho tp nd bd' Q HW ACX. by_callT_ex malloc_callT_k.
  intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [exact HW | exact HKc].
Qed.

Theorem free_callA_k : ltac2:(tb__ "0|4|
S43OF_;S5S5fA1S61S15S4bS5S1cA1M0S18S5S46Q40A1A1M1S29S12S8S1aS1aA2M2S5S53A1S42S66RcRbA2S32Vsegs;VKc;ReA3S64Vsegs;VE;VAInv;VCST;VXGL;A5S0SdG0A1S73RdS5bVE;RfReA3RcA3ScG0RbA2A3S0S6S72ReS5bVE;R10RfA3RdRcSeS15S5dVE;R10RfA3S10S15A1A3A5S7A3S0S6S85VNP;ReA2S7A3S0S6S88VNP;S19S14R10A1A1A2S7A3S0S6S2eS19S14R11A1A1RcA2S7A3S0S6S55S19S14R12A1A1RaA2S7A3S0SdG2A1S79G2S2aReA1RdA3ScG2RcA2A3VpayA;S1bS14R14A1A1S1fZ0A1S57S2dRfA1RcA5S3dS3dVPA;R2A1S40R3R2A2VPA;R3A1F_;F_;FA';FA;S86VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R16R15R14R13R11ScS24S54R13S48R15PcM3A2A2A2S3dS6dS1S94R15R11A2S1S0S8S24S24A2S95R15R11A2SbS24S24S54R15S48R17G3A2A2S54R15S48R17PdA2A2A4A3S60R1aR19S4aS49R15R16R1A3R17A2A3A2A2Lms;LAi;AfS18G1S4eS19S14R19A1A1R16R2A3S83R17S92G2R14S2aR15A1A3R3A3S45Vsegs;R1eS26Vsegs;VJA;S2bS92G2R15S2aR16A1A3S2fR16A1R13S2cR16A1A4A1S84S5bVE;R1dR1cA3R1bR1aR19S5dVE;R1dR1cA3A5R4R3A5R12A4F_;F_;Ftp';Frho';S45Vsegs;R1bS26Vsegs;VJA;R13A1R18R15R14A5RfA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok W st Cl s R rho tp nd i t bd' Q HW Hok AC. by_callT_safety ok free_callT_k.
  intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [exact HW | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
Qed.

Theorem free_callA_ex_k : ltac2:(tb__ "0|4|
S5S5fA1S61S15S4bS5S1cA1M0S18S5S46Q40A1A1M1S29S12S8S1aS1aA2M2S5S53A1S42S66RcRbA2S65Vsegs;VE;VAInv;VCST;VXGL;A5S0SdG0A1S73RcS5bVE;ReRdA3RbA3ScG0RaA2A3S0S6S72RdS5bVE;RfReA3RcRbSeS15S5dVE;RfReA3S10S15A1A3A5S7A3S0S6S85VNP;RdA2S7A3S0S6S88VNP;S19S14RfA1A1A2S7A3S0S6S2eS19S14R10A1A1RbA2S7A3S0S6S55S19S14R11A1A1R9A2S7A3S0SdG2A1S79G2S2aRdA1RcA3ScG2RbA2A3VpayA;S1bS14R13A1A1S1fZ0A1S57S2dReA1RbA5S3dS3dVPA;R2A1S40R3R2A2VPA;R3A1F_;F_;FA';FA;S86VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R15R14R13R12R10ScS24S54R12S48R14PcM3A2A2A2S3dS6dS1S94R14R10A2S1S0S8S24S24A2S95R14R10A2SbS24S24S54R14S48R16G3A2A2S54R14S48R16PdA2A2A4A3S60R19R18S4aS49R14R15R1A3R16A2A3A2A2Lms;LAi;AfS18G1S4eS19S14R18A1A1R15R2A3S83R16S92G2R13S2aR14A1A3R3A3S44Vsegs;S26Vsegs;VJA;S2bS92G2R14S2aR15A1A3S2fR15A1R12S2cR15A1A4A1S84S5bVE;R1cR1bA3R1aR19R18S5dVE;R1cR1bA3A5R4R3A5R11A3F_;F_;Ftp';Frho';S44Vsegs;S26Vsegs;VJA;R12A1R17R14R13A5ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc.
  intros W st Cl s R rho tp nd i t bd' Q HW ACX. by_callT_ex free_callT_k.
  intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [exact HW | exact HKc].
Qed.
End Rt.
End WithSegs.
End TobjJAK.

