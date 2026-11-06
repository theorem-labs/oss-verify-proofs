(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvJ.

(* [comment removed for export] *)
Module DrvJRe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "Some"; "option"; "orb"; "pair"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "ss_facts"; "sprop"; "SVar"; "sv"; "agree_below"; "eval"; "holds"; "rm"; "rw"; "sobj"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "nd_tv"; "JA"; "JAi"; "am_subst"; "fr_sub_eqb"; "am_eqb"; "amode"; "keptFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "V_TOP"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "w_cfg"; "w_tr"; "assn"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "to_nat"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nw.DrvJRe.PureCallV"; "post_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bud_le"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "import_sub"; "wsub_bound"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Code DrvJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Reorigin.
Variable AInv : ltac2:(tb__ "0|0|
S3aSfS8S25Q40A1A1S1dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Variable NP : positive.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S8S9S9S1fS1fA2S1fA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis H24 : (24 < NP)%positive.
Hypothesis H30 : (V_TOP < NP)%positive.

Lemma rw_rho_sub : ltac2:(tb__ "0|0|
SfS28S20S0S25Q40A1S19S26R3R2A2R1A2S16R3S27R2R1A2A2A3Fv;Fs;Frho;").
Proof. intros. reflexivity. Qed.

Lemma JAi_reorigin : ltac2:(tb__ "0|3|
SfSfOF_;M0G0S28S20S8S12A1S2aS2aS3aS1fSfSfS8S25Q40A1A1S8S1eA1S1dS0S14S27RcP18M1A2S13G1A1A3S0S14S27RdS38A2S13S38A1A3S44VNP;RdA2S0S6S2dReRcA2S7A3S0S6S51R10S2fRdA1S2fRcA1A3S7A3S0S6S33R11S2eReA1S2eRdA1A3S7A3S0S6S53R10S52R12S2cReA1A2S2cRfA1A3S7A3S0S35S32R13S2bRfA1A2S2bR10A1A3S15R13RdRcA3S45S12S17RdA1R13A3R17S26ReR16A2A1S31VAInv;VCST;VXGL;VNP;VKc;R1aR19VFB;VFF;VBX;VPA;R14R12R11R10ReRdRcA12S31VAInv;VCST;VXGL;VNP;VKc;S26R10R18A2M2R19VFB;VFF;VBX;VPA;R14R13R12G2RfReRdA12F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fkc;FAi;Fndj;Fndi;Ffacts;Fn;Fs;FP0f';FP0f;Frho0;").
Proof using ALA H24 H30.
  intros rho0 P0f P0f' s n facts ndi ndj Ai kc rho rho' tp tr md Hs24 Hs30 H2 H3 H5 H6 H7 Ham Hag HF HP0'' HJ.
  destruct (nd_below_split n ndi H3) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  destruct (tv_sub_eqb_sound s _ _ rho' H5) as [M1 M2].
  assert (Hrm0 : forall a, rm rho' a = rm rho a).
  { intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm. }
  assert (Hrm : forall a, rm (rho_sub rho' s) a = rm rho a).
  { intros a. cbn [rho_sub rm]. apply Hrm0. }
  split; [apply agree_vals_refl|].
  split; [exact Hk|].
  split; [eapply (law_vars _ _ _ ALA); [exact HM|]; apply functional_extensionality; exact Hrm|].
  split.
  {
    unfold TPA, T0 in HT |- *. rewrite !rw_rho_sub, Hs24. change Contract.V_TOP with V_TOP. rewrite Hs30. cbn [eval].
    destruct Hav' as [Hv _]. rewrite <- (Hv 24%positive ltac:(lia)), <- (Hv V_TOP ltac:(lia)).
    destruct Hav as [Hv0 _]. rewrite <- (Hv0 24%positive H24), <- (Hv0 V_TOP H30). exact HT. }
  split; [exact HB|]. split; [exact HFF|].
  split; [split; [|split]|].
  - eapply tvinA_map; [exact M1 | exact M2 |]. eapply tvinA_agree; [exact Hav' | exact Hbt | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact Hbt | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact Hbt | exact HZ].
  - split; [eapply fr_sub_eqb_sound; [exact H6|]; eapply frinA_agree; [exact Hav' | exact Hbf | exact HFR]|].
    split; [apply keptFA_refl|].
    split; [exact HP0''|].
    split; [eapply XA_subst; [exact M1 |]; rewrite Ham; eapply XA_agree; [exact Hav' | exact Hrm0 | exact Hba | exact Hbt | exact HXA]|].
    assert (HCNT : cntS rho (nd_tv ndi) <= cntS (rho_sub rho' s) (nd_tv ndj)) by (rewrite (cntS_map _ _ _ _ M1), (cntS_agree n rho rho' _ Hav' Hbt); lia).
    split; [|exact (JA_tail_le _ _ _ rho (rho_sub rho' s) _ _ HCNT HPA)].
    rewrite <- apot_subst, Ham, (apot_agree (nd_am ndi) n rho rho' Hav' Hrm0 Hba).
    eapply BUD_transfer; [exact HF | exact H7 |]. eapply BUD_agree; [exact Hav' | exact Hbb | exact HBU].
Qed.

Lemma SPA_reorigin_JA : ltac2:(tb__ "0|3|
SfSfOF_;M0G0S2S2S28S2aS2aSfS8S25Q40A1A1S3dS0S6S5R8R7R6A3S7A3S0S14S27R7P18M1A2S13G1A1A3S0S14S27R8S38A2S13S38A1A3S0S6S41VNP;S10S1RbA1A1A2S7A3S0S6S2dS10S1RcA1A1R9A2S7A3S0S6S51RbS2fRaA1S2fR9A1A3S7A3S0S6S33RcS2eRbA1S2eRaA1A3S7A3S0S6S53S11S1RfA1A1S52RdS2cRbA1A2S2cRcA1A3S7A3S0S6S34S32ReS2bRcA1A2S2bRdA1A2S7A3S3aS1fS45S12S17ReA1S11S1R13A1A1A3R16R17A1S57VNP;R18R10A3S36VCST;VXGL;R19VFB;VFF;S18R19A1S18R11A1A7VKc;S3fR10A1S48S3eR10A1A1A2S31VAInv;VCST;VXGL;VNP;VKc;R1bR1aVFB;VFF;VBX;VPA;R15R7R6R13R12S3fR11A1S48S3eR11A1A1A12R1aS26R14R17A2A1F_;F_;F_;F_;F_;F_;Fkc;FAi;S21S1cS30VAInv;VCST;VXGL;VNP;VKc;R15R14VFB;VFF;VBX;VPA;RfAcR12RdRcRbA6S21S1cS30VAInv;VCST;VXGL;VNP;VKc;S26ReR11A2M2R14VFB;VFF;VBX;VPA;RfAcR12G2RdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;FP0f';FP0f;Frho0;").
Proof using ALA H24 H30.
  intros rho0 P0f P0f' L T s ndi ndj rho tp w He Hs24 Hs30 Hnp Hnb Htv Hfr Hbd Ham HP0' [Hsm HJ]. apply Pos.leb_le in Hnp. apply am_eqb_sound in Ham.
  split; [eapply smatchA_entails; [exact He | exact Hsm]|].
  destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ, HP0' |- *.
  destruct HJ as (Ai & kc & HJ). exists Ai, kc.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  eapply (JAi_reorigin rho0 P0f P0f' s (ss_next (ax_S L)) (ss_facts (ax_S L)));
    [exact Hs24 | exact Hs30 | exact Hnp | exact Hnb | exact Htv | exact Hfr | exact Hbd | exact Ham | apply agree_below_refl | exact HF | | exact HJ].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK & HP0 & HXA & HBU & HPA).
  exact (HP0' Ai kc HF HP0 Hav HK Hk HJ).
Qed.
End Reorigin.

Section PureCallV.
Variable AInv : ltac2:(tb__ "0|0|
S3aSfS8S25Q40A1A1S1dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Variable NP : positive.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S8S9S9S1fS1fA2S1fA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Let JAK (Kc : KcA) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S30VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Vnd;Ac").

Definition post_val (s : wsub) (Pre Cl L : sstate) (rho' rhoL : valuation) : Prop := ltac2:(tb__ "0|2|
S20S0S6ScScSeS42R1S10VPre;A1M0A2A1S59Vs;R1A2A2S42R1S10VCl;A1M1A2A2S7A3S56S43R2A1S43S10VL;A1A1A2S0S25Q40A1S19VrhoL;R3A2S16Vrho';S27S58Vs;G0VL;G1A4R3A2A2A3F_;F_;Fv;").

Theorem pure_callJ_v : ltac2:(tb__ "0|4|
S3dOF_;S37S37S2S2S28S8S1aA1M0S8S3A1SfS8S25Q40A1A1M1S2aS22S22S40S39RcA1SfG1S3cS1cR11S21S1cR6RdR2R1A5S23S1cR5S10S1RdA1A1R2R1RaA6A4Ftp1;Frho1;S0SbG0A1S4eRdRcRbA3SaG0RaA2A3S0S6S4dReRdRcRbS46S3S2S4RaA4A5S7A3S0S6S41VNP;S10S1RfA1A1A2S7A3S0S6S2dS10S1R10A1A1R9A2S7A3S0S6S55S12S1bS10S1R11A1M2A1A1S11G2A1A3S7A3S8S1eA1M3S47S1dS24S1cR10RfR15SdG3S49R3S4aR2R1A2A4A5VJAK;R18RfR11R10R4R2A6RfS26S29R12R14S50R3R11R4A3A3R15A2R11R5R3A4F_;F_;Fmd;Fms;Ftr;SfG3S1dRdR3R10R2R1A4VJAK;R18R10R12R11R3R2A6F_;Fmd';Ftr';FrhoL;S3SfSfG3S1dS54S3R5R15A3S15S10S1R1aA1A1R15R5A3R12R5R15R4R3A4S4bR1aS1R1bA1S1R1cA1S1S4R8A1A1R7R6A6S3cS1cR20S21S1cVJAK;R1eR16A2S4cS11S1R1dA1A1S4fR1bR1cS4R9A1R1dR1aA5A2R8R17A5R13A4F_;F_;F_;F_;Fmd';Ftr';FrhoL;Frho';FL;S3cS1cR18S21S1cVJAK;R17ReA2R15R10RfA5RbA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FJp';FJp;Fnd;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;FKc';FKc;Fok;").
Proof using ALA.
  intros ok Kc Kc' Cl Pre s R Posts rho tp nd Jp Jp' Q HKc' Hsum He Hchk Hnf Hnb Hfb HIN HOUT Hcont. apply Pos.leb_le in Hnf.
  apply triple_factsA. intros HF.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (HIN tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' rhoL tr' md' HinL HAG Hk' (proj2 (proj2 HLK)) n HgQ). split.
  - apply smatchA_add_facts; [exact HSP | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
  - destruct (HOUT rhoL tr' md' Hk') as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NP Kc' rho0 P0f FB FF BX PA HKc' ALA (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ').
Qed.

Theorem pure_callJ_v_ex : ltac2:(tb__ "0|4|
S37S37S2S2S28S8S1aA1M0S8S3A1SfS8S25Q40A1A1M1S2aS22S22S3dOF_;S39RcA1SfG1S3bS1cS21S1cR6RdR2R1A5S23S1cR5S10S1RdA1A1R2R1RaA6A3Ftp1;Frho1;S0SbG0A1S4eRdRcRbA3SaG0RaA2A3S0S6S4dReRdRcRbS46S3S2S4RaA4A5S7A3S0S6S41VNP;S10S1RfA1A1A2S7A3S0S6S2dS10S1R10A1A1R9A2S7A3S0S6S55S12S1bS10S1R11A1M2A1A1S11G2A1A3S7A3S8S1eA1M3S47S1dS24S1cR10RfR15SdG3S49R3S4aR2R1A2A4A5VJAK;R18RfR11R10R4R2A6RfS26S29R12R14S50R3R11R4A3A3R15A2R11R5R3A4F_;F_;Fmd;Fms;Ftr;SfG3S1dRdR3R10R2R1A4VJAK;R18R10R12R11R3R2A6F_;Fmd';Ftr';FrhoL;S3SfSfG3S1dS54S3R5R15A3S15S10S1R1aA1A1R15R5A3R12R5R15R4R3A4S4bR1aS1R1bA1S1R1cA1S1S4R8A1A1R7R6A6S3bS1cS21S1cVJAK;R1eR16A2S4cS11S1R1dA1A1S4fR1bR1cS4R9A1R1dR1aA5A2R8R17A5R13A3F_;F_;F_;F_;Fmd';Ftr';FrhoL;Frho';FL;S3bS1cS21S1cVJAK;R17ReA2R15R10RfA5RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FJp';FJp;Fnd;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;FKc';FKc;").
Proof using ALA.
  intros Kc Kc' Cl Pre s R Posts rho tp nd Jp Jp' Q HKc' Hsum He Hchk Hnf Hnb Hfb HIN HOUT Hcont. apply Pos.leb_le in Hnf.
  apply etriple_factsA. intros HF.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (HIN tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' rhoL tr' md' HinL HAG Hk' (proj2 (proj2 HLK)) (tr', mkCfg ms' md')) as (w'' & Hsteps' & HQ).
  { split.
    - apply smatchA_add_facts; [exact HSP | |].
      + apply Forall_forall. intros q Hq.
        apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
        * exact (proj1 (forallb_forall _ _) Hfb q Hq).
        * exact (proj1 (Forall_forall _ _) HF q Hq).
      + apply forallb_forall. intros q Hq.
        eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
        unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
    - destruct (HOUT rhoL tr' md' Hk') as (Ai & kc & HJ'). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NP Kc' rho0 P0f FB FF BX PA HKc' ALA (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ'). }
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.
End PureCallV.
End DrvJRe.

