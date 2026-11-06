(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "@Corelib.Init.Datatypes"; "list"; "Some"; "bool"; "true"; "option"; "@Corelib.Init.Logic"; "eq"; "ex"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "valuation"; "ss_facts"; "sobj"; "sprop"; "sprop_below"; "agree_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.PureCallB"; "frozenJ"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "vna_state"; "SPfamA"; "SPfamEA"; "ax_add_facts"; "enodeA"; "mkVNA"; "to_enodeA"; "vmeasA"; "vna_rank"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.PureCallB.PC"; "T_call"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition frozenJ (J : jpredA) (rho : valuation) : jpredA := ltac2:(tb__ "0|0|
SeS4S24Q40A1A1S4S38A1S37VJ;Vrho;R3R2R1A4Lm;Lt;Lp;L_;").

Section PC.
Variable segs : list Segment.

Lemma frozenJ_ok_frameA : ltac2:(tb__ "0|0|
S1aOF_;S16SeS19Vsegs;R3R2A3S19Vsegs;R4S20R3R2A2A3F_;Frho;FJ;Fok;").
Proof using . intros ok J rho H r tp tr ms md msv' HJ. exact (H rho tp tr ms md msv' HJ). Qed.

Lemma frozenJ_stableA : ltac2:(tb__ "0|0|
S1eS1eS16SeS17Vsegs;R3R2A3S17Vsegs;R5S20R3R2A2A3F_;Frho;FJ;Fg;Fn;").
Proof using .
  intros n g J rho H r r' tp tr md md' _ Hme HJ. unfold frozenJ in *.
  eapply H; [apply agree_below_refl | exact Hme | exact HJ].
Qed.

Definition T_call (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S2aSfS2VCl;A1A1S32Vs;VPre;VL;VCl;VR;A5A2").

Theorem pure_callJ : ltac2:(tb__ "0|4|
S1aOF_;S16S1eS0S0S25S4S10A1M0S4S1A1SeS4S24Q40A1A1M1S1dS17Vsegs;R9RaA3S36RaSdS2R9A1A1A2SeG1S1cVsegs;RfS15Vsegs;S20ReR7A2M2RbR2R1A5S18Vsegs;G2SdS2RbA1A1R2R1R8A6A4Ftp1;Frho1;S9S8G0A1S31RbRaR9A3S5G0R8A2A3S9S6S30RcRbRaR9S23S1S0S3R8A4A5S7A3S9S6S22S11S12SdS2RdA1M3A1A1SfG3A1A3S7A3S1SeS21S1R2RcA3S13SdS2R11A1A1RcR2A3S1cVsegs;R15S15Vsegs;R14S35R11R12R10RfS3R4A1A5R3RcA5RbA4F_;F_;Frho';FL;S1cVsegs;R12S15Vsegs;R11RfRaR9A5R8A4F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;Fg;FJ;Fok;").
Proof using .
  intros ok J g Cl Pre s R Posts rho tp Q Hst Hg Hsum He Hchk Hfb Hcont.
  apply triple_factsA. intros HF.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact Hk]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' HinL HAG n HgQ). split.
  - apply smatchA_add_facts; [exact HSP | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
  - unfold frozenJ in Hk'. cbn [w_tr w_cfg fst snd cfg_model].
    eapply (Hst rho rho' tp tr' md' md'); [eapply agree_below_le; [exact Hg | exact HAG] | apply mat_equiv_refl | exact Hk'].
Qed.

Theorem pure_callJ_ex : ltac2:(tb__ "0|4|
S16S1eS0S0S25S4S10A1M0S4S1A1SeS4S24Q40A1A1M1S1aOF_;S17Vsegs;R9RaA3S36RaSdS2R9A1A1A2SeG1S1bVsegs;S15Vsegs;S20ReR7A2M2RbR2R1A5S18Vsegs;G2SdS2RbA1A1R2R1R8A6A3Ftp1;Frho1;S9S8G0A1S31RbRaR9A3S5G0R8A2A3S9S6S30RcRbRaR9S23S1S0S3R8A4A5S7A3S9S6S22S11S12SdS2RdA1M3A1A1SfG3A1A3S7A3S1SeS21S1R2RcA3S13SdS2R11A1A1RcR2A3S1bVsegs;S15Vsegs;R14S35R11R12R10RfS3R4A1A5R3RcA5RbA3F_;F_;Frho';FL;S1bVsegs;S15Vsegs;R11RfRaR9A5R8A3F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;Fg;FJ;").
Proof using .
  intros J g Cl Pre s R Posts rho tp Q Hst Hg Hsum He Hchk Hfb Hcont.
  apply etriple_factsA. intros HF.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre Hk)) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' HinL HAG (tr', mkCfg ms' md')) as (w'' & Hsteps' & HQ).
  { split.
    - apply smatchA_add_facts; [exact HSP | |].
      + apply Forall_forall. intros q Hq.
        apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
        * exact (proj1 (forallb_forall _ _) Hfb q Hq).
        * exact (proj1 (Forall_forall _ _) HF q Hq).
      + apply forallb_forall. intros q Hq.
        eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
        unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
    - unfold frozenJ in Hk'. cbn [w_tr w_cfg fst snd cfg_model].
      eapply (Hst rho rho' tp tr' md' md'); [eapply agree_below_le; [exact Hg | exact HAG] | apply mat_equiv_refl | exact Hk']. }
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma call_exitJ : ltac2:(tb__ "0|6|
S1aOF_;S16S1eS4S0A1S1dS0S0S0S4S34A1M0S25S4S10A1M1S4S1A1SeS4S24Q40A1A1M2S17Vsegs;RcRdA3S36RdSdS2R9A1A1A2S9S8S0A1M3S33RbR8A2S5S0RaA2A3SeG2S1cVsegs;R13S15Vsegs;S20R12R7A2M4RcR2R1A5S18Vsegs;G4SdS2RcA1A1R2R1R8A6A4Ftp1;Frho1;S9S8G1A1S31RcRbR9A3S5G1R8A2A3S9S6S30RdRcRaR9S23S1S0S3R8A4A5S7A3S9S6S22S11S12SdS2ReA1M5A1A1SfG5A1A3S7A3S1S21S1R1RbA3SaG0G0SaS0S0SbS9G3S33S35R12R13R10RfS3R4A1A5R2A2S5S0R1A2A3S21S0R1R16A3A2LT;A2Lxfb;A2F_;FL;S1cVsegs;R16S15Vsegs;R15R11RaR9A5S1aScS28Vsegs;R16R14RaR1A5R13R1A1A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FPosts;FR;Fs;Fxf;FPre;FE2;FE;FQ;Fcuts;Fg;FJ;Fok;").
Proof using .
  intros ok J g cuts Q E E2 Pre xf s R Posts rho tp Hst Hg Hxf Hsum He Hchk Hfb Hback.
  eapply triple_conseq; [intros w Hw; exact (SPA_axforms segs J xf rho E E2 tp w Hxf Hw) | intros w Hw; exact Hw |].
  apply (pure_callJ ok J g E2 Pre s R Posts rho tp _ Hst Hg Hsum He Hchk Hfb).
  intros L rho' HinL _. destruct (Hback L HinL) as (xfb & T & Hb & HinT).
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. left. exists T, rho'. split; [exact HinT|]. exact (SPA_axforms segs J xfb rho' _ T tp w Hb Hw).
Qed.

Lemma call_eexitJ : ltac2:(tb__ "0|7|
S16S1eS4S26A1S1aOF_;S26S0S0S4S34A1M0S25S4S10A1M1S4S1A1SeS4S24Q40A1A1M2S17Vsegs;RcRdA3S36RdSdS2R9A1A1A2S9S8S0A1M3S33S27RbA1R8A2S5S0RaA2A3SeG2S1bVsegs;S15Vsegs;S20R12R7A2M4RcR2R1A5S18Vsegs;G4SdS2RcA1A1R2R1R8A6A3Ftp1;Frho1;S9S8G1A1S31RcRbR9A3S5G1R8A2A3S9S6S30RdRcRaR9S23S1S0S3R8A4A5S7A3S9S6S22S11S12SdS2ReA1M5A1A1SfG5A1A3S7A3S1S21S1R1RbA3SaG0G0SaS0S0SaS1fS1fSbS9G3S33S35R13R14R11R10S3R5A1A5R3A2S5S0R2A2A3SbS21S26S2cR2R1S14Z0M6A1A3R17A3SbS39G6R1A2S3aR1S2fR15A1A2A2A2A2Lr;A2LT;A2Lxfb;A2F_;FL;S1bVsegs;S15Vsegs;R15S27R11A1RaR9A5S1aScS29Vsegs;S23S26S2bS2dR16A1R14A4RaS2eR12RbA2R1A5R13R1A1A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FPosts;FR;Fs;Fxf;FPre;FE2;FE;FQ;Fcuts;Fg;FJ;").
Proof using .
  intros J g cuts Q E E2 Pre xf s R Posts rho tp Hst Hg Hxf Hsum He Hchk Hfb Hback.
  eapply etriple_conseq; [intros w Hw; exact (SPA_axforms segs J xf rho (vna_state E) E2 tp w Hxf Hw) | intros w Hw; exact Hw |].
  apply (pure_callJ_ex J g E2 Pre s R Posts rho tp _ Hst Hg Hsum He Hchk Hfb).
  intros L rho' HinL _ w Hw. destruct (Hback L HinL) as (xfb & T & r & Hb & HinT & Hr).
  exists w. split; [apply wsteps_refl|]. left.
  exists (to_enodeA J (mkVNA T r (SLit 0))), rho'. split; [apply in_map; exact HinT|].
  cbn [to_enodeA ena_state ena_pred ena_meas fst snd vna_state]. split; [exact (SPA_axforms segs J xfb rho' _ T tp w Hb Hw)|].
  unfold vmeasA. cbn [vna_rank vna_var eval].
  pose proof (bv_unsigned_in_range _ (eval rho (vna_var E))) as Hu. unfold bv_modulus in Hu.
  rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0. nia.
Qed.

End PC.
