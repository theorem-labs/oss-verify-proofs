(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "agree_below"; "holds"; "ss_facts"; "sprop_below"; "ss_next"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "withGA"; "vna_state"; "ax_add_facts"; "SPfamEA"; "enodeA"; "SPfamA"; "to_enodeA"; "vmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "to_enodeIA"; "vmeasIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section GlueGA.
Variable segs : list Segment.

Lemma SPA_entails_sem1 : ltac2:(tb__ "0|0|
S22S26S10S10S7S1A1S28S0S7S25Q40A1A1S1dSaS8S12R7R6R4A3S9A3SaS8S29R5R9A2S9A3S24Vsegs;RaRbA3SaS8S2cS1S5S6SfR9A1A1A1R8A3S9A3SdS1S3R7A1S4SfRbA1A1A3SdS1S3S27R8R9A2A1RaA3F_;S21Vsegs;ReRcR8R7R6A6S21Vsegs;RfS17RbRcA2S27R9RaA2R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FF;FT0;FL;Fg;FJ;").
Proof using .
  intros J g L T0 F s rho tp w He Hid Hst Hb HF [Hsm Hk]. split.
  - apply smatchA_add_facts; [eapply smatchA_entails; eauto | | exact Hb].
    apply HF. eapply smatchA_facts; exact Hsm.
  - eapply Hst; [apply rho_sub_agree; exact Hid | apply mat_equiv_refl | exact Hk].
Qed.

Lemma exit_post_GA : ltac2:(tb__ "0|0|
S1dOF_;S22S26S0S7S10A1S7S11A1S10S10S7S1A1S28S7S25Q40A1A1S2bS11S13S17R3R4A2S2aA2R6A3SaS8S12R6R5R3A3S9A3SaS8S29R4RbA2S9A3S24Vsegs;RcRdA3SaS8S2cS1S5S6SfR8A1A1A1R7A3S9A3S0S2RfReR1A3SdS1S3R2A1S4SfRcA1A1A3SdS1S3S27R3RaA2A1RbA3F_;F_;Frho;S0S1fVsegs;R12S21Vsegs;S15S0S2R11R10R1A3Lr;R11A2RcR1R8A5S1dSbS1aVsegs;S15S0S2R12R11R1A3Lr;R12A2RfR9R1A5S23Vsegs;R12R11R10R9ReR1A7A2Lw;A4Frho;F_;F_;F_;F_;F_;F_;Ftp;Fs;FF;FP0;FE;Fposts;Fcuts;Frho0;Fn;FJ0;Fok;").
Proof using .
  intros ok J0 n rho0 cuts posts E P0 F s tp Hin He Hid Hst Hb HF rho.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm [Hag Hk]]. right. exists (mkLeafA (ax_add_facts F P0) RsSymJump), (rho_sub rho s).
  split; [exact Hin|]. split.
  - eapply agree_below_trans; [exact Hag|]. apply rho_sub_agree. exact Hid.
  - destruct (SPA_entails_sem1 J0 n E P0 F s rho tp w He Hid Hst Hb (HF rho Hag) (conj Hsm Hk)) as [Hsm' Hk']. split; assumption.
Qed.

Lemma eexit_post_GA : ltac2:(tb__ "0|1|
S22S26S0S7S14A1S7S11A1S14S10S7S1A1S28S7S25Q40A1A1S2bS11S13S17R3R4A2S2aA2R6A3SaS8S12S16R6A1R5R3A3S9A3SaS8S29R4RbA2S9A3S24Vsegs;RcRdA3SaS8S2cS1S5S6SfR8A1A1A1R7A3S9A3S0S2RfReR1A3SdS1S3R2A1S4SfS16RcA1M0A1A1A3SdS1S3S27R3RaA2A1RbA3F_;F_;Frho;S0S1eVsegs;S21Vsegs;S15S0S2R11R10R1A3Lr;R11A2G0R1R8A5S1dSbS18Vsegs;SeS14S19S1bS15S0S2R12R11R1A3Lr;R12A2A1RfA4R9S1cRdR2A2R1A5S23Vsegs;R12R11R10R9ReR1A7A2Lw;A3Frho;F_;F_;F_;F_;F_;F_;Ftp;Fs;FF;FP0;FE;Fposts;Fcuts;Frho0;Fn;FJ0;").
Proof using .
  intros J0 n rho0 cuts posts E P0 F s tp Hin He Hid Hst Hb HF rho w [Hsm [Hag Hk]].
  exists w. split; [apply wsteps_refl|]. right.
  exists (mkLeafA (ax_add_facts F P0) RsSymJump), (rho_sub rho s). split; [exact Hin|]. split.
  - eapply agree_below_trans; [exact Hag|]. apply rho_sub_agree. exact Hid.
  - destruct (SPA_entails_sem1 J0 n (vna_state E) P0 F s rho tp w He Hid Hst Hb (HF rho Hag) (conj Hsm Hk)) as [Hsm' Hk']. split; assumption.
Qed.

Lemma exit_contraA : ltac2:(tb__ "0|1|
S1dOF_;S22S10S20S7S25Q40A1A1M0S0G0S7S2eA1S2dR8R4R3R2R1A4SdS1S3R5A1S4SfR8A1A1A3ScF_;F_;Fmd;Ftr;Ftp;Frho;S0S1fVsegs;R7S21Vsegs;R6R5R1R3A5R4A4Frho;F_;Ftp;FQ;FE;FJ;Fok;").
Proof using .
  intros ok J E Q tp HX rho n Hn w [Hsm Hk]. exfalso. eapply (HX rho tp); [exact Hk|]. eapply smatchA_facts; exact Hsm.
Qed.

Lemma eexit_contraA : ltac2:(tb__ "0|1|
S22S10S1dOF_;S7S25Q40A1A1M0S0G0S7S2eA1S2dR8R4R3R2R1A4SdS1S3R5A1S4SfR8A1A1A3ScF_;F_;Fmd;Ftr;Ftp;Frho;S0S1eVsegs;S21Vsegs;R6R5R1R3A5R4A3Frho;F_;Ftp;FQ;FE;FJ;").
Proof using .
  intros J E Q tp HX rho w [Hsm Hk]. exfalso. eapply (HX rho tp); [exact Hk|]. eapply smatchA_facts; exact Hsm.
Qed.
End GlueGA.

Section PostIA.
Variable segs : list Segment.

Lemma eexit_post_IA : ltac2:(tb__ "0|1|
S22S26S0S7S14A1S7S11A1S14S10S7S1A1S28S7S25Q40A1A1S2bS11S13S17R3R4A2S2aA2R6A3SaS8S12S16R6A1R5R3A3S9A3SaS8S29R4RbA2S9A3S24Vsegs;RcRdA3SaS8S2cS1S5S6SfR8A1A1A1R7A3S9A3S0S2RfReR1A3SdS1S3R2A1S4SfS16RcA1M0A1A1A3SdS1S3S27R3RaA2A1RbA3F_;F_;Frho;S0S1eVsegs;S21Vsegs;S15S0S2R11R10R1A3Lr;R11A2G0R1R8A5S1dSbS18Vsegs;SeS14S19S2fS15S0S2R12R11R1A3Lr;R12A2A1RfA4R9S30RdR2A2R1A5S23Vsegs;R12R11R10R9ReR1A7A2Lw;A3Frho;F_;F_;F_;F_;F_;F_;Ftp;Fs;FF;FP0;FE;Fposts;Fcuts;Frho0;Fn;FJ0;").
Proof using .
  intros J0 n rho0 cuts posts E P0 F s tp Hin He Hid Hst Hb HF rho w [Hsm [Hag Hk]].
  exists w. split; [apply wsteps_refl|]. right.
  exists (mkLeafA (ax_add_facts F P0) RsSymJump), (rho_sub rho s). split; [exact Hin|]. split.
  - eapply agree_below_trans; [exact Hag|]. apply rho_sub_agree. exact Hid.
  - destruct (SPA_entails_sem1 segs J0 n (vna_state E) P0 F s rho tp w He Hid Hst Hb (HF rho Hag) (conj Hsm Hk)) as [Hsm' Hk']. split; assumption.
Qed.

Lemma eexit_postIA : ltac2:(tb__ "0|0|
S22S26S0S7S14A1S7S11A1S14S7S25Q40A1A1S2bS11S13S16R2A1S2aA2R3A3S0S1eVsegs;S21Vsegs;S15S0S2R9R8R1A3Lr;R9A2S16R4A1R1R3A5S1dSbS18Vsegs;SeS14S19S2fS15S0S2RaR9R1A3Lr;RaA2A1R7A4R4S30R5R2A2R1A5S23Vsegs;RaR9R8R4R6R1A7A2Lw;A3Frho;F_;Ftp;FP;Fposts;Fcuts;Frho0;Fn;FJ0;").
Proof using .
  intros J0 n rho0 cuts posts P tp Hin rho w [Hsm [Hag Hk]].
  exists w. split; [apply wsteps_refl|]. right. exists (mkLeafA (vna_state P) RsSymJump), rho. auto.
Qed.

End PostIA.
