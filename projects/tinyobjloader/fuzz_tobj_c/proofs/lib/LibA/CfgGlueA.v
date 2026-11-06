(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "vna_state"; "vna_rank"; "vna_var"; "enodeA"; "SPfamEA"; "edgeA"; "withGA"; "ax_add_facts"; "cfg_edgesA"; "ea_leaf"; "ea_src"; "ea_sub"; "ea_tgt"; "eedge_okA"; "@Corelib.Init.Datatypes"; "list"; "andb"; "bool"; "option"; "true"; "false"; "pair"; "app"; "nat"; "orb"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "eval"; "agree_below"; "holds"; "ss_facts"; "sv_below"; "sprop_below"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "stableA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA.ECfgIA"; "to_enodeIA"; "vmeasIA"; "echeckIA"; "check_ecfgIA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "ltb"; "add"; "leb"; "lt"; "mul"; "pow"; "sub"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "rho_sub"; "sv_subst"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "RsSymJump"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section ECfgIA.
Variable segs : list Segment.

Definition vmeasIA (n : vnodeA) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S3eS41S43S42Z2Z40A2S45Q40S1dVrho;S3Vn;A1A2A2A2Z100A2S2Vn;A1A2").

Definition to_enodeIA (J : jpredA) (n : vnodeA) : enodeA := ltac2:(tb__ "0|0|
S15S19S2dS28A2S1aS37Frho;S15S2dS28S1Vn;A1VJ;A4S39Vn;A1A4").

Definition echeckIA (g : positive) (nodes : list vnodeA) (e : edgeA) : bool := ltac2:(tb__ "0|a|
S12S0A1S11Lx;M0S35S0Vnodes;SbVe;A1A3S0G0S35S0Vnodes;SdVe;A1A3S0S10S10S10S10S10S10S10S46ScVe;A1M1Vg;A2S4fVg;S1cS2cS1R2A1A1A1M2A2A2S21G2S3R2A1M3A2A2S3fZ0M4S2R1A1M5A2A2S3dG5Z100M6A2A2S3fG4S2R2A1M7A2A2S3dG7G6A2A2S18S4aS20S2cSaVe;A1A1A1M8G3Z1S48G1S3R1A1A2M9A4S10S4aG8G3G4G9A4S3dG5G7A2A2A2A2Lnj;S14X12x2Lni;S14X12x2").

Definition check_ecfgIA (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list vnodeA) : bool := ltac2:(tb__ "0|1|
S10S34S0S0S21S1cS2cS1R1A1A1A1S3R1A1A2Ln;Vcuts;A3S12SfS6A1M0A1S11Lx;S9Vsegs;Vfuel;Vcutpcs;Vg;S26S0S2dS1Vcuts;A4S26S0S2dS1Vexits;A4A6G0S34S6S3aVg;S16S0Vcuts;Vexits;A3A2R1A3Les;S14X12x2A2").

Lemma echeckIA_sound : ltac2:(tb__ "0|0|
S36S28SfS0A1S6S2aVsegs;R4R3A3S23S11S3aR5R3R2A3S13A3SeS26S0S4S38R5A1R4A4R3A2F_;F_;Fe;Fnodes;FJ;Fg;").
Proof using .
  intros g J nodes e HJ H. unfold echeckIA in H. unfold eedge_okA.
  intros Ti Tj Hi Hj rho rho' tp tr md Hag Hg HF.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [ni|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [nj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [to_enodeIA ena_state ena_pred ena_meas fst snd] in *.
  apply andb_prop in H as [H Hdec].
  apply andb_prop in H as [H Hri2]. apply andb_prop in H as [H Hri1].
  apply andb_prop in H as [H Hrj2]. apply andb_prop in H as [H Hrj1].
  apply andb_prop in H as [H Hvb]. apply andb_prop in H as [Hid Hgle].
  apply Pos.leb_le in Hgle. apply Z.leb_le in Hrj1. apply Z.ltb_lt in Hrj2. apply Z.leb_le in Hri1. apply Z.ltb_lt in Hri2.
  split.
  - eapply HJ; [| apply mat_equiv_refl | exact Hg]. eapply agree_below_trans.
    + eapply agree_below_le; [exact Hgle | exact Hag].
    + apply rho_sub_agree. exact Hid.
  - unfold vmeasIA. rewrite <- eval_subst.
    rewrite (eval_agree _ rho rho' (vna_var ni) Hag Hvb).
    pose proof (urange (eval rho' (sv_subst (ea_sub e) (vna_var nj)))) as R1.
    pose proof (urange (eval rho' (vna_var ni))) as R2.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + pose proof (uleq_sound rho' _ _ 1 _ HF Hlt) as U1. unfold U in U1. nia.
    + apply andb_prop in Heq as [Hu Hr]. apply Z.ltb_lt in Hr.
      pose proof (uleq_sound rho' _ _ 0 _ HF Hu) as U1. unfold U in U1. nia.
Qed.

Theorem cfg_complete_autoIA : ltac2:(tb__ "0|2|
S17SfS37A1S36SfS0A1M0G0S28S31OF_;SfS44Q40A1A1S2aVsegs;R6R3A3S0S33S0R1R7A3S4eR9S1cS2cS1R2A1A1A1A2F_;Fn;S23S11S3bRaR9R8R7R6A5S13A3S0S1aS33S0R2R9A3S32Vsegs;S29Vsegs;R9S1R3A1M1R2R7A5S31S24S5Vsegs;S26S0S4S38RaA1RcA4R8S39R4R3A2R1A5R9R1A1A2Lw;A3F_;Frho;FE;S0S1aS33S0R2RbA3S32Vsegs;S29Vsegs;RaG1R2R8A5R9A3F_;Frho;Fn;F_;F_;F_;F_;Ftp;FQ;FJ;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits J Q tp HJ Hg Hchk Hexits n rho Hin.
  unfold check_ecfgIA in Hchk. apply andb_prop in Hchk as [Hvars Hchk].
  destruct (cfg_edgesA segs fuel cutpcs g (map vna_state cuts) (map vna_state exits)) as [es|] eqn:Hes; [|discriminate].
  change (vna_state n) with (ena_state (to_enodeIA J n)). change J with (ena_pred (to_enodeIA J n)) at 1.
  apply (cfg_complete_genA segs fuel cutpcs g (map (to_enodeIA J) cuts) (map (to_enodeIA J) exits) es Q tp).
  - intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0). cbn. eapply stableA_mono; [exact (Hg m0 Hm0) | exact HJ].
  - intros m r r' Hm Hag. apply in_map_iff in Hm as (m0 & <- & Hm0). cbn in Hag |- *. unfold vmeasIA.
    rewrite (eval_agree _ r r' (vna_var m0) Hag (proj1 (forallb_forall _ _) Hvars m0 Hm0)). reflexivity.
  - rewrite !map_map. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He.
    apply (echeckIA_sound g J); [exact HJ|]. exact (proj1 (forallb_forall _ _) Hchk e He).
  - intros E rhoE HinE. apply in_map_iff in HinE as (E0 & <- & HinE0). exact (Hexits E0 rhoE HinE0).
  - apply in_map_iff. exists n. auto.
Qed.

Lemma eexit_post_IA0 : ltac2:(tb__ "0|0|
S28S36S1aSfS0A1SfS2eA1S0SfS44Q40A1A1S33S2eS30S1R2A1S4bA2R3A3S1aS32Vsegs;S29Vsegs;S7S1aS1eR9R8R1A3Lr;R9A2S1R4A1R1R3A5S31S24S5Vsegs;S26S0S4S38S7S1aS1eRaR9R1A3Lr;RaA2A1R7A4R4S39R5R2A2R1A5S2bVsegs;RaR9R8R4R6R1A7A2Lw;A3Frho;F_;Ftp;FP;Fposts;Fcuts;Frho0;Fn;FJ0;").
Proof using .
  intros J0 n rho0 cuts posts P tp Hin rho w [Hsm [Hag Hk]]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeafA (vna_state P) RsSymJump), rho. auto.
Qed.

Lemma eexit_reenter_IA : ltac2:(tb__ "0|7|
S28S36SfS0A1S31OF_;S0S0SfS1bA1S2dS49SfS44Q40M0A1A1M1S33S0R5R8A3S23S2dS1R6A1S8R5R4A2A3S23S11S2fS1R8A1R5R4A3S13A3S23S11S46R5RcA2S13A3S2aVsegs;RdReA3S23S11S34S1bS22S1cS2cR8A1A1A1R9A3S13A3S1aG1SfS4dA1S4cR14R4R3R2R1A4S27S1bS1fR5A1S20S2cS1R11A1A1A1A3S25S27S1bS1fS47R6ReA2M2A1R10A3S24S40S45G0S1dR6S3R12A1A2A2M3S45G0S1dG2S3R11A1A2A2M4A2S25S3cG3G4A2S3cS3eS2R11A1Z1A2S2R12A1A2A2A2A2F_;F_;Fmd;Ftr;Ftp;Frho;S25S3cZ0M5S2RcA1M6A2S40G6Z100A2A2S3cG5S2ReA1A2S1aS32Vsegs;S29Vsegs;R14S1R10A1R1RbA5S31S24S5Vsegs;S26S0S4S38R15A1R13A4RcS39R11R2A2R1A5R12R1A1A2Lw;A3Frho;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Fs;FT0;FF;FC;FE;FQ;Fcuts;Fg;FJ;").
Proof using .
  intros J g cuts Q E C F T0 s tp Hin HC He Hid HJ Hb HF HrC HrE rho w Hsp.
  exists w. split; [apply wsteps_refl|]. left.
  pose proof (SPA_facts_hold segs J rho (vna_state E) tp w Hsp) as FACTS.
  destruct Hsp as [Hsm HJw].
  destruct (HF rho tp (w_tr w) (cfg_model (w_cfg w)) HJw FACTS) as [HF1 HV].
  exists (to_enodeIA J C), (rho_sub rho s). split; [apply in_map; exact Hin|].
  cbn [to_enodeIA ena_state ena_pred ena_meas fst snd]. split.
  - rewrite HC. eapply SPA_entails_sem; eauto. 2: exact (conj Hsm HJw).
    intros r t tr' md' Hj Hf. exact (proj1 (HF r t tr' md' Hj Hf)).
  - unfold vmeasIA.
    pose proof (urange (eval (rho_sub rho s) (vna_var C))) as R1.
    pose proof (urange (eval rho (vna_var E))) as R2. nia.
Qed.

End ECfgIA.
