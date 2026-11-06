(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs"; "PG_P"; "FUEL_pg"; "pg_cutpcs2"; "Pre_pg"; "E_r2"; "E_sc3"; "E_sc4"; "K29c"; "K318"; "K3dc"; "K4a"; "K4b"; "Kbbp"; "Kcm"; "Kfin"; "Knw"; "Kproj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vdir"; "mkLN"; "lnode"; "Vdown"; "SPfamE"; "Vup"; "enode"; "lmeas"; "to_enodeL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "SVar"; "sprop"; "agree_below"; "holds"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "nil"; "prod"; "bool"; "true"; "cons"; "false"; "pair"; "list"; "Some"; "app"; "nat"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts"; "elcut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_ex_nodes"; "lnodes_pg"; "lcuts_pg"; "lexits_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk"; "Posts_pg"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_glue"; "E3"; "E4"; "E5"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ECfgCuts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3.Lib_tess_run2d_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3.Lib_tess_polygon OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_ex_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3.Lib_tess_polygon_ex_c1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3.Lib_tess_polygon_ex_c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EXITS.
  Variable K : ltac2:(tb__ "0|0|
S2aS3bA1S3aOF_;F_;").
  Variable rho0 : valuation.
  Let G : ltac2:(tb__ "0|0|
S1cOFr;") := ltac2:(tb__ "0|0|
S1cS1fS2fVrho0;R1A3Lr;").
  Let Q : world -> Prop := ltac2:(tb__ "0|0|
S39S11VK;S2fVrho0;S3cA5").
  Let FAM (E : lnode) (rho : valuation) : ltac2:(tb__ "0|0|
S36OF_;") := ltac2:(tb__ "0|0|
S16S11VK;S3eS14S18S1aVG;A1S34S0A1A4S19VE;Vrho;A2A4").

  Lemma SP_facts : ltac2:(tb__ "0|0|
S22S1cS36S38S11VK;R3R2R1A5S3dS1eS20R3A1S21R4A1A3F_;Fw;Frho;FS;").
  Proof using . intros S rho [tr [ms md]] [Hsm _]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))). Qed.

  Lemma eexit_sc3 : ltac2:(tb__ "0|0|
S1cVG;R1A1S37S11S38S11VK;S3fR2A4S36S31VFAM;S13S5S0A1ZdS23S24S12S1bA2A1A3R3R1A3VQ;R1A1A2Lw;A3F_;Frho;").
  Proof using rho0.
    intros rho Hg w Hw.
    pose proof (SP_facts _ _ _ Hw) as HF.
    assert (Hn3 : holds rho (SPNot (SPBranch BC_NE pN (SLit 3)))).
    { exact (proj1 (Forall_forall _ _) HF _ ltac:(left; reflexivity)). }
    assert (Hw' : SP segs K E3r rho w).
    { eapply (SP_restate segs K rho E3 E3r); [reflexivity | exact sd3 | | constructor | exact Hw].
      unfold d3. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is3 rho Hn3). vm_compute. reflexivity. }
    refine (call_complete segs K K E3r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc s3 R3 P.Lib_tess__G1.Lib_tess_scale2d.Posts_sc _ rho efr3 chk3 _ _ w Hw').
    - intros rho1. apply P.Lib_tess__G1.Lib_tess_scale2d.scale2d_sum_ex.
    - intros L rho' HinL Hag'. destruct HinL as [<-|[]]. cbn [lf_state].
      change (import_post s3 (ss_next P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc) P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E3r) R3) with (import_post s3 NF P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E3r) R3). rewrite imp3.
      assert (HF' : Forall (holds rho') (ss_facts E3)).
      { eapply (Forall_holds_agree (ss_next E3r)); [exact Hag' | reflexivity | exact HF]. }
      assert (Hn3' : holds rho' (SPNot (SPBranch BC_NE pN (SLit 3)))).
      { exact (proj1 (Forall_forall _ _) HF' _ ltac:(left; reflexivity)). }
      intros w' Hw2. exists w'. split; [apply wsteps_refl|]. left.
      assert (Hw3 : SP segs K T3r rho' w').
      { eapply (SP_restate segs K rho' T3 T3r); [reflexivity | exact sd3r | | | exact Hw2].
        - unfold d3r. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is3 rho' Hn3'). vm_compute. reflexivity.
        - eapply Forall_by_eqb; [|exact HF']. vm_compute. reflexivity. }
      pose proof (SP_entails segs K T3r (K318 PG_P) s318 rho' w' ent318 Hw3) as Hw4.
      eapply (reenter_L segs K G (lcuts_pg PG_P) (mkLN (K318 PG_P) 12 []) _ (rho_sub rho' s318));
        [cbn; tauto | | exact Hw4 | cbn; lia | cbn; lia | cbn; lia].
      unfold G. eapply agree_below_trans; [exact Hg|]. eapply agree_below_trans; [eapply agree_below_le; [|exact Hag']; vm_compute; congruence|].
      apply rho_sub_agree. exact id318.
  Qed.

  Lemma eexit_sc4 : ltac2:(tb__ "0|0|
S1cVG;R1A1S37S11S38S11VK;S40R2A4S36S31VFAM;S13S6S0A1ZdS23S24S12S1bA2A1A3R3R1A3VQ;R1A1A2Lw;A3F_;Frho;").
  Proof using rho0.
    intros rho Hg w Hw.
    pose proof (SP_facts _ _ _ Hw) as HF.
    assert (Hn4 : holds rho (SPBranch BC_EQ pN (SLit 4))).
    { exact (proj1 (Forall_forall _ _) HF _ ltac:(left; reflexivity)). }
    assert (Hw' : SP segs K E4r rho w).
    { eapply (SP_restate segs K rho E4 E4r); [reflexivity | exact sd4 | | constructor | exact Hw].
      unfold d4. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is4 rho Hn4). vm_compute. reflexivity. }
    refine (call_complete segs K K E4r P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc s4 R4 P.Lib_tess__G1.Lib_tess_scale2d.Posts_sc _ rho efr4 chk4 _ _ w Hw').
    - intros rho1. apply P.Lib_tess__G1.Lib_tess_scale2d.scale2d_sum_ex.
    - intros L rho' HinL Hag'. destruct HinL as [<-|[]]. cbn [lf_state].
      change (import_post s4 (ss_next P.Lib_tess__G1.Lib_tess_scale2d.Pre_sc) P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E4r) R4) with (import_post s4 NF P.Lib_tess__G1.Lib_tess_scale2d.P_sc (ss_next E4r) R4). rewrite imp4.
      assert (HF' : Forall (holds rho') (ss_facts E4)).
      { eapply (Forall_holds_agree (ss_next E4r)); [exact Hag' | reflexivity | exact HF]. }
      assert (Hn4' : holds rho' (SPBranch BC_EQ pN (SLit 4))).
      { exact (proj1 (Forall_forall _ _) HF' _ ltac:(left; reflexivity)). }
      intros w' Hw2. exists w'. split; [apply wsteps_refl|]. left.
      assert (Hw3 : SP segs K T4r rho' w').
      { eapply (SP_restate segs K rho' T4 T4r); [reflexivity | exact sd4r | | | exact Hw2].
        - unfold d4r. constructor; [|constructor]. cbn [fst snd eval]. rewrite (n_is4 rho' Hn4'). vm_compute. reflexivity.
        - eapply Forall_by_eqb; [|exact HF']. vm_compute. reflexivity. }
      pose proof (SP_entails segs K T4r (K34c PG_P) s418 rho' w' ent34c Hw3) as Hw4.
      eapply (reenter_L segs K G (lcuts_pg PG_P) (mkLN (K34c PG_P) 12 []) _ (rho_sub rho' s418));
        [cbn; tauto | | exact Hw4 | cbn; lia | cbn; lia | cbn; lia].
      unfold G. eapply agree_below_trans; [exact Hg|]. eapply agree_below_trans; [eapply agree_below_le; [|exact Hag']; vm_compute; congruence|].
      apply rho_sub_agree. exact id418.
  Qed.

  Lemma eexit_r2 : ltac2:(tb__ "0|0|
S1cVG;R1A1S37S11S38S11VK;S41R2A4S36S31VFAM;S13S4S0A1ZdS23S24S12S1bA2A1A3R3R1A3VQ;R1A1A2Lw;A3F_;Frho;").
  Proof using rho0.
    intros rho Hg w Hw.
    pose proof (SP_facts _ _ _ Hw) as HF.
    assert (Hw' : SP segs K E5c rho w).
    { apply (SP_smatch_step K rho E5b E5c); [intros X; rewrite <- e5c; apply smatch_select; [exact X | select_ok | select_ok | select_ok] |].
      apply (SP_smatch_step K rho E5a E5b); [eapply smatch_split; exact sp5b |].
      apply (SP_smatch_step K rho E5 E5a); [eapply smatch_split; exact sp5a |]. exact Hw. }
    refine (call_complete segs K K E5c (Pre_r2 R2_P) s5 R5 (Posts_r2 R2_P) _ rho efr5 chk5 _ _ w Hw').
    - intros rho1. apply run2d_sum_ex.
    - intros L rho' HinL Hag'. destruct HinL as [<-|[]]. cbn [lf_state].
      change (import_post s5 (ss_next (Pre_r2 R2_P)) (P_ret R2_P) (ss_next E5c) R5) with (import_post s5 NF (P_ret R2_P) (ss_next E5c) R5). rewrite imp5.
      assert (HF' : Forall (holds rho') (ss_facts E5)).
      { eapply (Forall_holds_agree (ss_next E5c)); [exact Hag' | reflexivity | exact HF]. }
      intros w' Hw2. exists w'. split; [apply wsteps_refl|]. left.
      assert (Hw3 : SP segs K T5e rho' w').
      { eapply (SP_restate segs K rho' T5d T5e); [reflexivity | exact sd5 | constructor | eapply Forall_by_eqb; [|exact HF']; vm_compute; reflexivity |].
        apply (SP_smatch_step K rho' T5c T5d); [eapply smatch_merge; exact mg5d |].
        apply (SP_smatch_step K rho' T5b T5c); [eapply smatch_merge; exact mg5c |].
        apply (SP_smatch_step K rho' T5a T5b); [intros X; rewrite <- t5b; apply smatch_select; [exact X | select_ok | select_ok | select_ok] |].
        apply (SP_smatch_step K rho' T5 T5a); [eapply smatch_rebase; exact rb5 |]. exact Hw2. }
      pose proof (SP_entails segs K T5e (K3dc PG_P) s3dc rho' w' ent3dc Hw3) as Hw4.
      eapply (reenter_L segs K G (lcuts_pg PG_P) (mkLN (K3dc PG_P) 12 []) _ (rho_sub rho' s3dc));
        [cbn; tauto | | exact Hw4 | cbn; lia | cbn; lia | cbn; lia].
      unfold G. eapply agree_below_trans; [exact Hg|]. eapply agree_below_trans; [eapply agree_below_le; [|exact Hag']; vm_compute; congruence|].
      apply rho_sub_agree. exact id3dc.
  Qed.
End EXITS.

Lemma elc_0 : ltac2:(tb__ "0|0|
S30S25S32S11S1S2S0A1S2fS33S0A1U0S13S3S0S23S1eA1A2Z14S23S24S12S1bA2A1A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_1 : ltac2:(tb__ "0|1|
S30S25S32S11S1S2S0A1S2fS33S0A1U1S13SeS0A1Z13S27S24S12S1bA2M0S29S12S1bS15S28A1S1dP79A1A4S23G0A1A3A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_2 : ltac2:(tb__ "0|1|
S30S25S32S11S1S2S0A1S2fS33S0A1U2S13SdS0A1Z12S27S24S12S1bA2M0S29S12S1bS17S28A1S1dP78A1A4S23G0A1A3A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_3 : ltac2:(tb__ "0|1|
S30S25S32S11S1S2S0A1S2fS33S0A1U3S13SfS0A1Z11S27S24S12S1bA2M0S29S12S1bS15S28A1S1dP7bA1A4S23G0A1A3A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_5 : ltac2:(tb__ "0|1|
S30S25S32S11S1S2S0A1S2fS33S0A1U5S13S10S0A1ZfS27S24S12S1bA2M0S29S12S1bS15S28A1S1dP7bA1A4S23G0A1A3A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_6 : ltac2:(tb__ "0|1|
S30S25S32S11S1S2S0A1S2fS33S0A1U6S13ScS0A1ZfS27S24S12S1bA2M0S29S12S1bS15S28A1S1dP7bA1A4S23G0A1A3A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_7 : ltac2:(tb__ "0|0|
S30S25S32S11S1S2S0A1S2fS33S0A1U7S13S7S0A1ZeS23S24S12S1bA2A1A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_8 : ltac2:(tb__ "0|0|
S30S25S32S11S1S2S0A1S2fS33S0A1U8S13S8S0A1ZcS23S24S12S1bA2A1A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_10 : ltac2:(tb__ "0|0|
S30S25S32S11S1S2S0A1S2fS33S0A1UaS13S9S0A1ZcS23S24S12S1bA2A1A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_11 : ltac2:(tb__ "0|0|
S30S25S32S11S1S2S0A1S2fS33S0A1UbS13SaS0A1ZbS23S24S12S1bA2A1A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_12 : ltac2:(tb__ "0|0|
S30S25S32S11S1S2S0A1S2fS33S0A1UcS13SbS0A1ZaS23S24S12S1bA2A1A3A7S26A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma elc_all : ltac2:(tb__ "0|1|
S2dS14S30S2eS14A1S42S14S34S0A1M0R2A3S2bS14R1A2A3S30S25S32S11S1S2S0A1S2fS2cS14G0S35S0A1A3R3R2A7S26A3F_;Fn;Fi;").
Proof.
  intros i n Hn. change (elcut segs FUEL_pg (pg_cutpcs2 PG_P) NF (lnodes_pg PG_P) i n = true).
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_0|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_1|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_2|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_3|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_4|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_5|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_6|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_7|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_8|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_9|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_10|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_11|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_12|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_13|].
  destruct i; cbn in Hn; discriminate.
Qed.

Theorem tess_polygon_sum_ex : ltac2:(tb__ "0|0|
S2aS3bA1S3aOF_;F_;S1cS37S11S38S11R2S3S0S23S1eA1A2R1A4S39S11R2S2fR1S3cA5A3Frho;FK;").
Proof.
  intros K rho. change (Pre_pg PG_P []) with (ln_state (mkLN (Pre_pg PG_P []) 20 [])).
  apply (cfg_complete_auto2_cuts segs FUEL_pg (pg_cutpcs2 PG_P) NF (lcuts_pg PG_P) (lexits_pg PG_P)
           (fun r => agree_below NF rho r) K (LQ segs K NF rho Posts_pg)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact elc_all.
  - intros E rho' HinE HG. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [ln_state].
    + apply eexit_post_L; [left; reflexivity | exact HG].
    + apply eexit_post_L; [right; left; reflexivity | exact HG].
    + apply (eexit_sc3 K rho). exact HG.
    + apply (eexit_sc4 K rho). exact HG.
    + apply (eexit_r2 K rho). exact HG.
  - cbn. tauto.
  - apply agree_below_refl.
Qed.
