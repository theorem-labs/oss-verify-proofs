(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "nat"; "bool"; "true"; "Some"; "option"; "pair"; "prod"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "vnodeA"; "check_cfgA"; "vna_state"; "cfg_edgesA"; "check_cutA"; "check_ecfgA"; "cuts_edgesA"; "first_matchA"; "leaf_matchesA"; "leaf_okA"; "leaf_okA_ref"; "leaves_edgesA"; "leaves_edgesA_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "forallb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section Edges.
Variable segs : list Segment.

Lemma first_matchA_matches : ltac2:(tb__ "0|1|
SbS9S0S9A1S1S1S1cS8S5S7S1S1cA2M0A1S15R6R5R4R3A4S4G0S6S1S1cR2R1A4A2A3S8S2S16R7R6R5A3S3A3F_;Fs;Fj;Fj0;Ftargets;FL;Fg;").
Proof.
  induction targets as [|X rest IH]; intros j0 j s H; cbn in H; [discriminate|].
  unfold leaf_matchesA. cbn. destruct (leaf_matches1A g L X) eqn:E; [reflexivity|].
  eapply IH. exact H.
Qed.

Lemma leaves_edgesA_ok_ref : ltac2:(tb__ "0|1|
SbS1S0SaA1S0S9A1S0SdA1M0S8S5G0A1S1aR5R4R3R2A4S4G0R1A2A3S8S2S1bSaS18R6R3A2R4A3S3A3F_;Fes;Ftargets;Fleaves;Fi;Fg;").
Proof.
  induction leaves as [|L rest IH]; intros targets es H; cbn in H |- *; [reflexivity|].
  unfold leaf_okA_ref at 1. destruct (leaf_refuted (la_state L)) eqn:Hr.
  - eapply IH. exact H.
  - destruct (first_matchA g (la_state L) targets 0) as [[j s]|] eqn:Hm; [|discriminate].
    destruct (leaves_edgesA_ref g i rest targets) as [es'|] eqn:He; [|discriminate].
    rewrite (first_matchA_matches g (la_state L) targets 0 j s Hm). eapply IH. exact He.
Qed.

Lemma leaves_edgesA_ok : ltac2:(tb__ "0|1|
SbS1S0SaA1S0S9A1S0SdA1M0S8S5G0A1S19R5R4R3R2A4S4G0R1A2A3S8S2S1bSaS17R6R3A2R4A3S3A3F_;Fes;Ftargets;Fleaves;Fi;Fg;").
Proof.
  intros g i leaves targets es H. rewrite leaves_edgesA_ref_eq in H. rewrite forallb_lazy_leaf_okA_ref. exact (leaves_edgesA_ok_ref g i leaves targets es H).
Qed.

Lemma cuts_edgesA_ok : ltac2:(tb__ "0|2|
S1S0ScA1SbS1S0S9A1M0G0S0SdA1M1S8S5G1A1S14Vsegs;R7R6R5R4R3R2A7S4G1R1A2A3S8S2S1bS9S12Vsegs;R8R7R6R3A5R4A3S3A3F_;Fes;Ftargets;Fcuts;Fi;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g i cuts. revert i.
  induction cuts as [|T rest IH]; intros i targets es H; cbn in H |- *; [reflexivity|].
  unfold check_cutA at 1.
  destruct (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T); [|discriminate]. cbn in H.
  destruct (sym_runA segs fuel cutpcs T true) as [leaves|]; [|discriminate].
  destruct (leaves_edgesA g i leaves targets) as [es1|] eqn:He; [|discriminate].
  destruct (cuts_edgesA segs fuel cutpcs g (S i) rest targets) as [es2|] eqn:Hc; [|discriminate].
  rewrite (leaves_edgesA_ok g i leaves targets es1 He). eapply IH. exact Hc.
Qed.

Theorem check_cfgA_of_edges : ltac2:(tb__ "0|2|
S1S0ScA1SbS0S9A1M0G0S0SdA1M1S8S5G1A1S11Vsegs;R6R5R4R3R2A6S4G1R1A2A3S8S2SfVsegs;R7R6R5R4R3A6S3A3F_;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g cuts exits es H. unfold check_cfgA. unfold cfg_edgesA in H. eapply cuts_edgesA_ok. exact H.
Qed.

Theorem check_cfgA_of_ecfgA : ltac2:(tb__ "0|3|
S1S0ScA1SbS0SeA1M0G0S0S9A1M1G1S8G1S1dSeS9S10R4A4R2A3M2G2S8S2S13Vsegs;R9R8R7R6R5A6S3A3S8S2SfVsegs;RaR9R8R5R4A6S3A3F_;F_;F_;Fexits;Fcuts;Fvexits;Fvcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g vcuts vexits cuts exits <- <- H. unfold check_ecfgA in H.
  apply andb_prop in H as [_ H].
  destruct (cfg_edgesA segs fuel cutpcs g (map vna_state vcuts) (map vna_state vexits)) as [es|] eqn:E; [|discriminate].
  eapply check_cfgA_of_edges. exact E.
Qed.

Theorem check_cfgA_of_ecfgIA : ltac2:(tb__ "0|3|
S1S0ScA1SbS0SeA1M0G0S0S9A1M1G1S8G1S1dSeS9S10R4A4R2A3M2G2S8S2S1eVsegs;R9R8R7R6R5A6S3A3S8S2SfVsegs;RaR9R8R5R4A6S3A3F_;F_;F_;Fexits;Fcuts;Fvexits;Fvcuts;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g vcuts vexits cuts exits <- <- H. unfold check_ecfgIA in H.
  apply andb_prop in H as [_ H].
  destruct (cfg_edgesA segs fuel cutpcs g (map vna_state vcuts) (map vna_state vexits)) as [es|] eqn:E; [|discriminate].
  eapply check_cfgA_of_edges. exact E.
Qed.
End Edges.
