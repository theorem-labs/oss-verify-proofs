(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag ar ae ah.
From Stdlib Require NArith PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.

(* [comment removed for export] *)
Module F0A_b2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A"; "Ebg_2A"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_2A : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b2A.

(* [comment removed for export] *)
Module F0A_b2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be"; "Ebg_2Be"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_2Be : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b2Be.

(* [comment removed for export] *)
Module F0A_bL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A"; "Ebg_L1A"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L1A : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL1A.

(* [comment removed for export] *)
Module F0A_bL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be"; "Ebg_L1Be"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L1Be : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL1Be.

(* [comment removed for export] *)
Module F0A_bL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf"; "Ebg_L1Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_L1Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_bL1Bf.

(* [comment removed for export] *)
Module F0A_pins.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "iff"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "true"; "list"; "andb"; "nat"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins"; "spec_on"; "sv_on"; "sprop_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "holds"; "obj_range"; "sobj"; "eval"; "pairwise_disjoint"; "rl"; "rm"; "rw"; "ob_base"; "ob_hi"; "ob_lo"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "carve_ok"; "spec_zone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint sv_on (P : positive -> bool) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => P i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_on P a && sv_on P b
  | SExt _ _ a => sv_on P a
  | SLBytes _ i _ => sv_on P i
  end.
Fixpoint sprop_on (P : positive -> bool) (f : sprop) : bool :=
  match f with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_on P a && sv_on P b
  | SPNot g => sprop_on P g
  | SPTrue => true
  | SPAlign i _ => P i
  end.
Definition spec_on (P : positive -> bool) (k : carve_spec) : bool := ltac2:(tb__ "0|5|
S3S3S3S13S9A2M0S9A2M1S5S3S3S9S7A2M2S13A2M3A1M4A2S2Lk;Vk;G1G4G1S2Lp;R2G0S9G0S2Lp0;R2S13S9S6S10VP;R2A2S1fG3G3G3S2Lc;R1G2S13G2S2Lp;R2S9S7S10VP;R3A2Ln;Lz;X3x1Le;Lp;X3x1Lc;R5A3A2Lz0;Lb;X3x1Lz;Lp0;X3x1Lcs;Lp;X3x1").

Section Agree.
Variable P : positive -> bool.
Variables r1 r2 : valuation.
Hypothesis HW : ltac2:(tb__ "0|0|
SaS0S2VP;R1A1S4A3S0S20Q40A1S1bVr2;R2A2S1bVr1;R2A2A3F_;Fi;").
Hypothesis HL : ltac2:(tb__ "0|0|
SaS0S5S20Q8A1A1S19Vr2;R1A2S19Vr1;R1A2A3Fl;").
Hypothesis HM : ltac2:(tb__ "0|0|
S0S20Q40A1S8S20Q8A1A1F_;S1aVr2;A1S1aVr1;A1A3").

Lemma eval_on : ltac2:(tb__ "0|0|
S13S0S2S10VP;R1A2S4A3S0S20Q40A1S17Vr2;R2A2S17Vr1;R2A2A3F_;Fe;").
Proof.
  induction e; cbn; intros Hb; try (apply andb_prop in Hb as [Hb1 Hb2]); try rewrite (IHe1 Hb1); try rewrite (IHe2 Hb2); try reflexivity.
  - apply HW. exact Hb.
  - rewrite (IHe Hb). reflexivity.
  - rewrite HL, (IHe Hb). reflexivity.
Qed.
Lemma holds_on : ltac2:(tb__ "0|0|
S12S0S2S11VP;R1A2S4A3S1S14Vr1;R2A2S14Vr2;R2A2A2F_;Ff;").
Proof.
  induction f as [c a b|g IH|a b|a b|a b| |i a]; cbn; intros Hb; try (apply andb_prop in Hb as [Hb1 Hb2]); rewrite ?(eval_on _ Hb1), ?(eval_on _ Hb2); try tauto.
  rewrite (HW _ Hb). tauto.
Qed.
Lemma Forall_holds_on : ltac2:(tb__ "0|0|
S5S12A1S0S2S1fS12S11VP;A1R1A3S4A3SdS12S14Vr1;A1R2A3SdS12S14Vr2;A1R3A3F_;F_;Fl;").
Proof.
  intros l Hb H. apply Forall_forall. intros f Hf. apply (proj1 (holds_on f (proj1 (forallb_forall _ _) Hb f Hf))). exact (proj1 (Forall_forall _ _) H f Hf).
Qed.
Lemma carve_ok_on : ltac2:(tb__ "0|0|
SbS0S2SfVP;R1A2S4A3S21Vr1;R2A2S21Vr2;R3A2F_;F_;Fk;").
Proof.
  intros [[[base lo] hi] cs] Hb. unfold spec_on in Hb. apply andb_prop in Hb as [Hb Hc]. unfold carve_ok. cbn zeta.
  rewrite (eval_on base Hb), HM. intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 _))))))).
  unfold cells_in_view in *. apply Forall_forall. intros [[off k] v] Hin. pose proof (proj1 (Forall_forall _ _) C8 _ Hin) as C. cbn beta iota in C |- *.
  pose proof (proj1 (forallb_forall _ _) Hc _ Hin) as Hv. cbn beta iota in Hv. rewrite (eval_on v Hv). exact C.
Qed.
Lemma Forall_carve_ok_on : ltac2:(tb__ "0|0|
S5SbA1S0S2S1fSbSfVP;A1R1A3S4A3SdSbS21Vr1;A1R2A3SdSbS21Vr2;A1R3A3F_;F_;FN;").
Proof.
  intros N Hb H. apply Forall_forall. intros k Hk. apply (carve_ok_on k (proj1 (forallb_forall _ _) Hb k Hk)). exact (proj1 (Forall_forall _ _) H k Hk).
Qed.
Lemma carve_range_on : ltac2:(tb__ "0|1|
SbS0S2SfVP;R1A2S4A3S0S3S9S9A2S15Vr2;ScR2A1M0A2S15Vr1;G0A2A3F_;Fk;").
Proof.
  intros [[[base lo] hi] cs] Hb. unfold spec_on in Hb. apply andb_prop in Hb as [Hb _]. cbn [carve_obj]. unfold carved, obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi eval].
  rewrite (eval_on base Hb). reflexivity.
Qed.
Lemma spec_zone_on : ltac2:(tb__ "0|0|
S9S9S9SbS0S2SfVP;R1A2S4A3S22Vr1;R5R4R3R2A5S22Vr2;R6R5R4R3A5F_;F_;Fk;Fn8;Fp;Ftop;").
Proof.
  intros top p n8 [[[base lo] hi] cs] Hb. unfold spec_on in Hb. apply andb_prop in Hb as [Hb _]. unfold spec_zone. rewrite (eval_on base Hb). exact (fun H => H).
Qed.
Lemma Forall_spec_zone_on : ltac2:(tb__ "0|0|
S9S9S9S5SbA1S0S2S1fSbSfVP;A1R1A3S4A3SdSbS22Vr1;R5R4R3A4R2A3SdSbS22Vr2;R6R5R4A4R3A3F_;F_;FN;Fn8;Fp;Ftop;").
Proof.
  intros top p n8 N Hb H. apply Forall_forall. intros k Hk. apply (spec_zone_on top p n8 k (proj1 (forallb_forall _ _) Hb k Hk)). exact (proj1 (Forall_forall _ _) H k Hk).
Qed.
Lemma pd_on : ltac2:(tb__ "0|0|
S5SbA1S0S2S1fSbSfVP;A1R1A3S4A3S18Vr1;SeSbS16ScR2A4A2S18Vr2;SeSbS16ScR3A4A2F_;F_;FN;").
Proof.
  induction N as [|k N IH]; intros Hb Hpd; [exact I|]. cbn [forallb] in Hb. apply andb_prop in Hb as [Hk Hb]. cbn [map pairwise_disjoint] in Hpd |- *.
  destruct Hpd as [Hd Hpd]. split; [|exact (IH Hb Hpd)].
  apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k' & <- & Hk').
  rewrite (carve_range_on k Hk), (carve_range_on k' (proj1 (forallb_forall _ _) Hb k' Hk')).
  exact (proj1 (Forall_forall _ _) Hd (carve_obj k') (in_map _ _ _ Hk')).
Qed.
Lemma obj_range_on : ltac2:(tb__ "0|0|
S16S0S2S6S6S10VP;S1cR1A1A2S10VP;S1eR1A1A2A2S10VP;S1dR1A1A2A2S4A3S0S3S9S9A2S15Vr2;R2A2S15Vr1;R2A2A3F_;Fo;").
Proof.
  intros o Hb. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite (eval_on _ H1), (eval_on _ H2), (eval_on _ H3). reflexivity.
Qed.
End Agree.
End F0A_pins.

