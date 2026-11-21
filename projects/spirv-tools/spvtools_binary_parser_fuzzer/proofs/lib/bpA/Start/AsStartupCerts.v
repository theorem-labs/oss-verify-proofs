(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off certificates proved in the build at both CONFIG_RSEQ values against the computed hand-off tables. *)
(* LPS 727298f3: the level certificates of the start-up, over the computed hand-off tables
   ([AsStartupHS1] .. [AsStartupHSF]), one table per CONFIG_RSEQ value up to hand-offs 100 .. 105 and one
   met table at the main entry: each table entry's plan is certified at both values by its [AsStartupCertG*]
   module; the recorded proofs this file held were for the earlier tables. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab AsImages AsPlanImages AsStartup AsStartupPlan AsStartupRanges
  AsStartupHS1 AsStartupHSC AsStartupHSA AsStartupHSF AsPlanRegen AsStartupRegen.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export AsStartupCertG1 AsStartupCertG2 AsStartupCertG3 AsStartupCertG4 AsStartupCertG5 AsStartupCertG6 AsStartupCertG7 AsStartupCertG8 AsStartupCertG9 AsStartupCertG10.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(** split a lookup in a concrete table into its entries *)
Ltac hs_cases H :=
  repeat (lazymatch type of H with
          | (if Nat.eqb ?h ?k then Some _ else _) = Some _ =>
              let E := fresh "E" in
              destruct (Nat.eqb h k) eqn:E; [apply Nat.eqb_eq in E; subst h; injection H as <- |]
          | None = Some _ => discriminate H
          end).

Ltac cert_entry rs p S C Hh :=
  exists rs, (psh FSH p), S; split; [exact C | exact Hh].

Lemma cert2_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_asan_0 HSC_asan_0.
Proof.
  intros h ch H. unfold HS1_asan_0, HS1_asan_table_0 in H. cbn [hs_lookup] in H. hs_cases H.
  cert_entry startup_plan_seg90_xranges startup_plan_seg90 AsStartupCert90.startup_shape AsStartupCert90.startup_cert_0 AsStartupCert90.startup_shape_holes.
Qed.
Lemma cert2_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_asan_1 HSC_asan_1.
Proof.
  intros h ch H. unfold HS1_asan_1, HS1_asan_table_1 in H. cbn [hs_lookup] in H. hs_cases H.
  cert_entry startup_plan_seg90_xranges startup_plan_seg90 AsStartupCert90.startup_shape AsStartupCert90.startup_cert_1 AsStartupCert90.startup_shape_holes.
Qed.
Lemma cert2 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HS1_asan_r r) (HSC_asan_r r).
Proof. intros r. unfold HS1_asan_r, HSC_asan_r. destruct (Z.eqb r 1); [exact cert2_1 | exact cert2_0]. Qed.

Lemma cert3_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_asan_0 HSA_asan_0.
Proof.
  intros h ch H. unfold HSC_asan_0, HSC_asan_table_0 in H. cbn [hs_lookup] in H. hs_cases H.
  - cert_entry startup_plan_seg91_xranges startup_plan_seg91 AsStartupCert91.startup_shape AsStartupCert91.startup_cert_0 AsStartupCert91.startup_shape_holes.
  - cert_entry startup_plan_seg94_xranges startup_plan_seg94 AsStartupCert94.startup_shape AsStartupCert94.startup_cert_0 AsStartupCert94.startup_shape_holes.
Qed.
Lemma cert3_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_asan_1 HSA_asan_1.
Proof.
  intros h ch H. unfold HSC_asan_1, HSC_asan_table_1 in H. cbn [hs_lookup] in H. hs_cases H.
  - cert_entry startup_plan_seg91_xranges startup_plan_seg91 AsStartupCert91.startup_shape AsStartupCert91.startup_cert_1 AsStartupCert91.startup_shape_holes.
  - cert_entry startup_plan_seg94_xranges startup_plan_seg94 AsStartupCert94.startup_shape AsStartupCert94.startup_cert_1 AsStartupCert94.startup_shape_holes.
Qed.
Lemma cert3 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSC_asan_r r) (HSA_asan_r r).
Proof. intros r. unfold HSC_asan_r, HSA_asan_r. destruct (Z.eqb r 1); [exact cert3_1 | exact cert3_0]. Qed.

Lemma cert4_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_asan_0 HSF_asan.
Proof.
  intros h ch H. unfold HSA_asan_0, HSA_asan_table_0 in H. cbn [hs_lookup] in H. hs_cases H.
  - cert_entry startup_plan_seg100_xranges startup_plan_seg100 AsStartupCert100.startup_shape AsStartupCert100.startup_cert_0 AsStartupCert100.startup_shape_holes.
  - cert_entry startup_plan_seg101_xranges startup_plan_seg101 AsStartupCert101.startup_shape AsStartupCert101.startup_cert_0 AsStartupCert101.startup_shape_holes.
  - cert_entry startup_plan_seg102_xranges startup_plan_seg102 AsStartupCert102.startup_shape AsStartupCert102.startup_cert_0 AsStartupCert102.startup_shape_holes.
  - cert_entry startup_plan_seg103_xranges startup_plan_seg103 AsStartupCert103.startup_shape AsStartupCert103.startup_cert_0 AsStartupCert103.startup_shape_holes.
  - cert_entry startup_plan_seg104_xranges startup_plan_seg104 AsStartupCert104.startup_shape AsStartupCert104.startup_cert_0 AsStartupCert104.startup_shape_holes.
  - cert_entry startup_plan_seg105_xranges startup_plan_seg105 AsStartupCert105.startup_shape AsStartupCert105.startup_cert_0 AsStartupCert105.startup_shape_holes.
Qed.
Lemma cert4_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_asan_1 HSF_asan.
Proof.
  intros h ch H. unfold HSA_asan_1, HSA_asan_table_1 in H. cbn [hs_lookup] in H. hs_cases H.
  - cert_entry startup_plan_seg100_xranges startup_plan_seg100 AsStartupCert100.startup_shape AsStartupCert100.startup_cert_1 AsStartupCert100.startup_shape_holes.
  - cert_entry startup_plan_seg101_xranges startup_plan_seg101 AsStartupCert101.startup_shape AsStartupCert101.startup_cert_1 AsStartupCert101.startup_shape_holes.
  - cert_entry startup_plan_seg102_xranges startup_plan_seg102 AsStartupCert102.startup_shape AsStartupCert102.startup_cert_1 AsStartupCert102.startup_shape_holes.
  - cert_entry startup_plan_seg103_xranges startup_plan_seg103 AsStartupCert103.startup_shape AsStartupCert103.startup_cert_1 AsStartupCert103.startup_shape_holes.
  - cert_entry startup_plan_seg104_xranges startup_plan_seg104 AsStartupCert104.startup_shape AsStartupCert104.startup_cert_1 AsStartupCert104.startup_shape_holes.
  - cert_entry startup_plan_seg105_xranges startup_plan_seg105 AsStartupCert105.startup_shape AsStartupCert105.startup_cert_1 AsStartupCert105.startup_shape_holes.
Qed.
Lemma cert4 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSA_asan_r r) HSF_asan.
Proof. intros r. unfold HSA_asan_r. destruct (Z.eqb r 1); [exact cert4_1 | exact cert4_0]. Qed.

Lemma HSF_asan_pc : forall h ch, HSF_asan h = Some ch -> pc ch = 952236.
Proof.
  intros h ch H. unfold HSF_asan, HSF_asan_table in H. cbn [hs_lookup] in H. hs_cases H; vm_compute; reflexivity.
Qed.
