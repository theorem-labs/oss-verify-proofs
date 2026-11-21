(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, lemmas added for the revision. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab BothImages BothPlanImages BsStartup BsStartupPlan
  BsStartupHS1 BsStartupHSC BsStartupHSA BsStartupHSF BsStartupCert1 BsStartupCert100 BsStartupCert101 BsStartupCert102 BsStartupCert103 BsStartupCert104 BsStartupCert105 BsStartupCert90 BsStartupCert91 BsStartupCert94.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: the levels of the start-up chain, one per CONFIG_RSEQ value [b]
   (the root to segment 90, segment 90 to segments 91/94, segments 91/94 to segments 100..105),
   and the last level, segments 100..105 of either value to the one main-entry table. *)
Lemma cert2_k : forall b, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HS1_asan_k b) (HSC_asan_k b).
Proof.
  intros b h ch Hh. destruct b.
  - cbn [HS1_asan_k] in Hh. apply hs_lookup_cases in Hh. cbn [HS1_asan_table_r1 fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg90_xranges, startup_plan_seg90_k, BsStartupCert90.startup_shape_r1; split; [exact BsStartupCert90.startup_cert_r1 | exact BsStartupCert90.startup_shape_holes_r1]|].
    destruct Hh.
  - cbn [HS1_asan_k] in Hh. apply hs_lookup_cases in Hh. cbn [HS1_asan_table_r0 fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg90_xranges, startup_plan_seg90_k, BsStartupCert90.startup_shape_r0; split; [exact BsStartupCert90.startup_cert_r0 | exact BsStartupCert90.startup_shape_holes_r0]|].
    destruct Hh.
Qed.

Lemma cert3_k : forall b, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSC_asan_k b) (HSA_asan_k b).
Proof.
  intros b h ch Hh. destruct b.
  - cbn [HSC_asan_k] in Hh. apply hs_lookup_cases in Hh. cbn [HSC_asan_table_r1 fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg91_xranges, startup_plan_seg91_k, BsStartupCert91.startup_shape_r1; split; [exact BsStartupCert91.startup_cert_r1 | exact BsStartupCert91.startup_shape_holes_r1]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg94_xranges, startup_plan_seg94_k, BsStartupCert94.startup_shape_r1; split; [exact BsStartupCert94.startup_cert_r1 | exact BsStartupCert94.startup_shape_holes_r1]|].
    destruct Hh.
  - cbn [HSC_asan_k] in Hh. apply hs_lookup_cases in Hh. cbn [HSC_asan_table_r0 fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg91_xranges, startup_plan_seg91_k, BsStartupCert91.startup_shape_r0; split; [exact BsStartupCert91.startup_cert_r0 | exact BsStartupCert91.startup_shape_holes_r0]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg94_xranges, startup_plan_seg94_k, BsStartupCert94.startup_shape_r0; split; [exact BsStartupCert94.startup_cert_r0 | exact BsStartupCert94.startup_shape_holes_r0]|].
    destruct Hh.
Qed.

Lemma cert4_k : forall b, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSA_asan_k b) HSF_asan.
Proof.
  intros b h ch Hh. destruct b.
  - cbn [HSA_asan_k] in Hh. apply hs_lookup_cases in Hh. cbn [HSA_asan_table_r1 fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg100_xranges, startup_plan_seg100_k, BsStartupCert100.startup_shape_r1; split; [exact BsStartupCert100.startup_cert_r1 | exact BsStartupCert100.startup_shape_holes_r1]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg101_xranges, startup_plan_seg101_k, BsStartupCert101.startup_shape_r1; split; [exact BsStartupCert101.startup_cert_r1 | exact BsStartupCert101.startup_shape_holes_r1]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg102_xranges, startup_plan_seg102_k, BsStartupCert102.startup_shape_r1; split; [exact BsStartupCert102.startup_cert_r1 | exact BsStartupCert102.startup_shape_holes_r1]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg103_xranges, startup_plan_seg103_k, BsStartupCert103.startup_shape_r1; split; [exact BsStartupCert103.startup_cert_r1 | exact BsStartupCert103.startup_shape_holes_r1]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg104_xranges, startup_plan_seg104_k, BsStartupCert104.startup_shape_r1; split; [exact BsStartupCert104.startup_cert_r1 | exact BsStartupCert104.startup_shape_holes_r1]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg105_xranges, startup_plan_seg105_k, BsStartupCert105.startup_shape_r1; split; [exact BsStartupCert105.startup_cert_r1 | exact BsStartupCert105.startup_shape_holes_r1]|].
    destruct Hh.
  - cbn [HSA_asan_k] in Hh. apply hs_lookup_cases in Hh. cbn [HSA_asan_table_r0 fold_right fst snd] in Hh.
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg100_xranges, startup_plan_seg100_k, BsStartupCert100.startup_shape_r0; split; [exact BsStartupCert100.startup_cert_r0 | exact BsStartupCert100.startup_shape_holes_r0]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg101_xranges, startup_plan_seg101_k, BsStartupCert101.startup_shape_r0; split; [exact BsStartupCert101.startup_cert_r0 | exact BsStartupCert101.startup_shape_holes_r0]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg102_xranges, startup_plan_seg102_k, BsStartupCert102.startup_shape_r0; split; [exact BsStartupCert102.startup_cert_r0 | exact BsStartupCert102.startup_shape_holes_r0]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg103_xranges, startup_plan_seg103_k, BsStartupCert103.startup_shape_r0; split; [exact BsStartupCert103.startup_cert_r0 | exact BsStartupCert103.startup_shape_holes_r0]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg104_xranges, startup_plan_seg104_k, BsStartupCert104.startup_shape_r0; split; [exact BsStartupCert104.startup_cert_r0 | exact BsStartupCert104.startup_shape_holes_r0]|].
    destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg105_xranges, startup_plan_seg105_k, BsStartupCert105.startup_shape_r0; split; [exact BsStartupCert105.startup_cert_r0 | exact BsStartupCert105.startup_shape_holes_r0]|].
    destruct Hh.
Qed.

Lemma HSF_asan_pc : forall (h : nat) (ch : acs), HSF_asan h = Some ch -> pc ch = 780476.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh.
Qed.
