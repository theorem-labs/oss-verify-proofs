(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab BothImages BothPlanImages BsStartup BsStartupPlan
  BsStartupHS1 BsStartupHSC BsStartupHSA BsStartupHSF BsStartupCert1 BsStartupCert100 BsStartupCert101 BsStartupCert102 BsStartupCert103 BsStartupCert104 BsStartupCert105 BsStartupCert90 BsStartupCert91 BsStartupCert94.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup~~~~~~0flevel_certified69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHS1~~~~~~kd8HS1_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSC~~~~~~p78HSC_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBsStartupPlan~~~~~~u1aCERT_BFUELu19CERT_FUELu18CERT_KC069OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSA~~~~~~hk58HSA_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSF~~~~~~hp08HSF_asan79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~htb3acs37Corelib4Init5Logicii02eq37Corelib4Init9Datatypesija4Someija3natija6option37Corelib7Numbers7BinNumsimb1Zhtb2pc" s.   (* [comment removed for export] *)

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Lemma cert2 : ltac2:(zQ "60!jc!oc!t6!hi1!hie!hja@5$0$5$3$4$1$2").
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg90_xranges, startup_plan_seg90, BsStartupCert90.startup_shape; split; [exact BsStartupCert90.startup_cert | exact BsStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3 : ltac2:(zQ "60!jc!ho4!t6!hi1!hie!hja@5$0$5$3$4$2$1").
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg91_xranges, startup_plan_seg91, BsStartupCert91.startup_shape; split; [exact BsStartupCert91.startup_cert | exact BsStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg94_xranges, startup_plan_seg94, BsStartupCert94.startup_shape; split; [exact BsStartupCert94.startup_cert | exact BsStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4 : ltac2:(zQ "60!jc!ho4!hsf!hi1!hie!hja@5$0$5$3$4$1$2").
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg100_xranges, startup_plan_seg100, BsStartupCert100.startup_shape; split; [exact BsStartupCert100.startup_cert | exact BsStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg101_xranges, startup_plan_seg101, BsStartupCert101.startup_shape; split; [exact BsStartupCert101.startup_cert | exact BsStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg102_xranges, startup_plan_seg102, BsStartupCert102.startup_shape; split; [exact BsStartupCert102.startup_cert | exact BsStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg103_xranges, startup_plan_seg103, BsStartupCert103.startup_shape; split; [exact BsStartupCert103.startup_cert | exact BsStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg104_xranges, startup_plan_seg104, BsStartupCert104.startup_shape; split; [exact BsStartupCert104.startup_cert | exact BsStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [nexists startup_plan_seg105_xranges, startup_plan_seg105, BsStartupCert105.startup_shape; split; [exact BsStartupCert105.startup_cert | exact BsStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.

(* [comment removed for export] *)
Lemma HSF_asan_pc : ltac2:(zQ "80!ih9!ij4!il2!ila!im1!io4!io9!hsf>1h$3>2ch$0>0@3$1@1$4$0@1$7^2@2$2$0^1@3$1$5@1$6^2+ruorc").
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
