(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsStartupPlan AsStartupHSA AsStartupHSF AsImages AsPlanImages AsStartup.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanPlanF.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsStartupItab.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~05shape05SHole37Corelib4Init9Datatypeskc4boolkc4true37Corelib4Init5Logicn22eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsStartup~~~~~~obaholes_only69OSSVerify6Proofsaboost_jsonafuzz_parse3libh0AsStartupCert100~~~~~~t4dstartup_shape69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~hi85ASEGSkc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~hn76ASAN_Hob3XB0ob3XE0ob3XN069OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSA~~~~~~hsecHSA_asan_10069OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~ihd8HSF_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsStartupPlan~~~~~~im8aCERT_BFUELim89CERT_FUELim88CERT_KC0im8h3startup_plan_seg100im8hbstartup_plan_seg100_xranges69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~jg75LIMIT03COk03NX005check04cres07loopctx0emk_itab_ranges" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Definition startup_shape : ltac2:(zQ "10!je$0") := ltac2:(zQ "10!k5@1$0N0").

Lemma startup_shape_holes : ltac2:(zQ "50!m4!mb!o6!s7!hh8@3$2$0@1$3$4$1").
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert : ltac2:(zQ "h60!hm7!hn0!o6!hr2!hrc!hs2!hs8!hh8!igd!ilc!iq8!ir6!is3!isf!iu7!jk2!jkb!jl0!jl5!jlc!jm2!jmb@3$2$h3@f$h2$0@2$h5$0$e$3$h1$f$6$5$4$9$c$a$b@1$1$h4$8$d@1$h0$7").
Proof. ltac1:(rewrite <- ARM_ITAB_eq). apply FC.check_of_f. cert_refl constr:(COk startup_shape). Qed.   (* [comment removed for export] *)
