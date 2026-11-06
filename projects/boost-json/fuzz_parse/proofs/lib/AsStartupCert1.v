(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsStartupPlan AsStartupHS1 AsImages AsPlanImages AsStartup.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanPlanF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~05shape05SHole37Corelib4Init9Datatypeskc4boolkc4true37Corelib4Init5Logicn22eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsStartup~~~~~~obaholes_only69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsStartupCert1~~~~~~t4dstartup_shape69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~hi55ASEGSkc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~hn46ASAN_Hhn45hinitob3XB0ob3XE0ob3XN069OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHS1~~~~~~ht48HS1_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsStartupPlan~~~~~~ihfaCERT_BFUELihf9CERT_FUELihf8CERT_KC0ihfcstartup_planihfh4startup_plan_xranges69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~iqf5LIMIT03COk03NX005check04cres07loopctx0emk_itab_ranges" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Definition startup_shape : ltac2:(zQ "10!je$0") := ltac2:(zQ "10!k5@1$0Nla").

Lemma startup_shape_holes : ltac2:(zQ "50!m4!mb!o6!s7!hh5@3$2$0@1$3$4$1").
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert : ltac2:(zQ "h60!hm4!hmd!o6!hqf!hr9!hs2!hs8!hse!hh5!ih3!ilf!imd!ina!io6!ip6!iua!iv3!iv8!ivd!jg4!jga!jh3@3$2$h3@f$h2$0@2$h5$0$e$3$h1$f$7$6$5$9$c$a$b@1$1$h4$4$d@1$h0$8").
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape). Qed.   (* [comment removed for export] *)
