(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan BsStartupPlan BsStartupHSA BsStartupHSC BothImages BothPlanImages BsStartup.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanPlanF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~05shape05SHole37Corelib4Init9Datatypeskc4boolkc4true37Corelib4Init5Logicn22eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup~~~~~~obaholes_only69OSSVerify6Proofsaboost_jsonafuzz_parse3libfBsStartupCert91~~~~~~t4dstartup_shape69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~hi65ASEGSkc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~hn75LIMIT03COk03NX005check04cres07loopctx0emk_itab_ranges69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~hub6BOTH_Hob3XB0ob3XE0ob3XN069OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSA~~~~~~ik48HSA_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSC~~~~~~iofbHSC_asan_9169OSSVerify6Proofsaboost_jsonafuzz_parse3libdBsStartupPlan~~~~~~itdaCERT_BFUELitd9CERT_FUELitd8CERT_KC0itdh2startup_plan_seg91itdhastartup_plan_seg91_xranges" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Definition startup_shape : ltac2:(zQ "10!je$0") := ltac2:(zQ "10!k5@1$0Nm6").

Lemma startup_shape_holes : ltac2:(zQ "50!m4!mb!o6!s7!hh6@3$2$0@1$3$4$1").
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert : ltac2:(zQ "h60!hm7!hn0!o6!hr2!hrb!hs0!hs5!hsc!ht2!htb!ii8!ij2!ij8!ije!hh6!io3!ise!jhd!jib!jj8!jk4!jlb@3$2$7@f$6$0@2$9$0$h5$a$5$3$d$c$b$f$h3$h1$h2@1$1$8$h0$h4@1$4$e").
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape). Qed.   (* [comment removed for export] *)
