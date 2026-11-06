(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan BsStartupPlan BsStartupHS1 BsStartupHSC BothImages BothPlanImages BsStartup.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanPlanF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~05shape05SHole05SCase79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~l34EVar37Corelib4Init9Datatypespb4boolpb4true37Corelib4Init5Logics12eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup~~~~~~taaholes_only69OSSVerify6Proofsaboost_jsonafuzz_parse3libfBsStartupCert90~~~~~~hi3dstartup_shape69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~hn65ASEGSpb4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~hs75LIMIT03COk03NX005check04cres07loopctx0emk_itab_ranges69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~ijb6BOTH_Hta3XB0ta3XE0ta3XN069OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHS1~~~~~~ip4bHS1_asan_9069OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSC~~~~~~iu28HSC_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBsStartupPlan~~~~~~jidaCERT_BFUELjid9CERT_FUELjid8CERT_KC0jidh2startup_plan_seg90jidhastartup_plan_seg90_xranges" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Definition startup_shape : ltac2:(zQ "10!je$0") := ltac2:(zQ "30!k5!kc!p4@4$1@1$2Na+a@1$0Nlb@1$0Nle").

Lemma startup_shape_holes : ltac2:(zQ "50!r3!ra!t5!hh6!hm5@3$2$0@1$3$4$1").
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert : ltac2:(zQ "h60!hr7!hs0!t5!ig2!igb!ih0!ih5!ihc!ii2!iib!in8!io2!io8!ioe!hm5!it3!ji1!jmd!jnb!jo8!jp4!jqb@3$2$7@f$6$0@2$9$0$h5$a$5$3$d$c$b$h0$h3$h1$h2@1$1$8$f$h4@1$4$e").
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape). Qed.   (* [comment removed for export] *)
