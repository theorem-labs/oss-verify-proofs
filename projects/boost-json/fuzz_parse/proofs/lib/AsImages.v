(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~06atable37Corelib7Numbers7BinNumsk61Z37Corelib4Init9Datatypesm34consm33nil02AT03acs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~p16ASAN_H0binit_acs_of" s.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Definition ASAN_H : ltac2:(zQ "10!je$0") := ltac2:(zQ "40!lf!nb!o2!o8@hb$3+hggg0+nhmgg0N4+nvvvogg0+mnujc+hqtgg0+lmpgg0+hggk0+j8+b+qiin8+qihvc+hqlqi8+hqlmi4+qins4+qimq4+hhtp6+mukv8+qjotcZZZ+hpjqk0+hpjqkc+hpjrg4+hpjrh0@3$1$0+mshmc@3$1$0+mtnp0@3$1$0+piji0@3$1$0+popjc@3$1$0+popl0@3$1$0+popm4@3$1$0+puiv4@3$1$0+pujs4@3$1$0+qrpgc@3$1$0+qsohc@3$1$0+qspqc@3$1$0+qsrhc@3$1$0+rmng4@1$2$0").

Definition hinit : ltac2:(zQ "10!oc$0") := ltac2:(zQ "20!sc!t5@1$1$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
