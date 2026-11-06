(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg CatSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAcct SpinAlg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsi2dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runm95mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statepd5Model69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~t34MInv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~hh59srealizes35stdpp9bitvectorbdefinitionshlc2bv37Corelib4Init9Datatypeshnf4Nonehnf4listhnf6optionhnf4prod37Corelib4Init5Logichr92eqi26ms_mempd8m_haltedpd9m_vm_lazyt34A_wft36hcleant3alazy_covert38restrictt3h5same_but_materializedt3aunrestrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ik16msteps69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~io44TSet3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeis77Segmenthnf4boolt3eH_off_segmentst3ewx_segs_nowrap" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : ltac2:(zQ "20!hpf!ivc@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)
Variable H : ltac2:(zQ "30!jg7!h9!hn9>0@1$2@1$1#k0$0").
Hypothesis HH : ltac2:(zQ "10!jgf@2$0?4segs?1H").
Hypothesis Hwx : ltac2:(zQ "10!ji0@1$0?4segs").

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.

(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.

Theorem srz_msteps_restricted_T : ltac2:(zQ "h80!h9!hf!l9!p5!sb!hge!hkf!hn9!hp7!hpf!hq7!hr1!hsd!ht3!htc!hu7!hv3!hva!ig3!ih0!ihb!ij4!ina!irf>1A@1$9@2$b$1$1>2ms$2>4msr'$2>5model$4>1T$h7>0@3$h2?1H@1$f^2^5>0@1$h0^6>0@2$5^7^4>0@3$c@1$a@1$7@1$0#k0@1$e^5@1$8@1$7@1$0#k0>0@3$h6?4segs@2$h3?1H^8^7>0>6model'$4>0@2$5^b^1>0@2$h4^9^2>0@2$h1?1H^b@4$6?4segs?2SC@2$3@3$h5?1H@1$d^d^c^4^a@4$6?4segs?2SC@2$3^a^8^7").
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
(* [comment removed for export] *)
